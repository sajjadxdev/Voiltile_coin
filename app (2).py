import logging
import json
import threading
import queue
from flask import Flask, jsonify, render_template, Response, request
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
import requests
import time
import numpy as np
from websocket import create_connection, WebSocketException
import random
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
import bisect
import atexit
import signal
import sys
from typing import Dict, List, Optional, Tuple, Any
import multiprocessing

app = Flask(__name__)
CORS(app, origins=['http://localhost:9100', 'http://127.0.0.1:9100'])

# Rate limiting with per-endpoint configuration
limiter = Limiter(
    app=app,
    key_func=get_remote_address,
    default_limits=["10000 per day", "1000 per hour"],  # Increased limits
    storage_uri="memory://"
)

logging.basicConfig(level=logging.INFO, format='%(asctime)s [%(levelname)s] %(message)s')
logger = logging.getLogger(__name__)

# Constants with explanations
PRICE_HISTORY_SIZE = 100  # Store last 100 candle prices for change calculations
TICK_HISTORY_SIZE = 3600  # Store 1 hour of tick data (1 per second) for accurate price change calculations
MAX_WORKERS = min(8, multiprocessing.cpu_count())  # Scale with CPU cores, max 8 to respect rate limits
MAX_WS_RECONNECT_ATTEMPTS = 999999  # Unlimited reconnection attempts
WS_HEARTBEAT_INTERVAL = 180  # Increased to 180s - WebSocket heartbeat check interval in seconds
QUEUE_MAX_SIZE = 5000  # Increased maximum update queue size
QUEUE_PUT_TIMEOUT = 0.1  # Timeout for queue put operations
SYMBOL_CLEANUP_INTERVAL = 3600  # Clean up inactive symbols every hour
SYMBOL_INACTIVE_THRESHOLD = 7200  # Consider symbol inactive after 2 hours without updates
BOOTSTRAP_MAX_RETRIES = 3  # Maximum bootstrap retry attempts
BOOTSTRAP_RETRY_DELAY = 5  # Delay between bootstrap retries in seconds
THREAD_MONITOR_INTERVAL = 60  # Monitor threads every 60 seconds

# Updated annualization factors for 24/7 crypto markets
# Using industry-standard formula: sqrt(periods_per_year)
# For crypto: 252 trading days * 24 hours = 6048 hourly periods per year
TIMEFRAMES = {
    '3m': {'interval': '3m', 'seconds': 180, 'minutes': 3, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
    '5m': {'interval': '5m', 'seconds': 300, 'minutes': 5, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
    '15m': {'interval': '15m', 'seconds': 900, 'minutes': 15, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
    '30m': {'interval': '30m', 'seconds': 1800, 'minutes': 30, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
    '1h': {'interval': '1h', 'seconds': 3600, 'minutes': 60, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
    '2h': {'interval': '2h', 'seconds': 7200, 'minutes': 120, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
    '4h': {'interval': '4h', 'seconds': 14400, 'minutes': 240, 'atr': 14, 'bb': 20, 'hv': 20, 'rsi': 14},
}

# Calculate annualization factors using industry-standard approach
# sqrt(252 * 24 * 60 / timeframe_minutes) for crypto 24/7 markets
for tf_key, tf_config in TIMEFRAMES.items():
    periods_per_year = (252 * 24 * 60) / tf_config['minutes']
    tf_config['annualization_factor'] = np.sqrt(periods_per_year)

# Global variables
ws_tickers: Dict[str, Dict[str, float]] = {}
ws_tickers_lock = threading.Lock()
all_symbols: List[str] = []
STATE: Dict[str, Dict[str, Dict[str, Any]]] = {}
STATE_LOCKS: Dict[str, threading.Lock] = {}
STATE_CREATION_LOCK = threading.Lock()  # Thread-safe lock creation
update_queue = queue.Queue(maxsize=QUEUE_MAX_SIZE)
bootstrap_progress = {'current': 0, 'total': 0, 'status': 'Not started', 'current_timeframe': ''}
bootstrap_progress_lock = threading.Lock()
bootstrap_event = threading.Event()
refresh_cycles: Dict[str, Dict[str, Any]] = {}
shutdown_event = threading.Event()  # Graceful shutdown signal
timeframe_refresh_timers: Dict[str, float] = {}  # Track next refresh time for each timeframe
timeframe_last_refresh: Dict[str, float] = {}  # Track last successful refresh time
ws_connections: List[Any] = []  # Track WebSocket connections for cleanup
ws_connections_lock = threading.Lock()
dropped_updates_count = 0  # Monitor dropped updates
dropped_updates_lock = threading.Lock()
active_threads: Dict[str, threading.Thread] = {}  # Track active threads for monitoring
active_threads_lock = threading.Lock()

BINANCE_HOSTS = ['api.binance.com', 'api1.binance.com', 'api2.binance.com']

def safe_float(value: Any, default: float = 0.0) -> float:
    """Convert value to float with fallback default"""
    try:
        return float(value)
    except (ValueError, TypeError):
        return default

def ensure_state_lock(symbol: str) -> threading.Lock:
    """Thread-safe lock creation with double-check locking pattern"""
    # Fast path - lock already exists
    if symbol in STATE_LOCKS:
        return STATE_LOCKS[symbol]

    # Slow path - need to create lock
    with STATE_CREATION_LOCK:
        # Double-check after acquiring lock
        if symbol not in STATE_LOCKS:
            STATE_LOCKS[symbol] = threading.Lock()
        return STATE_LOCKS[symbol]

def fetch_all_usdt_symbols() -> List[str]:
    """Fetch all USDT trading pairs from Binance"""
    try:
        url = f"https://{random.choice(BINANCE_HOSTS)}/api/v3/exchangeInfo"
        response = requests.get(url, timeout=10)
        response.raise_for_status()
        data = response.json()
        symbols = [s['symbol'][:-4] for s in data['symbols'] if s['symbol'].endswith('USDT') and s['status'] == 'TRADING']
        logger.info(f"Fetched {len(symbols)} USDT trading pairs")
        return symbols
    except Exception as e:
        logger.error(f"Error fetching symbols: {e}")
        return []

def fetch_klines(symbol: str, timeframe: str, limit: int = 100) -> Optional[Dict[str, List]]:
    """Fetch kline data from Binance with validation and retry logic"""
    # Validate inputs
    if not symbol or timeframe not in TIMEFRAMES:
        logger.error(f"Invalid parameters: symbol={symbol}, timeframe={timeframe}")
        return None

    if not (1 <= limit <= 1000):
        logger.error(f"Invalid limit: {limit}")
        return None

    full_symbol = symbol + 'USDT'
    interval = TIMEFRAMES[timeframe]['interval']
    max_retries = 3
    retry_delay = 1

    for attempt in range(max_retries):
        if shutdown_event.is_set():
            return None

        try:
            url = f"https://{random.choice(BINANCE_HOSTS)}/api/v3/klines?symbol={full_symbol}&interval={interval}&limit={limit}"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            klines = response.json()

            if not isinstance(klines, list) or len(klines) < 2:
                logger.warning(f"Invalid klines data for {symbol} {timeframe}")
                return None

            data = {
                'closes': [float(k[4]) for k in klines],
                'highs': [float(k[2]) for k in klines],
                'lows': [float(k[3]) for k in klines],
                'volumes': [float(k[5]) for k in klines],
                'timestamps': [int(k[0]) for k in klines],
            }
            return data

        except requests.exceptions.RequestException as e:
            if attempt < max_retries - 1:
                logger.warning(f"Retrying fetch for {symbol} {timeframe} after error: {e}")
                time.sleep(retry_delay * (attempt + 1))
                continue
            logger.error(f"Failed to fetch klines for {symbol} {timeframe} after {max_retries} attempts: {e}")
        except Exception as e:
            logger.error(f"Unexpected error fetching klines for {symbol} {timeframe}: {e}")

        return None

def calculate_rsi(closes_list: List[float], period: int = 14) -> float:
    """Calculate Relative Strength Index"""
    if len(closes_list) < period + 1:
        return 50.0  # Neutral RSI

    closes = np.array(closes_list[-(period + 1):])
    deltas = np.diff(closes)

    gains = np.where(deltas > 0, deltas, 0)
    losses = np.where(deltas < 0, -deltas, 0)

    avg_gain = np.mean(gains[:period])
    avg_loss = np.mean(losses[:period])

    if avg_loss == 0:
        return 100.0

    rs = avg_gain / avg_loss
    rsi = 100 - (100 / (1 + rs))

    return rsi

def calculate_historical_volatility(closes_list: List[float], period: int, annualization_factor: float) -> float:
    """Calculate Historical Volatility with industry-standard annualization for 24/7 markets"""
    if len(closes_list) < period + 1:
        return 0.0

    closes_array = np.array(closes_list[-(period + 1):])
    returns = np.diff(np.log(closes_array))

    if len(returns) == 0:
        return 0.0

    vol_std = np.std(returns, ddof=1)
    annualized_vol = vol_std * annualization_factor

    return annualized_vol * 100

def calculate_volatility_score(atr_pct: float, bb_width: float, vol_surge: float, hv: float,
                               current_price: float, bb_upper: float, bb_lower: float) -> float:
    """Enhanced volatility scoring without RSI component (pure volatility focus)"""
    # Normalize individual components
    atr_normalized = min(atr_pct / 10 * 100, 100)
    bb_normalized = min(bb_width / 15 * 100, 100)
    vol_normalized = min((vol_surge - 1) / 4 * 100, 100) if vol_surge >= 1 else 0
    hv_normalized = min(hv / 50 * 100, 100)

    # Bonus for price outside Bollinger Bands (indicates high volatility)
    if current_price > bb_upper or current_price < bb_lower:
        bb_normalized = min(bb_normalized + 20, 100)

    # Weighted calculation focused on volatility metrics only
    total = (atr_normalized * 0.30 +
             bb_normalized * 0.30 +
             vol_normalized * 0.20 +
             hv_normalized * 0.20)

    return min(total, 100)

def update_indicators_incremental(state: Dict[str, Any], close: float, high: float,
                                  low: float, volume: float, cfg: Dict[str, Any]) -> bool:
    """Incrementally update indicators when a new candle closes"""
    try:
        prev_close = state['closes'][-1] if len(state['closes']) > 0 else close

        # Update price and volume history
        state['closes'].append(close)
        state['volumes'].append(volume)

        # Update ATR
        tr = max(high - low, abs(high - prev_close), abs(low - prev_close))
        state['atr'] = (state['atr'] * (cfg['atr'] - 1) + tr) / cfg['atr']
        state['atr_history'].append(state['atr'])

        # Recalculate ATR percentage
        state['atr_percent'] = (state['atr'] / close * 100) if close > 0 else 0.0

        # Recalculate Bollinger Bands
        if len(state['closes']) >= cfg['bb']:
            bb_closes = list(state['closes'])[-cfg['bb']:]
            bb_sma = np.mean(bb_closes)
            bb_std = np.std(bb_closes, ddof=1)
            state['bb_upper'] = bb_sma + (2 * bb_std)
            state['bb_lower'] = bb_sma - (2 * bb_std)
            state['bb_sma'] = bb_sma
            state['bb_width'] = ((state['bb_upper'] - state['bb_lower']) / max(bb_sma, 1e-8) * 100)

        # Recalculate Volume Surge
        if len(state['volumes']) >= 2:
            vol_period = min(50, len(state['volumes']))
            avg_vol = np.mean(list(state['volumes'])[-vol_period:])
            state['volume_surge'] = (state['volumes'][-1] / avg_vol) if avg_vol > 0 else 1.0

        # Recalculate Historical Volatility
        state['historical_volatility'] = calculate_historical_volatility(
            list(state['closes']), cfg['hv'], cfg['annualization_factor']
        )

        # Calculate RSI
        state['rsi'] = calculate_rsi(list(state['closes']), cfg['rsi'])

        # Recalculate Gainer Score
        state['gainer_score'] = calculate_volatility_score(
            state['atr_percent'],
            state['bb_width'],
            state['volume_surge'],
            state['historical_volatility'],
            close,
            state['bb_upper'],
            state['bb_lower']
        )

        return True
    except Exception as e:
        logger.error(f"Error updating indicators incrementally: {e}")
        return False

def initialize_state(symbol: str, timeframe: str, data: Dict[str, List]) -> bool:
    """Initialize state for a symbol-timeframe pair with thread-safe state creation"""
    try:
        closes_list = data.get('closes', [])
        highs = data.get('highs', [])
        lows = data.get('lows', [])
        volumes = data.get('volumes', [])
        timestamps = data.get('timestamps', [])

        if len(closes_list) < 2:
            return False

        cfg = TIMEFRAMES[timeframe]
        closes = deque(maxlen=max(cfg['bb'], cfg['hv'], cfg['rsi']) + 10)
        vols = deque(maxlen=50)
        atr_history = deque(maxlen=20)
        closes.append(closes_list[0])
        vols.append(volumes[0])
        atr = 0.0001

        closes_array = np.array(closes_list)
        highs_array = np.array(highs)
        lows_array = np.array(lows)
        volumes_array = np.array(volumes)

        for i in range(1, len(closes_list)):
            close, high, low, vol = closes_array[i], highs_array[i], lows_array[i], volumes_array[i]
            prev_close = closes[-1]
            closes.append(close)
            vols.append(vol)
            tr = max(high - low, abs(high - prev_close), abs(low - prev_close))
            atr = tr if i == 1 else (atr * (cfg['atr'] - 1) + tr) / cfg['atr']
            atr_history.append(atr)

        current_price = closes_array[-1]
        atr_pct = (atr / current_price * 100) if current_price > 0 else 0.0

        if len(closes) >= cfg['bb']:
            bb_closes = list(closes)[-cfg['bb']:]
            bb_sma = np.mean(bb_closes)
            bb_std = np.std(bb_closes, ddof=1)
            bb_upper = bb_sma + (2 * bb_std)
            bb_lower = bb_sma - (2 * bb_std)
            bb_width = ((bb_upper - bb_lower) / max(bb_sma, 1e-8) * 100)
        else:
            bb_upper = bb_lower = bb_sma = bb_width = 0.0

        if len(vols) < 2:
            vol_surge = 1.0
        else:
            vol_period = min(50, len(vols))
            avg_vol = np.mean(list(vols)[-vol_period:])
            vol_surge = (vols[-1] / avg_vol) if avg_vol > 0 else 1.0

        hv = calculate_historical_volatility(list(closes), cfg['hv'], cfg['annualization_factor'])
        rsi = calculate_rsi(list(closes), cfg['rsi'])
        gainer_score = calculate_volatility_score(atr_pct, bb_width, vol_surge, hv, current_price, bb_upper, bb_lower)

        now = time.time()

        candle_price_history = deque(maxlen=PRICE_HISTORY_SIZE)
        for idx in range(len(closes_list)):
            if idx < len(timestamps):
                timestamp = timestamps[idx] / 1000.0  # Convert ms to seconds
            else:
                timestamp = now - ((len(closes_list) - idx - 1) * cfg['seconds'])
            candle_price_history.append((timestamp, closes_list[idx]))

        tick_price_history = deque(maxlen=TICK_HISTORY_SIZE)
        for timestamp, price in candle_price_history:
            tick_price_history.append((timestamp, price))

        new_state = {
            'prev_close': current_price,
            'closes': closes,
            'volumes': vols,
            'atr': atr,
            'atr_history': atr_history,
            'atr_percent': atr_pct,
            'bb_upper': bb_upper,
            'bb_lower': bb_lower,
            'bb_sma': bb_sma,
            'bb_width': bb_width,
            'volume_surge': vol_surge,
            'historical_volatility': hv,
            'rsi': rsi,
            'gainer_score': gainer_score,
            'price_change_1m': 0.0,
            'price_change_5m': 0.0,
            'price_change_15m': 0.0,
            'price_change_30m': 0.0,
            'last_candle_time': now,
            'candle_price_history': candle_price_history,
            'tick_price_history': tick_price_history,
            'last_update': now,
            'last_indicator_update': now,
            'intra_candle_high': current_price,
            'intra_candle_low': current_price,
            'candle_open_price': current_price,
            'intra_candle_volatility': 0.0
        }

        # Thread-safe state initialization with double-check locking
        lock = ensure_state_lock(symbol)
        with lock:
            if symbol not in STATE:
                STATE[symbol] = {}
            STATE[symbol][timeframe] = new_state

        return True
    except Exception as e:
        logger.error(f"Error init {symbol} {timeframe}: {e}")
        return False

def get_price_change_from_ticks(tick_history: deque, minutes: int) -> Optional[float]:
    """Get price change from tick data using binary search"""
    if len(tick_history) < 2:
        return None

    current_time = time.time()
    target_time = current_time - (minutes * 60)

    history_list = list(tick_history)
    current_price = history_list[-1][1]

    if history_list[0][0] > target_time:
        return None

    times = [t for t, p in history_list]
    idx = bisect.bisect_left(times, target_time)

    if idx == 0:
        historical_price = history_list[0][1]
    elif idx == len(history_list):
        historical_price = history_list[-1][1]
    else:
        if abs(times[idx] - target_time) < abs(times[idx-1] - target_time):
            historical_price = history_list[idx][1]
        else:
            historical_price = history_list[idx-1][1]

    return historical_price

def calculate_price_change(symbol: str, timeframe: str, minutes: int,
                          current_price: float, state: Dict[str, Any]) -> float:
    """Calculate price change with fallback to candle data (extracted duplicate logic)"""
    if current_price <= 0:
        return 0.0

    tick_price = get_price_change_from_ticks(state['tick_price_history'], minutes)

    if tick_price is None or tick_price == 0:
        candle_history = state['candle_price_history']
        if len(candle_history) < 2:
            return 0.0

        target_time = time.time() - (minutes * 60)
        history_list = list(candle_history)
        times = [t for t, p in history_list]

        idx = bisect.bisect_left(times, target_time)

        if idx == 0:
            tick_price = history_list[0][1]
        elif idx == len(history_list):
            tick_price = history_list[-1][1]
        else:
            if abs(times[idx] - target_time) < abs(times[idx-1] - target_time):
                tick_price = history_list[idx][1]
            else:
                tick_price = history_list[idx-1][1]

    if tick_price is None or tick_price == 0 or current_price == 0:
        return 0.0

    return ((current_price - tick_price) / tick_price * 100)

def get_price_change(symbol: str, timeframe: str, minutes: int) -> float:
    """Calculate price change wrapper"""
    # Thread-safe check with lock
    lock = ensure_state_lock(symbol)
    with lock:
        if symbol not in STATE or timeframe not in STATE[symbol]:
            return 0.0

    with ws_tickers_lock:
        current_price = ws_tickers.get(symbol, {}).get('c', 0.0)

    # Get state snapshot with minimal lock time
    with lock:
        if symbol not in STATE or timeframe not in STATE[symbol]:
            return 0.0
        state = STATE[symbol][timeframe]
        # Snapshot needed data
        tick_history = state['tick_price_history'].copy()
        candle_history = state['candle_price_history'].copy()

    # Calculate outside lock
    state_snapshot = {
        'tick_price_history': tick_history,
        'candle_price_history': candle_history
    }

    return calculate_price_change(symbol, timeframe, minutes, current_price, state_snapshot)

def calculate_consistent_gainer_status(symbol: str, timeframe: str) -> Optional[Dict[str, int]]:
    """Calculate if a symbol is a consistent gainer in real-time"""
    lock = ensure_state_lock(symbol)
    with lock:
        if symbol not in STATE or timeframe not in STATE[symbol]:
            return None

    with ws_tickers_lock:
        price_change_24h = ws_tickers.get(symbol, {}).get('P', 0.0)

    with lock:
        if symbol not in STATE or timeframe not in STATE[symbol]:
            return None
        state = STATE[symbol][timeframe]

        changes = [
            price_change_24h,
            state.get('price_change_1m', 0),
            state.get('price_change_5m', 0),
            state.get('price_change_15m', 0),
            state.get('price_change_30m', 0)
        ]

        positive_changes = len([change for change in changes if change > 0])

        if positive_changes >= 3:
            return {
                'positive_changes': positive_changes,
                'max_changes': len(changes)
            }

    return None

def safe_queue_put(item: Dict[str, Any], timeout: float = QUEUE_PUT_TIMEOUT) -> bool:
    """Safely put item in queue with timeout and logging"""
    global dropped_updates_count
    try:
        update_queue.put(item, timeout=timeout)
        return True
    except queue.Full:
        with dropped_updates_lock:
            dropped_updates_count += 1
            if dropped_updates_count % 100 == 0:  # Log every 100 dropped updates
                logger.warning(f"Update queue full, total dropped updates: {dropped_updates_count}")
        return False

def process_kline(sym: str, tf: str, k: Dict[str, Any]) -> None:
    """Process kline update with optimized lock usage"""
    try:
        close = safe_float(k.get('c', 0))
        high = safe_float(k.get('h', 0))
        low = safe_float(k.get('l', 0))
        volume = safe_float(k.get('v', 0))
        is_closed = k.get('x', False)

        if close <= 0 or high <= 0 or low <= 0:
            return

        # Thread-safe check with lock
        lock = ensure_state_lock(sym)
        with lock:
            state_exists = sym in STATE and tf in STATE[sym]

        if not state_exists:
            data = fetch_klines(sym, tf)
            if data:
                initialize_state(sym, tf, data)
            return

        cfg = TIMEFRAMES[tf]
        current_time = time.time()

        # Get current price from tickers
        with ws_tickers_lock:
            current_price = ws_tickers.get(sym, {}).get('c', close)

        # Snapshot data with minimal lock time
        with lock:
            if sym not in STATE or tf not in STATE[sym]:
                return
            state = STATE[sym][tf]

            if not is_closed:
                if 'candle_open_price' not in state or state['candle_open_price'] is None:
                    state['candle_open_price'] = close
                    state['intra_candle_high'] = high
                    state['intra_candle_low'] = low
                else:
                    state['intra_candle_high'] = max(state['intra_candle_high'], high)
                    state['intra_candle_low'] = min(state['intra_candle_low'], low)

                candle_range = state['intra_candle_high'] - state['intra_candle_low']
                intra_volatility = (candle_range / close * 100) if close > 0 else 0.0
                state['intra_candle_volatility'] = intra_volatility

            state['candle_price_history'].append((current_time, close))

            # Calculate price changes
            tick_history = state['tick_price_history'].copy()
            candle_history = state['candle_price_history'].copy()

        # Calculate outside lock
        state_snapshot = {
            'tick_price_history': tick_history,
            'candle_price_history': candle_history
        }

        pc_1m = calculate_price_change(sym, tf, 1, current_price, state_snapshot)
        pc_5m = calculate_price_change(sym, tf, 5, current_price, state_snapshot)
        pc_15m = calculate_price_change(sym, tf, 15, current_price, state_snapshot)
        pc_30m = calculate_price_change(sym, tf, 30, current_price, state_snapshot)

        # Update state with calculated values
        with lock:
            if sym not in STATE or tf not in STATE[sym]:
                return
            state['price_change_1m'] = pc_1m
            state['price_change_5m'] = pc_5m
            state['price_change_15m'] = pc_15m
            state['price_change_30m'] = pc_30m
            state['last_update'] = current_time

        # Check consistent gainer status
        consistent_status = calculate_consistent_gainer_status(sym, tf)

        if not is_closed and max(abs(pc_1m), abs(pc_5m), abs(pc_15m), abs(pc_30m)) > 0.01:
            with lock:
                if sym not in STATE or tf not in STATE[sym]:
                    return
                update_data = {
                    'type': 'price_change_update',
                    'symbol': sym,
                    'timeframe': tf,
                    'price_change_1m': pc_1m,
                    'price_change_5m': pc_5m,
                    'price_change_15m': pc_15m,
                    'price_change_30m': pc_30m,
                    'intra_candle_volatility': state.get('intra_candle_volatility', 0)
                }

            # Add consistent gainer status to update
            if consistent_status:
                update_data['is_consistent_gainer'] = True
                update_data['positive_changes'] = consistent_status['positive_changes']
                update_data['max_changes'] = consistent_status['max_changes']

            safe_queue_put(update_data)
            return

        if not is_closed:
            return

        # CANDLE CLOSED - UPDATE INDICATORS INCREMENTALLY
        logger.info(f"🔄 {sym} {tf} CANDLE CLOSED - UPDATING INDICATORS")

        # Use incremental update instead of full fetch
        with lock:
            if sym not in STATE or tf not in STATE[sym]:
                return
            update_success = update_indicators_incremental(state, close, high, low, volume, cfg)

        if update_success:
            with lock:
                if sym not in STATE or tf not in STATE[sym]:
                    return
                state['last_indicator_update'] = current_time
                state['candle_open_price'] = close  # Reset for next candle
                state['intra_candle_high'] = close
                state['intra_candle_low'] = close

                # Snapshot updated data
                update_data = {
                    'type': 'indicator_update',
                    'symbol': sym,
                    'timeframe': tf,
                    'atr_percent': state.get('atr_percent', 0),
                    'bb_width': state.get('bb_width', 0),
                    'volume_surge': state.get('volume_surge', 1.0),
                    'historical_volatility': state.get('historical_volatility', 0),
                    'rsi': state.get('rsi', 50),
                    'gainer_score': state.get('gainer_score', 0),
                    'price_change_1m': state.get('price_change_1m', 0),
                    'price_change_5m': state.get('price_change_5m', 0),
                    'price_change_15m': state.get('price_change_15m', 0),
                    'price_change_30m': state.get('price_change_30m', 0),
                    'last_indicator_update': current_time
                }

            logger.debug(f"✅ {sym} {tf} indicators updated incrementally")

            # Check consistent gainer status after indicator update
            consistent_status = calculate_consistent_gainer_status(sym, tf)

            # Add consistent gainer status to update
            if consistent_status:
                update_data['is_consistent_gainer'] = True
                update_data['positive_changes'] = consistent_status['positive_changes']
                update_data['max_changes'] = consistent_status['max_changes']

            safe_queue_put(update_data)
        else:
            logger.warning(f"⚠️ Failed to update indicators for {sym} {tf}")

    except Exception as e:
        logger.debug(f"Error process {sym} {tf}: {e}")

def websocket_price_updater() -> None:
    """WebSocket updater for price tickers with connection tracking"""
    thread_name = 'ws_price_updater'
    with active_threads_lock:
        active_threads[thread_name] = threading.current_thread()

    try:
        while not all_symbols and not shutdown_event.is_set():
            time.sleep(1)

        if shutdown_event.is_set():
            return

        ws_url = "wss://stream.binance.com:9443/ws/!ticker@arr"
        reconnect_delay = 1
        reconnect_attempts = 0
        ws = None
        last_heartbeat = time.time()
        last_message_time = time.time()

        while not shutdown_event.is_set():
            try:
                ws = create_connection(ws_url, timeout=60)

                # Track connection for cleanup
                with ws_connections_lock:
                    ws_connections.append(ws)

                logger.info("✅ Price WebSocket connected")
                reconnect_delay = 1
                reconnect_attempts = 0
                last_heartbeat = time.time()
                last_message_time = time.time()

                while not shutdown_event.is_set():
                    # Check heartbeat - if no message for WS_HEARTBEAT_INTERVAL, reconnect
                    current_time = time.time()
                    if current_time - last_message_time > WS_HEARTBEAT_INTERVAL:
                        logger.warning(f"Price WebSocket no data for {WS_HEARTBEAT_INTERVAL}s, reconnecting...")
                        break

                    try:
                        ws.settimeout(10)  # Set socket timeout to prevent infinite blocking
                        data = json.loads(ws.recv())
                        last_heartbeat = time.time()
                        last_message_time = time.time()

                        for ticker in data:
                            if not ticker['s'].endswith('USDT'):
                                continue
                            symbol = ticker['s'][:-4]
                            if symbol not in all_symbols:
                                continue
                            price = safe_float(ticker.get('c', 0))
                            change = safe_float(ticker.get('P', 0))
                            if price <= 0:
                                continue

                            with ws_tickers_lock:
                                ws_tickers[symbol] = {'c': price, 'P': change}

                            current_time = time.time()
                            lock = ensure_state_lock(symbol)
                            with lock:
                                if symbol in STATE:
                                    for tf in TIMEFRAMES.keys():
                                        if tf in STATE[symbol]:
                                            STATE[symbol][tf]['tick_price_history'].append((current_time, price))
                                            STATE[symbol][tf]['last_update'] = current_time

                            if abs(change) > 0.01:
                                safe_queue_put({
                                    'type': 'price_update',
                                    'symbol': symbol,
                                    'price': price,
                                    'change': change
                                })
                    except WebSocketException:
                        logger.warning("Price WebSocket exception, reconnecting...")
                        break
                    except Exception as e:
                        logger.debug(f"Price WS parse error: {e}")
                        continue
            except Exception as e:
                reconnect_attempts += 1
                logger.error(f"❌ Price WS error (attempt {reconnect_attempts}): {e}")
                time.sleep(reconnect_delay)
                reconnect_delay = min(reconnect_delay * 2, 30)
            finally:
                if ws:
                    try:
                        with ws_connections_lock:
                            if ws in ws_connections:
                                ws_connections.remove(ws)
                        ws.close()
                    except:
                        pass
                    ws = None

        logger.info("Price WebSocket updater shutting down...")
    finally:
        with active_threads_lock:
            if thread_name in active_threads:
                del active_threads[thread_name]

def websocket_kline_updater(timeframe: str) -> None:
    """WebSocket updater for kline data with connection tracking"""
    thread_name = f'ws_kline_{timeframe}'
    with active_threads_lock:
        active_threads[thread_name] = threading.current_thread()

    try:
        bootstrap_event.wait()

        if shutdown_event.is_set():
            return

        interval = TIMEFRAMES[timeframe]['interval']
        symbol_groups = [all_symbols[i:i+100] for i in range(0, len(all_symbols), 100)]
        logger.info(f"🚀 Starting {timeframe} WebSocket monitor")

        for group_id, symbols_group in enumerate(symbol_groups):
            def run_group():
                group_thread_name = f'ws_kline_{timeframe}_group_{group_id}'
                with active_threads_lock:
                    active_threads[group_thread_name] = threading.current_thread()

                try:
                    full_symbols = [f"{s.lower()}usdt@kline_{interval}" for s in symbols_group]
                    streams = "/".join(full_symbols)
                    ws_url = f"wss://stream.binance.com:9443/stream?streams={streams}"
                    reconnect_delay = 1
                    reconnect_attempts = 0
                    ws = None
                    last_heartbeat = time.time()
                    last_message_time = time.time()

                    while not shutdown_event.is_set():
                        try:
                            ws = create_connection(ws_url, timeout=60)

                            # Track connection for cleanup
                            with ws_connections_lock:
                                ws_connections.append(ws)

                            logger.info(f"✅ {timeframe} Group {group_id+1} connected")
                            reconnect_delay = 1
                            reconnect_attempts = 0
                            last_heartbeat = time.time()
                            last_message_time = time.time()

                            while not shutdown_event.is_set():
                                current_time = time.time()
                                if current_time - last_message_time > WS_HEARTBEAT_INTERVAL:
                                    logger.warning(f"{timeframe} Group {group_id+1} no data for {WS_HEARTBEAT_INTERVAL}s, reconnecting...")
                                    break

                                try:
                                    ws.settimeout(10)  # Set socket timeout
                                    msg = json.loads(ws.recv())
                                    last_heartbeat = time.time()
                                    last_message_time = time.time()

                                    if 'data' in msg and msg['data']['e'] == 'kline':
                                        k = msg['data']['k']
                                        sym = msg['data']['s'][:-4].upper()
                                        process_kline(sym, timeframe, k)
                                except WebSocketException:
                                    logger.warning(f"{timeframe} Group {group_id+1} WebSocket exception, reconnecting...")
                                    break
                                except Exception as e:
                                    logger.debug(f"{timeframe} Group {group_id+1} parse error: {e}")
                                    continue
                        except Exception as e:
                            reconnect_attempts += 1
                            logger.error(f"❌ {timeframe} Group {group_id+1} error (attempt {reconnect_attempts}): {e}")
                            time.sleep(reconnect_delay)
                            reconnect_delay = min(reconnect_delay * 2, 30)
                        finally:
                            if ws:
                                try:
                                    with ws_connections_lock:
                                        if ws in ws_connections:
                                            ws_connections.remove(ws)
                                    ws.close()
                                except:
                                    pass
                                ws = None

                    logger.info(f"{timeframe} Group {group_id+1} updater shutting down...")
                finally:
                    with active_threads_lock:
                        if group_thread_name in active_threads:
                            del active_threads[group_thread_name]

            threading.Thread(target=run_group, daemon=True).start()
            time.sleep(1)
    finally:
        with active_threads_lock:
            if thread_name in active_threads:
                del active_threads[thread_name]

def cleanup_inactive_symbols() -> None:
    """Periodically clean up inactive symbols to prevent memory bloat"""
    thread_name = 'cleanup_inactive'
    with active_threads_lock:
        active_threads[thread_name] = threading.current_thread()

    try:
        while not shutdown_event.is_set():
            time.sleep(SYMBOL_CLEANUP_INTERVAL)

            if shutdown_event.is_set():
                break

            current_time = time.time()
            symbols_to_remove = []

            # Find inactive symbols
            for symbol in list(STATE.keys()):
                lock = ensure_state_lock(symbol)
                with lock:
                    if symbol in STATE:
                        # Check if any timeframe has been updated recently
                        all_inactive = True
                        for tf in STATE[symbol].keys():
                            last_update = STATE[symbol][tf].get('last_update', 0)
                            if current_time - last_update < SYMBOL_INACTIVE_THRESHOLD:
                                all_inactive = False
                                break

                        if all_inactive:
                            symbols_to_remove.append(symbol)

            # Remove inactive symbols
            if symbols_to_remove:
                logger.info(f"🧹 Cleaning up {len(symbols_to_remove)} inactive symbols")
                for symbol in symbols_to_remove:
                    lock = ensure_state_lock(symbol)
                    with lock:
                        if symbol in STATE:
                            del STATE[symbol]

                    # Clean up lock (in production, consider keeping locks)
                    with STATE_CREATION_LOCK:
                        if symbol in STATE_LOCKS:
                            del STATE_LOCKS[symbol]

        logger.info("Cleanup thread shutting down...")
    finally:
        with active_threads_lock:
            if thread_name in active_threads:
                del active_threads[thread_name]

def refresh_timeframe_full_pipeline(timeframe: str) -> None:
    """
    Automatically refresh ALL symbols for a timeframe when the timeframe duration passes.
    Example: For 3M timeframe, refresh every 3 minutes. For 1H, refresh every 1 hour.
    This ensures indicators are recalculated with the latest complete data.
    """
    thread_name = f'refresh_{timeframe}'
    with active_threads_lock:
        active_threads[thread_name] = threading.current_thread()

    try:
        bootstrap_event.wait()

        if shutdown_event.is_set():
            return

        cfg = TIMEFRAMES[timeframe]
        refresh_interval = cfg['seconds']  # Refresh every timeframe period

        logger.info(f"🔄 Starting auto-refresh cycle for {timeframe} (every {refresh_interval}s)")

        while not shutdown_event.is_set():
            # Wait for the timeframe duration
            time.sleep(refresh_interval)

            if shutdown_event.is_set():
                break

            logger.info(f"⏰ {timeframe} period elapsed - Starting full pipeline refresh")

            start_time = time.time()
            total_symbols = len(all_symbols)

            refresh_cycles[timeframe] = {
                'status': 'running',
                'start': start_time,
                'current': 0,
                'total': total_symbols,
                'timeframe': timeframe,
                'type': 'full_pipeline_refresh'
            }

            refreshed = 0
            failed = 0

            # Process in batches to avoid rate limits
            batch_size = 50
            for i in range(0, total_symbols, batch_size):
                if shutdown_event.is_set():
                    break

                batch = all_symbols[i:i + batch_size]

                with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
                    future_to_symbol = {}
                    for symbol in batch:
                        future = executor.submit(fetch_klines, symbol, timeframe, 100)
                        future_to_symbol[future] = symbol

                    for future in as_completed(future_to_symbol):
                        if shutdown_event.is_set():
                            executor.shutdown(wait=False)
                            break

                        symbol = future_to_symbol[future]
                        try:
                            data = future.result()
                            if data:
                                if initialize_state(symbol, timeframe, data):
                                    refreshed += 1
                                else:
                                    failed += 1
                            else:
                                failed += 1
                        except Exception as e:
                            logger.debug(f"Refresh error {symbol} {timeframe}: {e}")
                            failed += 1

                        processed = refreshed + failed
                        refresh_cycles[timeframe].update({
                            'current': processed,
                            'refreshed': refreshed,
                            'failed': failed,
                            'percent': (processed / total_symbols * 100),
                            'status': f"{timeframe}: {processed}/{total_symbols} ({(processed / total_symbols * 100):.1f}%)"
                        })

                # Small delay between batches
                if i + batch_size < total_symbols:
                    time.sleep(0.5)

            end_time = time.time()
            duration = end_time - start_time

            refresh_cycles[timeframe] = {
                'status': 'complete',
                'end': end_time,
                'current': total_symbols,
                'total': total_symbols,
                'refreshed': refreshed,
                'failed': failed,
                'percent': 100.0,
                'timeframe': timeframe,
                'duration': duration,
                'type': 'full_pipeline_refresh'
            }

            timeframe_last_refresh[timeframe] = end_time

            logger.info(f"✅ {timeframe} full pipeline refresh complete: {refreshed} symbols refreshed, {failed} failed in {duration:.1f}s")
            logger.info(f"⏱️  Next {timeframe} refresh in {refresh_interval}s")

        logger.info(f"Refresh thread for {timeframe} shutting down...")
    finally:
        with active_threads_lock:
            if thread_name in active_threads:
                del active_threads[thread_name]

def monitor_threads() -> None:
    """Monitor and restart dead threads"""
    thread_name = 'thread_monitor'
    with active_threads_lock:
        active_threads[thread_name] = threading.current_thread()

    try:
        logger.info("🔍 Thread monitor started")

        while not shutdown_event.is_set():
            time.sleep(THREAD_MONITOR_INTERVAL)

            if shutdown_event.is_set():
                break

            with active_threads_lock:
                threads_snapshot = dict(active_threads)

            # Check price updater
            if 'ws_price_updater' not in threads_snapshot or not threads_snapshot['ws_price_updater'].is_alive():
                logger.warning("⚠️ Price updater thread is dead, restarting...")
                threading.Thread(target=websocket_price_updater, daemon=True).start()

            # Check kline updaters
            for tf in TIMEFRAMES.keys():
                kline_thread_name = f'ws_kline_{tf}'
                if kline_thread_name not in threads_snapshot or not threads_snapshot[kline_thread_name].is_alive():
                    logger.warning(f"⚠️ Kline updater for {tf} is dead, restarting...")
                    threading.Thread(target=websocket_kline_updater, args=(tf,), daemon=True).start()

                refresh_thread_name = f'refresh_{tf}'
                if refresh_thread_name not in threads_snapshot or not threads_snapshot[refresh_thread_name].is_alive():
                    logger.warning(f"⚠️ Refresh thread for {tf} is dead, restarting...")
                    threading.Thread(target=refresh_timeframe_full_pipeline, args=(tf,), daemon=True).start()

            # Check cleanup thread
            if 'cleanup_inactive' not in threads_snapshot or not threads_snapshot['cleanup_inactive'].is_alive():
                logger.warning("⚠️ Cleanup thread is dead, restarting...")
                threading.Thread(target=cleanup_inactive_symbols, daemon=True).start()

            logger.debug(f"✅ Thread monitor check complete - {len(threads_snapshot)} threads active")

        logger.info("Thread monitor shutting down...")
    finally:
        with active_threads_lock:
            if thread_name in active_threads:
                del active_threads[thread_name]

def bootstrap_symbol_timeframe(symbol: str, timeframe: str) -> bool:
    """Bootstrap a single symbol-timeframe pair"""
    data = fetch_klines(symbol, timeframe)
    if data:
        return initialize_state(symbol, timeframe, data)
    return False

def bootstrap_states() -> None:
    """Bootstrap all symbols with retry logic"""
    global all_symbols

    thread_name = 'bootstrap'
    with active_threads_lock:
        active_threads[thread_name] = threading.current_thread()

    try:
        logger.info("📊 Fetching symbols from Binance...")
        with bootstrap_progress_lock:
            bootstrap_progress['status'] = 'Fetching symbols...'
            bootstrap_progress['current'] = 0
            bootstrap_progress['total'] = 0

        # Retry logic for fetching symbols with unlimited attempts
        while not shutdown_event.is_set():
            all_symbols = fetch_all_usdt_symbols()
            if all_symbols:
                break

            logger.warning(f"Failed to fetch symbols, retrying in {BOOTSTRAP_RETRY_DELAY}s...")
            time.sleep(BOOTSTRAP_RETRY_DELAY)

        if not all_symbols or shutdown_event.is_set():
            logger.error("❌ Failed to fetch symbols or shutdown requested!")
            with bootstrap_progress_lock:
                bootstrap_progress['status'] = 'Failed to fetch symbols or shutdown'
            return

        logger.info(f"Found {len(all_symbols)} USDT trading pairs")

        with ws_tickers_lock:
            for symbol in all_symbols:
                ws_tickers[symbol] = {'c': 0.0, 'P': 0.0}

        with bootstrap_progress_lock:
            bootstrap_progress['total'] = len(all_symbols) * len(TIMEFRAMES)
            bootstrap_progress['current'] = 0

        logger.info(f"🔄 Starting bootstrap for {len(all_symbols)} symbols")
        time.sleep(1)
        completed = 0
        batch_size = 50

        for tf in TIMEFRAMES.keys():
            if shutdown_event.is_set():
                return

            logger.info(f"📈 Bootstrapping {tf}...")
            with bootstrap_progress_lock:
                bootstrap_progress['current_timeframe'] = tf
                bootstrap_progress['status'] = f"Processing {tf}..."

            for i in range(0, len(all_symbols), batch_size):
                if shutdown_event.is_set():
                    return

                batch = all_symbols[i:i + batch_size]

                with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
                    future_to_symbol = {executor.submit(bootstrap_symbol_timeframe, symbol, tf): symbol for symbol in batch}
                    for future in as_completed(future_to_symbol):
                        if shutdown_event.is_set():
                            executor.shutdown(wait=False)
                            return

                        symbol = future_to_symbol[future]
                        try:
                            if future.result():
                                completed += 1
                        except Exception as e:
                            logger.error(f"Error bootstrapping {symbol} {tf}: {e}")

                        with bootstrap_progress_lock:
                            bootstrap_progress['current'] = completed
                            total = bootstrap_progress['total']
                            percent = (completed / total * 100) if total > 0 else 0
                            bootstrap_progress['status'] = f"{tf}: {completed}/{total} ({percent:.1f}%)"

                time.sleep(0.5)
            logger.info(f"✅ Completed {tf} timeframe")

        bootstrap_event.set()
        logger.info("✅ BOOTSTRAP COMPLETE! Starting auto-refresh cycles...")
        with bootstrap_progress_lock:
            bootstrap_progress['status'] = 'Complete - WebSockets Active'

        # Start automatic refresh cycles for each timeframe
        for tf in TIMEFRAMES.keys():
            threading.Thread(target=refresh_timeframe_full_pipeline, args=(tf,), daemon=True).start()
            logger.info(f"🔄 Auto-refresh cycle started for {tf} (refreshes every {TIMEFRAMES[tf]['seconds']}s)")
            time.sleep(0.5)

        # Start cleanup thread
        threading.Thread(target=cleanup_inactive_symbols, daemon=True).start()
        logger.info("🧹 Inactive symbol cleanup thread started")

        # Start thread monitor
        threading.Thread(target=monitor_threads, daemon=True).start()
        logger.info("🔍 Thread monitor started")
    finally:
        with active_threads_lock:
            if thread_name in active_threads:
                del active_threads[thread_name]

def cleanup_resources() -> None:
    """Cleanup resources on shutdown"""
    logger.info("🔄 Cleaning up resources...")
    shutdown_event.set()

    # Close all WebSocket connections
    with ws_connections_lock:
        logger.info(f"Closing {len(ws_connections)} WebSocket connections...")
        for ws in ws_connections:
            try:
                ws.close()
            except:
                pass
        ws_connections.clear()

    # Clear queues
    while not update_queue.empty():
        try:
            update_queue.get_nowait()
        except queue.Empty:
            break

    logger.info("✅ Cleanup complete")

def signal_handler(sig: int, frame: Any) -> None:
    """Handle shutdown signals"""
    logger.info(f"Received signal {sig}, shutting down gracefully...")
    cleanup_resources()
    sys.exit(0)

# Register cleanup handlers
atexit.register(cleanup_resources)
signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)

@app.route("/")
def index():
    return render_template("index.html")

@app.route("/api/start-bootstrap", methods=['POST'])
@limiter.limit("5 per minute")
def start_bootstrap():
    if bootstrap_event.is_set():
        return jsonify({'status': 'already_running', 'message': 'Bootstrap already completed'})
    threading.Thread(target=bootstrap_states, daemon=True).start()
    return jsonify({'status': 'started'})

@app.route("/api/start-websockets", methods=['POST'])
@limiter.limit("5 per minute")
def start_websockets():
    threading.Thread(target=websocket_price_updater, daemon=True).start()
    for tf in TIMEFRAMES.keys():
        threading.Thread(target=websocket_kline_updater, args=(tf,), daemon=True).start()
        time.sleep(0.5)
    return jsonify({'status': 'started'})

@app.route("/api/bootstrap-status")
@limiter.limit("60 per minute")
def get_bootstrap_status():
    with bootstrap_progress_lock:
        return jsonify(dict(bootstrap_progress))

@app.route("/api/health")
@limiter.limit("120 per minute")  # Increased from 60
def health_check():
    with dropped_updates_lock:
        dropped_count = dropped_updates_count

    with ws_connections_lock:
        active_connections = len(ws_connections)

    with active_threads_lock:
        thread_count = len(active_threads)
        thread_names = list(active_threads.keys())

    return jsonify({
        'status': 'running',
        'websockets_active': thread_count,
        'websocket_connections': active_connections,
        'symbols_initialized': len(STATE),
        'queue_size': update_queue.qsize(),
        'total_symbols': len(all_symbols),
        'bootstrap_complete': bootstrap_event.is_set(),
        'refresh_cycles': refresh_cycles,
        'last_refresh_times': timeframe_last_refresh,
        'dropped_updates': dropped_count,
        'active_thread_names': thread_names
    })

@app.route("/api/data/<timeframe>")
@limiter.limit("120 per minute")  # Increased from 30
def get_data(timeframe: str):
    # Validate timeframe
    if timeframe not in TIMEFRAMES:
        return jsonify({'error': 'Invalid timeframe'}), 400

    if not all_symbols:
        return jsonify({'error': 'System initializing, please wait'}), 503

    # OPTIMIZATION: Create bulk snapshot to avoid per-symbol locks
    data_list = []

    # Get ticker snapshot once
    with ws_tickers_lock:
        ticker_snapshot = dict(ws_tickers)

    # Collect all data with minimal lock time per symbol
    for symbol in all_symbols:
        ticker = ticker_snapshot.get(symbol, {'c': 0.0, 'P': 0.0})
        price = safe_float(ticker.get('c', 0))

        # Quick lock check - don't hold lock while building response
        lock = ensure_state_lock(symbol)
        with lock:
            if symbol not in STATE or timeframe not in STATE[symbol]:
                state_data = None
            else:
                # Copy only what we need
                state = STATE[symbol][timeframe]
                state_data = {
                    'price_change_1m': state.get('price_change_1m', 0),
                    'price_change_5m': state.get('price_change_5m', 0),
                    'price_change_15m': state.get('price_change_15m', 0),
                    'price_change_30m': state.get('price_change_30m', 0),
                    'atr_percent': state.get('atr_percent', 0),
                    'bb_width': state.get('bb_width', 0),
                    'volume_surge': state.get('volume_surge', 1.0),
                    'historical_volatility': state.get('historical_volatility', 0),
                    'rsi': state.get('rsi', 50),
                    'gainer_score': state.get('gainer_score', 0),
                    'last_indicator_update': state.get('last_indicator_update', 0),
                    'intra_candle_volatility': state.get('intra_candle_volatility', 0)
                }

        # Build response outside lock
        if state_data is None:
            data_list.append({
                'symbol': symbol,
                'price': price if price > 0 else 0.0,
                'priceChangePercent': safe_float(ticker.get('P', 0)),
                'price_change_1m': 0,
                'price_change_5m': 0,
                'price_change_15m': 0,
                'price_change_30m': 0,
                'atr_percent': 0,
                'bb_width': 0,
                'volume_surge': 1.0,
                'historical_volatility': 0,
                'rsi': 50,
                'gainer_score': 0,
                'last_indicator_update': 0,
                'intra_candle_volatility': 0
            })
        else:
            data_list.append({
                'symbol': symbol,
                'price': price,
                'priceChangePercent': safe_float(ticker.get('P', 0)),
                **state_data
            })

    return jsonify(data_list)

@app.route("/api/top-gainers/<timeframe>")
@limiter.limit("120 per minute")  # Increased from 30
def get_top_gainers(timeframe: str):
    normalized_tf = timeframe.lower()

    # Validate timeframe
    if normalized_tf not in TIMEFRAMES:
        return jsonify({'error': 'Invalid timeframe'}), 400

    if not all_symbols:
        return jsonify({'error': 'System initializing, please wait'}), 503

    # Validate limit parameter (enforced server-side)
    limit = request.args.get('limit', 50, type=int)
    if not (1 <= limit <= 500):
        return jsonify({'error': 'Limit must be between 1 and 500'}), 400

    gainer_list = []

    # Get ticker snapshot once
    with ws_tickers_lock:
        ticker_snapshot = dict(ws_tickers)

    # OPTIMIZATION: Minimize lock time per symbol
    for symbol in all_symbols:
        ticker = ticker_snapshot.get(symbol, {'c': 0.0, 'P': 0.0})
        price = safe_float(ticker.get('c', 0))

        lock = ensure_state_lock(symbol)
        with lock:
            if symbol not in STATE or normalized_tf not in STATE[symbol]:
                continue

            state = STATE[symbol][normalized_tf]
            gainer_score = state.get('gainer_score', 0)

            if gainer_score > 0:
                # Copy data inside lock, build object outside
                state_data = {
                    'price_change_1m': state.get('price_change_1m', 0),
                    'price_change_5m': state.get('price_change_5m', 0),
                    'price_change_15m': state.get('price_change_15m', 0),
                    'price_change_30m': state.get('price_change_30m', 0),
                    'atr_percent': state.get('atr_percent', 0),
                    'bb_width': state.get('bb_width', 0),
                    'volume_surge': state.get('volume_surge', 1.0),
                    'historical_volatility': state.get('historical_volatility', 0),
                    'rsi': state.get('rsi', 50),
                    'gainer_score': gainer_score,
                    'last_indicator_update': state.get('last_indicator_update', 0),
                    'intra_candle_volatility': state.get('intra_candle_volatility', 0)
                }

        # Build response outside lock
        if gainer_score > 0:
            gainer_list.append({
                'symbol': symbol,
                'price': price,
                'priceChangePercent': safe_float(ticker.get('P', 0)),
                **state_data
            })

    gainer_list.sort(key=lambda x: x['gainer_score'], reverse=True)
    return jsonify(gainer_list[:limit])

@app.route("/api/consistent-gainers/<timeframe>")
@limiter.limit("120 per minute")  # Increased from 30
def get_consistent_gainers(timeframe: str):
    normalized_tf = timeframe.lower()

    # Validate timeframe
    if normalized_tf not in TIMEFRAMES:
        return jsonify({'error': 'Invalid timeframe'}), 400

    if not all_symbols:
        return jsonify({'error': 'System initializing, please wait'}), 503

    # Validate limit parameter (enforced server-side)
    limit = request.args.get('limit', 50, type=int)
    if not (1 <= limit <= 500):
        return jsonify({'error': 'Limit must be between 1 and 500'}), 400

    consistent_gainers = []

    # Get ticker snapshot once
    with ws_tickers_lock:
        ticker_snapshot = dict(ws_tickers)

    # OPTIMIZATION: Minimize lock time per symbol
    for symbol in all_symbols:
        ticker = ticker_snapshot.get(symbol, {'c': 0.0, 'P': 0.0})
        price = safe_float(ticker.get('c', 0))
        price_change_24h = safe_float(ticker.get('P', 0))

        lock = ensure_state_lock(symbol)
        with lock:
            if symbol not in STATE or normalized_tf not in STATE[symbol]:
                continue

            state = STATE[symbol][normalized_tf]

            # Calculate positive changes inside lock
            changes = [
                price_change_24h,
                state.get('price_change_1m', 0),
                state.get('price_change_5m', 0),
                state.get('price_change_15m', 0),
                state.get('price_change_30m', 0)
            ]

            positive_changes = len([change for change in changes if change > 0])

            if positive_changes >= 3:
                state_data = {
                    'price_change_1m': state.get('price_change_1m', 0),
                    'price_change_5m': state.get('price_change_5m', 0),
                    'price_change_15m': state.get('price_change_15m', 0),
                    'price_change_30m': state.get('price_change_30m', 0),
                    'last_update': state.get('last_update', 0),
                    'positive_changes': positive_changes
                }

        # Build response outside lock
        if positive_changes >= 3:
            consistent_gainers.append({
                'symbol': symbol,
                'price': price,
                'priceChangePercent': price_change_24h,
                **state_data
            })

    consistent_gainers.sort(key=lambda x: (
        x['positive_changes'],
        max(abs(x['price_change_1m']),
            abs(x['price_change_5m']),
            abs(x['price_change_15m']),
            abs(x['price_change_30m']))
    ), reverse=True)

    return jsonify(consistent_gainers[:limit])

@app.route("/ws")
def ws_endpoint():
    def event_stream():
        while not shutdown_event.is_set():
            try:
                msg = update_queue.get(timeout=30)
                yield f"data: {json.dumps(msg)}\n\n"
            except queue.Empty:
                yield f"data: {json.dumps({'type': 'heartbeat'})}\n\n"

    return Response(event_stream(), mimetype="text/event-stream")

if __name__ == "__main__":
    logger.info("🚀 Flask server starting...")
    app.run(debug=False, threaded=True, host='0.0.0.0', port=9100)