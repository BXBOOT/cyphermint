import socket
import threading
import json
import hashlib
import time
import os
import sys
import base64
import ecdsa
import signal
import argparse
import struct
import requests
from decimal import Decimal, getcontext
from typing import List, Dict, Optional, Tuple
import math
import random
from collections import deque
from datetime import datetime, timedelta


getcontext().prec = 16

# Bitcoin-like constants
PEER_PORT = 8334
BLOCKCHAIN_FILE = 'blockchain.json'
WALLET_FILE_DEFAULT = 'wallet.json'
PEERS_FILE = 'peers.json'
MEMPOOL_FILE = 'mempool.json'
UTXO_FILE = 'utxos.json'
CONSENSUS_ANALYTICS_FILE = 'consensus_analytics.json'
WITNESS_FILE = 'witness_nodes.json'
RECENT_DUP_WINDOW = 5

# Cyphermint consensus parameters
INITIAL_REWARD = 50 * 100000000  # 50 CPM in satoshis
HALVING_INTERVAL = 210000  # blocks
DIFFICULTY_ADJUSTMENT_INTERVAL = 2016  # blocks
TARGET_BLOCK_TIME = 600  # 10 minutes in seconds
MAX_TARGET = 0x1d00ffff  # Initial difficulty target


# --- Orphan/backfill globals & RPC helper ---
ORPHAN_BLOCKS: Dict[str, Dict] = {}
BACKFILL_QUEUE: set = set()
LIVE_PEERS_CACHE = set()
LIVE_PEERS_LOCK = threading.Lock()

# How many peers to ping per discovery tick (keep small on tiny nets)
DISCOVERY_FANOUT = int(os.environ.get("CYM_DISCOVERY_FANOUT", "2"))
# Don’t ask the same peer for peers again before this many seconds
GETPEERS_TTL     = int(os.environ.get("CYM_GETPEERS_TTL", "300"))  # 5 min
# Backoff (seconds) when a connect or recv fails; doubles up to MAX
DEFAULT_BACKOFF  = 60
MAX_BACKOFF      = 900

# Per-peer state
LAST_GETPEERS = {}   # (ip,port) -> last_ts
PEER_BACKOFF  = {}   # (ip,port) -> retry_after_ts

CHAIN_SEGMENT_MAX     = 200          # must be <= server cap
SINGLE_SYNC_TTL       = 120          # don't re-sync same peer within 2 min
_single_sync_backoff  = {}           # (ip,port) -> retry_after_ts

def request_block_by_hash(ip: str, port: int, block_hash: str) -> Optional[Dict]:
    """Ask a peer for a block by its hash. Returns a block dict or None."""
    try:
        with socket.create_connection((ip, port), timeout=5) as s:
            req = {"type": "get_block_by_hash", "data": {"hash": block_hash}}
            s.sendall(json.dumps(req).encode())
            s.shutdown(socket.SHUT_WR)
            chunks = []
            while True:
                part = s.recv(65536)
                if not part:
                    break
                chunks.append(part)
        if not chunks:
            return None
        resp = json.loads(b"".join(chunks).decode())
        if resp.get("type") == "block_response" and resp.get("data"):
            return resp["data"]
    except Exception:
        return None
    return None

# ---- Normalization & work helpers ----

def cmd_repair_duplicate_heights() -> None:
    """
    One-time chain repair:
      - builds a contiguous, deduped prefix from genesis using link-first + work preference
      - writes the repaired chain back to disk atomically
      - rebuilds the UTXO set
    """
    with BLOCKCHAIN_LOCK:
        chain = load_json(BLOCKCHAIN_FILE, [])
    before = len(chain)
    if not chain:
        print("❌ Empty chain; nothing to repair")
        return

    # Use your existing normalization helper
    fixed = sort_and_dedupe_by_index(chain)
    after = len(fixed)

    if not fixed:
        print("❌ Repair failed: could not construct a contiguous prefix")
        return

    # Persist repaired chain
    with BLOCKCHAIN_LOCK:
        save_json(BLOCKCHAIN_FILE, fixed)

    # Rebuild UTXOs (works whether your rebuild takes a param or not)
    try:
        rebuild_utxo_set(fixed)          # if your signature is rebuild_utxo_set(blockchain)
    except TypeError:
        rebuild_utxo_set()               # if your signature is rebuild_utxo_set() with internal load

    tip = fixed[-1]
    print(f"✅ Repaired chain to contiguous height {tip.get('index')} ({after}/{before} kept)")
    print("🔧 UTXO set rebuilt")

def try_adopt_chain(candidate_chain: List[Dict]) -> bool:
    """
    Adopt candidate_chain iff it is valid and strictly better by total work
    (height breaks ties). Atomically replaces BLOCKCHAIN_FILE, then rebuilds
    UTXOs (if a rebuild helper exists) and prunes confirmed txs from mempool.
    Returns True if adoption happened.
    """
    # 0) Sanity
    if not candidate_chain or not is_valid_chain(candidate_chain):
        return False

    # Candidate tip info
    cand_h = candidate_chain[-1].get("index", len(candidate_chain) - 1)
    cand_w = calculate_chain_work(candidate_chain)

    # 1) Compare against local tip under lock
    with BLOCKCHAIN_LOCK:
        local_chain = load_json(BLOCKCHAIN_FILE, [])
        if local_chain:
            local_h = local_chain[-1].get("index", len(local_chain) - 1)
            local_w = calculate_chain_work(local_chain)
        else:
            local_h, local_w = -1, 0

        # Must be strictly better by work (height breaks ties)
        if not (cand_w > local_w or (cand_w == local_w and cand_h > local_h)):
            return False

        # 2) Atomic write of new chain
        tmp = BLOCKCHAIN_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(candidate_chain, f, indent=2)
            f.flush(); os.fsync(f.fileno())
        os.replace(tmp, BLOCKCHAIN_FILE)

        # 3) Optional: rebuild UTXOs if your project exposes a helper
        rebuild_fn = (globals().get("rebuild_utxo_set_from_chain")
                      or globals().get("rebuild_utxos")
                      or globals().get("reindex_utxos_from_chain"))
        if callable(rebuild_fn):
            try:
                rebuild_fn(candidate_chain)
            except Exception as e:
                print(f"⚠️ UTXO rebuild failed after adoption: {e}")

        # 4) Best-effort: prune confirmed txs from mempool
        try:
            mem = load_json(MEMPOOL_FILE, [])
            confirmed = {
                tx.get("txid")
                for b in candidate_chain
                for tx in b.get("transactions", [])
                if tx.get("txid")
            }
            mem = [tx for tx in mem if tx.get("txid") not in confirmed]
            save_json(MEMPOOL_FILE, mem)
        except Exception:
            pass

    print(f"✅ Chain adopted: height {cand_h}, work {cand_w}")
    return True

def _local_tip_info() -> Tuple[int, int]:
    """
    Return (local_height, local_total_work) from the current on-disk chain.
    Height is the last block's index (or len(chain)-1 as fallback).
    """
    with BLOCKCHAIN_LOCK:
        chain = load_json(BLOCKCHAIN_FILE, [])
    if not chain:
        return (-1, 0)
    h = chain[-1].get('index', len(chain) - 1)
    w = calculate_chain_work(chain)
    return (int(h), int(w))


def get_peer_info_quick(ip: str, port: int, timeout: int = 5) -> Optional[dict]:
    """
    Lightweight pre-check: ask a peer for height/total_work before any heavy sync.
    Returns: {'ip','port','height','total_work','latest_hash'} or None.
    """
    if is_self_peer(ip):
        return None

    s = create_safe_connection(ip, port, timeout=timeout)
    if not s:
        return None

    try:
        s.settimeout(timeout)
        # If your server expects newline-delimited JSON, add + b"\\n"
        s.sendall(json.dumps({'type': 'get_info'}).encode())
        data = s.recv(BUFFER_SIZE)
        if not data:
            return None

        msg = json.loads(data.decode())
        if msg.get('type') != 'info_response':
            return None

        d = msg.get('data', {}) or {}
        return {
            'ip': ip,
            'port': port,
            'height': int(d.get('height', -1)),
            'total_work': int(d.get('total_work', 0)),
            'latest_hash': d.get('latest_hash'),
        }
    except Exception:
        return None
    finally:
        try:
            s.close()
        except:
            pass


def _block_hash_of(b: Dict) -> str:
    return b.get('hash') or b.get('block_hash') or ''

def _block_index_of(b: Dict) -> int:
    try:
        return int(b.get('index', -1))
    except Exception:
        return -1

def _block_prev_hash_of(b: Dict) -> str:
    return b.get('previous_hash') or b.get('prev_hash') or ''

def _per_block_work(bits: int) -> int:
    try:
        target = DifficultyAdjustment.bits_to_target(bits or MAX_TARGET)
        return (1 << 256) // (target + 1)
    except Exception:
        return 0

def sort_and_dedupe_by_index(chain: List[Dict]) -> List[Dict]:
    """Return a contiguous, deduped prefix of the chain ordered by height.
    For each height, prefer a candidate that links to the chosen prev; else, highest work.
    Stop at the first height gap.
    """
    if not chain:
        return []
    # Group by height
    by_idx: Dict[int, List[Dict]] = {}
    for b in chain:
        idx = _block_index_of(b)
        if idx >= 0:
            by_idx.setdefault(idx, []).append(b)
    if not by_idx:
        return []
    heights = sorted(by_idx.keys())
    start_h = 0 if 0 in by_idx else heights[0]
    cands0 = by_idx[start_h]
    chosen0 = max(cands0, key=lambda x: _per_block_work(x.get('bits', MAX_TARGET)))
    result: List[Dict] = [chosen0]
    expected_next = _block_index_of(chosen0) + 1
    for h in heights:
        if h <= _block_index_of(chosen0):
            continue
        if h != expected_next:
            break
        candidates = by_idx[h]
        prev = result[-1]
        linked = [c for c in candidates if _block_prev_hash_of(c) == _block_hash_of(prev)]
        if linked:
            chosen = max(linked, key=lambda x: _per_block_work(x.get('bits', MAX_TARGET)))
        else:
            chosen = max(candidates, key=lambda x: _per_block_work(x.get('bits', MAX_TARGET)))
        result.append(chosen)
        expected_next += 1
    return result
BUFFER_SIZE = 65536

CONNECTION_TIMEOUT = 30
PEER_TIMEOUT = 15
BROADCAST_TIMEOUT = 10
BASE_PEER_BROADCAST_INTERVAL = 600
MINING_SYNC_INTERVAL = 1

# Consensus parameters
MAX_CONCURRENT_CONNECTIONS = 100
CONNECTIONS_PER_PEER = 20
MAX_CONNECTIONS = 100

# Chain switch dampening
CHAIN_SWITCH_DAMPENING = 30        # Seconds between allowed switches
MIN_IMPROVEMENT_NORMAL = 3         # Required improvement normally
MIN_IMPROVEMENT_DAMPENED = 5       # Required improvement during dampening

# Consensus timing constants (matching what's used in the code)
BASE_CONSENSUS_CHECK_INTERVAL = 30  # Base interval for consensus checks
ADAPTIVE_CONSENSUS_INTERVAL = 30    # Current adaptive interval (will be modified)
LAST_CONSENSUS_TIME = 0            # Last time consensus was checked
MIN_CONSENSUS_INTERVAL = 10        # Minimum interval when behind
MAX_CONSENSUS_INTERVAL = 300       # Maximum interval when synced

# Consensus parameters
CONSENSUS_THRESHOLD_PEER = 2       # Already defined in your code
MAX_CONSENSUS_PEERS = 10           # Maximum peers to check

# ------------------------------------------------------------------
# Local address detection and self-peer filtering
# ------------------------------------------------------------------
from typing import Set

# Maintain a set of IP addresses that identify this node. Any outbound
# connection attempt to an address in this set will be skipped. This
# prevents the node from inadvertently connecting to itself, which can
# saturate the connection pool and trigger "Too many connections" errors.
LOCAL_IPS: Set[str] = set()

# Additional missing functions that need to be defined
def validate_chain_indices_match_positions(chain: List[Dict]) -> bool:
    """Ensure each block's index field matches its position in the chain"""
    for i, block in enumerate(chain):
        if block.get('index') != i:
            print(f"❌ Block at position {i} has index {block.get('index')} - INVALID CHAIN")
            return False
    return True

def validate_blockchain_indices(chain: List[Dict]) -> bool:
    """Validate that blockchain has no duplicate indices and proper sequence"""
    if not chain:
        return True
    
    # Check first block is genesis
    if chain[0]['index'] != 0:
        print(f"❌ Chain doesn't start with genesis block")
        return False
    
    # Check each block has correct index
    for i, block in enumerate(chain):
        if block['index'] != i:
            print(f"❌ Block at position {i} has index {block['index']}")
            return False
    
    # Check no duplicate indices
    indices = [block['index'] for block in chain]
    if len(indices) != len(set(indices)):
        print(f"❌ Duplicate block indices found")
        return False
    
    return True

def create_safe_socket():
    """Create a socket with proper settings"""
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    return sock

def receive_full_message(sock):
    """Receive a complete message from socket"""
    try:
        sock.settimeout(PEER_TIMEOUT)
        data = sock.recv(BUFFER_SIZE)
        if data:
            return json.loads(data.decode())
    except:
        return None
    return None

def create_message(msg_type: str, data: dict) -> bytes:
    """Create a message to send"""
    message = {
        'type': msg_type,
        'data': data,
        'timestamp': time.time()
    }
    return json.dumps(message).encode()

def validate_blockchain(chain: List[Dict]) -> bool:
    """Validate an entire blockchain"""
    if not chain:
        return False
    
    # Check genesis block
    if chain[0]['index'] != 0:
        return False
    
    # Validate each block
    for i in range(1, len(chain)):
        if not validate_block(chain[i], chain[i-1]):
            return False
    
    return True

def wallet_manager():
    """Placeholder for wallet manager - this should be defined elsewhere in your code"""
    pass

def broadcast_chain_info(peers: List[Tuple[str, int]]):
    """Broadcast our chain info to peers"""
    pass

def _initialize_local_ips() -> None:
    """
    Populate the LOCAL_IPS set with addresses that refer to this node.  It
    attempts to resolve the hostname to an IP and adds common local
    addresses.  This function is idempotent and safe to call multiple
    times.  If UPnP is enabled later, the discovered internal address
    will be added to LOCAL_IPS within setup_upnp_port.
    """
    try:
        # Attempt to resolve the machine's hostname to an IP.  This may
        # return a LAN address such as 192.168.x.x or 10.x.x.x.
        hostname = socket.gethostname()
        resolved = socket.gethostbyname(hostname)
        if resolved:
            LOCAL_IPS.add(resolved)
    except Exception:
        pass
    # Add common loopback addresses.  Including '0.0.0.0' ensures any
    # configuration using a wildcard bind does not cause self-dialing.
    LOCAL_IPS.update({'127.0.0.1', 'localhost', '0.0.0.0'})
    if os.path.exists('.node_identity'):
        with open('.node_identity', 'r') as f:
            node_data = json.load(f)
            if 'external_ip' in node_data:
                LOCAL_IPS.add(node_data['external_ip'])


def is_self_peer(ip: str, port: int = PEER_PORT) -> bool:
    """Check if a peer address refers to ourselves"""
    # Check against known local IPs
    if ip in LOCAL_IPS:
        return True
    
    # Check if it's our port on localhost variants
    if port == PEER_PORT and ip in ['localhost', '0.0.0.0', '::1']:
        return True
    
    # Check against cached external IP
    external_ip_data = load_json('external_ip_cache.json', {})
    if external_ip_data.get('ip') == ip:
        return True
    
    # Check if IP resolves to one of our hostnames
    try:
        if ip in ['seed1.cyphermint.org', 'seed2.cyphermint.org', 'seed3.cyphermint.org']:
            # These are known seed addresses - check if we're running as a seed
            if '--seed' in sys.argv:
                return True
    except:
        pass
    
    return False

def get_genesis_address() -> str:
    """Load the genesis address from genesis_block.json"""
    if os.path.exists("genesis_block.json"):
        with open("genesis_block.json", "r") as f:
            data = json.load(f)
            return data.get("genesis_address", "0" * 40)
    return "0" * 40

def safe_update_utxos(block):
    try:
        update_utxo_set(block)
    except (KeyError, ValueError) as e:
        print(f"⚠️ UTXO error detected: {e}. Forcing validation and rebuild.")
        rebuild_utxo_set(load_blockchain())
        print("✅ UTXO set successfully rebuilt.")

def rebuild_utxos_from_chain():
    blockchain = load_json("blockchain.json", [])
    utxos = {}
    for block in blockchain:
        for tx in block["transactions"]:
            # Remove spent inputs (if applicable)
            for txin in tx.get("inputs", []):
                key = f"{txin['txid']}:{txin['index']}"
                utxos.pop(key, None)

            # Add outputs using index convention (block hash + index or similar)
            tx_hash = hashlib.sha256(json.dumps(tx, sort_keys=True).encode()).hexdigest()
            for i, output in enumerate(tx["outputs"]):
                utxos[f"{tx_hash}:{i}"] = output

    return utxos



# ------------------------------------------------------------------
# Peer list sanitation
# ------------------------------------------------------------------
from typing import Iterable

def sanitize_peer_list(peers: Iterable[Tuple[str, int]]) -> List[Tuple[str, int]]:
    """Remove self-addresses and duplicates from a peer list.

    This helper iterates over a list of peer tuples, filters out any
    entries that are this node (as determined by :func:`is_self_peer`),
    and removes duplicates while preserving order of first appearance.
    It always returns a list of (ip, port) tuples.
    """
    seen: Set[Tuple[str, int]] = set()
    clean_peers: List[Tuple[str, int]] = []
    for peer in peers:
        if isinstance(peer, (list, tuple)) and len(peer) == 2:
            ip, port = peer[0], peer[1]
            # Skip self addresses
            if is_self_peer(ip):
                continue
            peer_key = (ip, port)
            if peer_key in seen:
                continue
            seen.add(peer_key)
            clean_peers.append(peer_key)
    return clean_peers

# Initialize local IPs immediately on import
_initialize_local_ips()

# Consensus thresholds
CONSENSUS_THRESHOLD_SEED = 1
CONSENSUS_THRESHOLD_PEER = 1
INITIAL_SYNC_ATTEMPTS = 5
PRE_MINING_CONSENSUS_INTERVAL = 1

# Multi-seed approach for redundancy
HARDCODED_SEEDS = [
    ('3.149.130.220', 8334),  # Primary seed (us-east-1)
    ('35.81.59.214', 8334),   # Backup seed (us-west-2)
    ('52.209.95.50', 8334),   # International seed (eu-west-1)
]

# Network magic bytes
MAGIC_BYTES = b'\xF9\xBE\xB4\xD9'

# Enhanced thread safety with RLocks
BLOCKCHAIN_LOCK = threading.RLock()
UTXO_LOCK = threading.RLock()
PEERS_LOCK = threading.RLock()
CONSENSUS_LOCK = threading.RLock()
ANALYTICS_LOCK = threading.RLock()
WITNESS_LOCK = threading.RLock()

# --- Orphan/Backfill globals ---
ORPHAN_BLOCKS = ORPHAN_BLOCKS if 'ORPHAN_BLOCKS' in globals() else {}
BACKFILL_QUEUE = BACKFILL_QUEUE if 'BACKFILL_QUEUE' in globals() else set()

# Connection pool management
ACTIVE_CONNECTIONS = {}
CONNECTION_POOL_LOCK = threading.Lock()
CONNECTION_CACHE = {}
CONNECTION_CACHE_LOCK = threading.Lock()

# Checkpoint system for critical blocks
CHECKPOINTS = {
    0: None,  # Will be set to genesis hash
    1000: None,  # To be updated as network grows
    5000: None,
    10000: None,
    50000: None,
    100000: None
}

# Chain pruning settings
PRUNE_KEEP_RECENT = 10000  # Keep last 10k blocks when pruning
PRUNE_THRESHOLD = 50000    # Start pruning after 50k blocks

# Witness node parameters
WITNESS_THRESHOLD_DAYS = 30
WITNESS_WEIGHT_MULTIPLIER = 1.5
WITNESS_MAX_WEIGHT = 3.0

# Fork memory parameters
FORK_PENALTY_DURATION = 3600  # 1 hour penalty for frequent forking chains
MIN_CHAIN_IMPROVEMENT = 3     # Require 3+ blocks improvement to switch chains

def get_cached_connection(ip: str, port: int) -> Optional[socket.socket]:
    """Get or create a cached connection"""
    key = f"{ip}:{port}"
    
    with CONNECTION_CACHE_LOCK:
        if key in CONNECTION_CACHE:
            sock = CONNECTION_CACHE[key]
            # Test if still alive
            try:
                sock.send(b'')
                return sock
            except:
                del CONNECTION_CACHE[key]
        
        # Create new connection
        sock = create_safe_connection(ip, port)
        if sock:
            CONNECTION_CACHE[key] = sock
        return sock

def load_json(filename, default=None):
    import os
    import json
    if not os.path.exists(filename):
        return default if default is not None else []
    try:
        with open(filename, 'r') as f:
            return json.load(f)
    except (json.JSONDecodeError, IOError):
        return default if default is not None else []
    
def load_blockchain():
    try:
        with open(BLOCKCHAIN_FILE, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return []


# Genesis puzzle stages (disabled)
# The genesis puzzle has been removed for now. If reintroduced, puzzle stage
# definitions will be stored elsewhere (e.g., genesis block metadata).
#GENESIS_PUZZLE_STAGES = {}

# Development mode
DEVELOPMENT_MODE = False

class ConsensusAnalytics:
    """Track and analyze consensus health metrics"""
    
    def __init__(self):
        self.fork_count = 0
        self.reorg_depths = deque(maxlen=100)  # Last 100 reorgs
        self.consensus_times = deque(maxlen=100)  # Last 100 consensus times
        self.network_partitions = 0
        self.last_fork_time = 0
        self.consensus_start_time = time.time()
        
    def record_fork(self, depth: int):
        """Record a blockchain fork/reorg event"""
        self.fork_count += 1
        self.reorg_depths.append(depth)
        self.last_fork_time = time.time()
        
    def record_consensus_time(self, duration: float):
        """Record time taken to reach consensus"""
        self.consensus_times.append(duration)
        
    def get_network_health_score(self) -> float:
        """Calculate network health score (0-100)"""
        score = 100.0
        
        # Penalize for recent forks
        recent_forks = sum(1 for d in self.reorg_depths if d > 0)
        score -= min(recent_forks * 5, 30)  # Max 30 point penalty
        
        # Penalize for deep reorgs
        if self.reorg_depths:
            avg_depth = sum(self.reorg_depths) / len(self.reorg_depths)
            score -= min(avg_depth * 2, 20)  # Max 20 point penalty
        
        # Penalize for slow consensus
        if self.consensus_times:
            avg_time = sum(self.consensus_times) / len(self.consensus_times)
            if avg_time > 30:  # More than 30 seconds average
                score -= min((avg_time - 30), 20)  # Max 20 point penalty
        
        # Time since last fork bonus
        hours_since_fork = (time.time() - self.last_fork_time) / 3600
        score += min(hours_since_fork, 10)  # Max 10 point bonus
        
        return max(0, min(100, score))
    
    def get_stability_score(self) -> float:
        """Get recent network stability (0-1)"""
        if not self.reorg_depths:
            return 1.0
            
        recent_forks = sum(1 for d in list(self.reorg_depths)[-10:] if d > 0)
        return 1.0 - (recent_forks / 10.0)
    
    def save_analytics(self):
        """Save analytics to file"""
        with ANALYTICS_LOCK:
            data = {
                'fork_count': self.fork_count,
                'reorg_depths': list(self.reorg_depths),
                'consensus_times': list(self.consensus_times),
                'network_partitions': self.network_partitions,
                'last_fork_time': self.last_fork_time,
                'consensus_start_time': self.consensus_start_time,
                'health_score': self.get_network_health_score(),
                'stability_score': self.get_stability_score()
            }
            save_json(CONSENSUS_ANALYTICS_FILE, data)
    
    @classmethod
    def load_analytics(cls):
        """Load analytics from file"""
        analytics = cls()
        with ANALYTICS_LOCK:
            data = load_json(CONSENSUS_ANALYTICS_FILE, {})
            if data:
                analytics.fork_count = data.get('fork_count', 0)
                analytics.reorg_depths = deque(data.get('reorg_depths', []), maxlen=100)
                analytics.consensus_times = deque(data.get('consensus_times', []), maxlen=100)
                analytics.network_partitions = data.get('network_partitions', 0)
                analytics.last_fork_time = data.get('last_fork_time', 0)
                analytics.consensus_start_time = data.get('consensus_start_time', time.time())
        return analytics

class ForkMemory:
    """Prevent consensus thrashing by remembering recent forks"""
    
    def __init__(self):
        self.recent_forks = deque(maxlen=20)  # Track last 20 forks
        self.fork_penalties = {}  # Chain fingerprint -> penalty expiry time
        self.chain_switches = deque(maxlen=50)  # Track chain switches
        
    def get_chain_fingerprint(self, chain: List[Dict]) -> str:
        """Create a unique fingerprint for a chain"""
        if not chain:
            return ""
        # Use last 10 block hashes for fingerprint
        last_blocks = chain[-10:] if len(chain) >= 10 else chain
        fingerprint_data = "".join(block['hash'] for block in last_blocks)
        return hashlib.sha256(fingerprint_data.encode()).hexdigest()[:16]
    
    def should_switch_chain(self, current_chain: List[Dict], new_chain: List[Dict], 
                          analytics: ConsensusAnalytics) -> Tuple[bool, str]:
        """Decide whether to switch chains with hysteresis"""
        
        # Basic length check with minimum improvement
        if len(new_chain) < len(current_chain) + MIN_CHAIN_IMPROVEMENT:
            return False, f"New chain not sufficiently longer ({len(new_chain)} vs {len(current_chain)}+{MIN_CHAIN_IMPROVEMENT})"
        
        # Check chain quality score
        current_quality = self.calculate_chain_quality_score(current_chain)
        new_quality = self.calculate_chain_quality_score(new_chain)
        
        if new_quality < current_quality * 0.9:  # New chain must be at least 90% quality
            return False, f"New chain quality too low ({new_quality:.2f} vs {current_quality:.2f})"
        
        # Check if we've recently switched away from this chain
        new_fingerprint = self.get_chain_fingerprint(new_chain)
        if new_fingerprint in self.fork_penalties:
            penalty_expiry = self.fork_penalties[new_fingerprint]
            if time.time() < penalty_expiry:
                time_left = penalty_expiry - time.time()
                return False, f"Chain on penalty timeout ({time_left:.0f}s remaining)"
        
        # Check switch frequency
        recent_switches = len([s for s in self.chain_switches 
                             if s['timestamp'] > time.time() - 3600])
        if recent_switches > 5:  # More than 5 switches in last hour
            return False, "Too many recent chain switches"
        
        # Network stability check
        if analytics.get_stability_score() < 0.5:  # Network unstable
            if len(new_chain) < len(current_chain) + MIN_CHAIN_IMPROVEMENT * 2:
                return False, "Network unstable - requiring extra confirmation"
        
        return True, "Chain switch approved"
    
    def record_chain_switch(self, old_chain: List[Dict], new_chain: List[Dict]):
        """Record a chain switch event"""
        old_fingerprint = self.get_chain_fingerprint(old_chain)
        new_fingerprint = self.get_chain_fingerprint(new_chain)
        
        # Add penalty to old chain to prevent thrashing
        self.fork_penalties[old_fingerprint] = time.time() + FORK_PENALTY_DURATION
        
        # Record switch
        self.chain_switches.append({
            'timestamp': time.time(),
            'old_fingerprint': old_fingerprint,
            'new_fingerprint': new_fingerprint,
            'old_height': len(old_chain),
            'new_height': len(new_chain)
        })
        
        # Record fork depth
        fork_depth = len(old_chain) - self.find_common_ancestor(old_chain, new_chain)
        self.recent_forks.append({
            'timestamp': time.time(),
            'depth': fork_depth
        })
    
    def find_common_ancestor(self, chain1: List[Dict], chain2: List[Dict]) -> int:
        """Find the common ancestor block index"""
        min_length = min(len(chain1), len(chain2))
        for i in range(min_length):
            if chain1[i]['hash'] != chain2[i]['hash']:
                return i - 1
        return min_length - 1
    
    def calculate_chain_quality_score(self, chain: List[Dict]) -> float:
        """Calculate chain quality beyond just PoW"""
        if not chain:
            return 0.0
            
        score = 0.0
        
        # Traditional metrics (40%)
        score += calculate_chain_work(chain) * 0.4
        
        # Chain length (20%)
        score += len(chain) * 0.2
        
        # Transaction diversity (20%)
        score += self.calculate_transaction_diversity(chain) * 0.2
        
        # Time consistency (10%)
        score += self.calculate_time_consistency(chain) * 0.1
        
        # Fee fairness (10%)
        score += self.calculate_fee_fairness(chain) * 0.1
        
        return score
    
    def calculate_transaction_diversity(self, chain: List[Dict]) -> float:
        """Measure transaction diversity in the chain"""
        if len(chain) < 100:
            return 1.0  # Not enough data
            
        unique_addresses = set()
        total_txs = 0
        
        for block in chain[-100:]:  # Last 100 blocks
            for tx in block.get('transactions', []):
                total_txs += 1
                for output in tx.get('outputs', []):
                    addr = output.get('address', output.get('to', ''))
                    if addr:
                        unique_addresses.add(addr)
        
        if total_txs == 0:
            return 0.0
            
        # More unique addresses = higher diversity score
        diversity = len(unique_addresses) / max(total_txs * 0.5, 1)
        return min(1.0, diversity)
    
    def calculate_time_consistency(self, chain: List[Dict]) -> float:
        """Check for time consistency in block timestamps"""
        if len(chain) < 10:
            return 1.0
            
        time_deltas = []
        for i in range(len(chain) - 10, len(chain)):
            if i > 0:
                delta = chain[i]['timestamp'] - chain[i-1]['timestamp']
                time_deltas.append(delta)
        
        if not time_deltas:
            return 1.0
            
        # Penalize chains with suspicious time patterns
        avg_delta = sum(time_deltas) / len(time_deltas)
        variance = sum((d - avg_delta) ** 2 for d in time_deltas) / len(time_deltas)
        
        # Lower variance = more consistent = higher score
        consistency_score = 1.0 / (1.0 + variance / 10000)
        return consistency_score
    
    def calculate_fee_fairness(self, chain: List[Dict]) -> float:
        """Measure fee distribution fairness"""
        # This rewards chains that don't have extreme fee manipulation
        # Implementation would analyze fee patterns
        return 0.8  # Placeholder for now

class ConsensusWitness:
    """Long-running nodes gain special consensus weight"""
    
    def __init__(self):
        self.node_id = self.generate_node_id()
        self.start_time = time.time()
        self.blocks_validated = 0
        self.last_seen_block = 0
        self.witness_status = False
        self.reliability_score = 1.0
        
    def generate_node_id(self) -> str:
        """Generate unique node ID"""
        # Combine MAC address, timestamp, and random data
        node_data = f"{time.time()}-{os.urandom(16).hex()}"
        return hashlib.sha256(node_data.encode()).hexdigest()[:16]
    
    def update_validation_count(self, block_height: int):
        """Update blocks validated count"""
        if block_height > self.last_seen_block:
            self.blocks_validated += 1
            self.last_seen_block = block_height
    
    def get_uptime_days(self) -> float:
        """Get node uptime in days"""
        return (time.time() - self.start_time) / 86400
    
    def calculate_witness_weight(self) -> float:
        """Calculate consensus weight for this witness node"""
        uptime_days = self.get_uptime_days()
        
        if uptime_days < WITNESS_THRESHOLD_DAYS:
            return 1.0  # Normal weight for new nodes
        
        # Calculate reliability score
        expected_blocks = (time.time() - self.start_time) / TARGET_BLOCK_TIME
        if expected_blocks > 0:
            self.reliability_score = min(self.blocks_validated / expected_blocks, 1.0)
        
        # Apply witness weight multiplier
        base_weight = WITNESS_WEIGHT_MULTIPLIER
        reliability_bonus = self.reliability_score * 0.5
        uptime_bonus = min(uptime_days / 365, 0.5)  # Max 0.5 bonus for 1 year
        
        total_weight = base_weight + reliability_bonus + uptime_bonus
        return min(total_weight, WITNESS_MAX_WEIGHT)
    
    def should_become_witness(self) -> bool:
        """Check if node qualifies for witness status"""
        return (self.get_uptime_days() >= WITNESS_THRESHOLD_DAYS and 
                self.reliability_score >= 0.8)
    
    def save_witness_data(self):
        """Save witness data to file"""
        with WITNESS_LOCK:
            data = {
                'node_id': self.node_id,
                'start_time': self.start_time,
                'blocks_validated': self.blocks_validated,
                'last_seen_block': self.last_seen_block,
                'witness_status': self.witness_status,
                'reliability_score': self.reliability_score
            }
            save_json(WITNESS_FILE, data)
    
    @classmethod
    def load_witness_data(cls):
        """Load witness data from file"""
        witness = cls()
        with WITNESS_LOCK:
            data = load_json(WITNESS_FILE, {})
            if data:
                witness.node_id = data.get('node_id', witness.node_id)
                witness.start_time = data.get('start_time', witness.start_time)
                witness.blocks_validated = data.get('blocks_validated', 0)
                witness.last_seen_block = data.get('last_seen_block', 0)
                witness.witness_status = data.get('witness_status', False)
                witness.reliability_score = data.get('reliability_score', 1.0)
        return witness

class AdaptiveConsensus:
    """Manage adaptive consensus intervals based on network conditions"""
    
    def __init__(self, analytics: ConsensusAnalytics):
        self.analytics = analytics
        self.current_interval = BASE_CONSENSUS_CHECK_INTERVAL
        self.last_adjustment = time.time()
        
    def get_consensus_interval(self) -> int:
        """Get current adaptive consensus interval"""
        # Adjust every 5 minutes
        if time.time() - self.last_adjustment > 300:
            self.adjust_interval()
            self.last_adjustment = time.time()
            
        return self.current_interval
    
    def adjust_interval(self):
        """Adjust consensus interval based on network conditions"""
        health_score = self.analytics.get_network_health_score()
        stability_score = self.analytics.get_stability_score()
        
        if health_score < 50 or stability_score < 0.5:
            # Network unstable - more aggressive checking
            self.current_interval = max(3, BASE_CONSENSUS_CHECK_INTERVAL // 2)
        elif health_score > 90 and stability_score > 0.95:
            # Network very stable - less aggressive checking
            self.current_interval = min(30, BASE_CONSENSUS_CHECK_INTERVAL * 2)
        else:
            # Normal conditions
            self.current_interval = BASE_CONSENSUS_CHECK_INTERVAL
        
        print(f"🔄 Consensus interval adjusted to {self.current_interval}s " + 
              f"(health: {health_score:.0f}, stability: {stability_score:.2f})")

        
        return {'valid': False, 'error': 'Invalid vanity address'}

# Part 3: Enhanced Merkle Tree and Validation Classes

class MerkleTree:
    """Bitcoin-style Merkle tree implementation"""
    
    @staticmethod
    def double_sha256(data: bytes) -> bytes:
        """Bitcoin uses double SHA256"""
        return hashlib.sha256(hashlib.sha256(data).digest()).digest()
    
    @staticmethod
    def calculate_merkle_root(transactions: List[Dict]) -> str:
        """Calculate Merkle root exactly like Bitcoin"""
        if not transactions:
            return '0' * 64
        
        # Convert transactions to hashes
        tx_hashes = []
        for tx in transactions:
            tx_bytes = json.dumps(tx, sort_keys=True).encode()
            tx_hash = MerkleTree.double_sha256(tx_bytes)
            tx_hashes.append(tx_hash)
        
        # If odd number of transactions, duplicate the last one
        if len(tx_hashes) % 2 == 1:
            tx_hashes.append(tx_hashes[-1])
        
        # Build tree bottom-up
        while len(tx_hashes) > 1:
            next_level = []
            for i in range(0, len(tx_hashes), 2):
                left = tx_hashes[i]
                right = tx_hashes[i + 1] if i + 1 < len(tx_hashes) else tx_hashes[i]
                combined = left + right
                parent_hash = MerkleTree.double_sha256(combined)
                next_level.append(parent_hash)
            
            # If odd number at this level, duplicate last hash
            if len(next_level) % 2 == 1 and len(next_level) > 1:
                next_level.append(next_level[-1])
            
            tx_hashes = next_level
        
        return tx_hashes[0].hex()

class DifficultyAdjustment:
    """Bitcoin-accurate difficulty adjustment"""
    
    @staticmethod
    def target_to_bits(target: int) -> int:
        """Convert target to compact bits format (nBits)"""
        if target == 0:
            return 0
        
        # Find the most significant byte
        size = (target.bit_length() + 7) // 8
        
        if size <= 3:
            compact = target << (8 * (3 - size))
        else:
            compact = target >> (8 * (size - 3))
        
        # The 0x00800000 bit denotes the sign
        if compact & 0x00800000:
            compact >>= 8
            size += 1
        
        return compact | (size << 24)
    
    @staticmethod
    def bits_to_target(bits: int) -> int:
        """Convert compact bits format to target"""
        size = bits >> 24
        word = bits & 0x007fffff
        
        if size <= 3:
            return word >> (8 * (3 - size))
        else:
            return word << (8 * (size - 3))
    
    @staticmethod
    def calculate_next_difficulty(blocks: List[Dict]) -> int:
        """Calculate next difficulty target using Bitcoin's algorithm with a ramp-up period"""

        block_height = len(blocks)

        # Gradual ramp for first 2016 blocks
        if block_height <= 100:
            return 0x1e0fff00  # Very easy (for bootstrapping)
        elif block_height <= 250:
            return 0x1e0ffff0  # Slightly harder
        elif block_height <= 500:
            return 0x1e0fff00
        elif block_height <= 1000:
            return 0x1e0ff000
        elif block_height <= 1500:
            return 0x1e0f0000
        elif block_height < 2016:
            return 0x1e00afff  # Bitcoin's original difficulty

        # 🔄 Full Bitcoin-style difficulty adjustment from block 2016 onward
        last_block = blocks[-1]
        first_block = blocks[-DIFFICULTY_ADJUSTMENT_INTERVAL]

        actual_time = last_block['timestamp'] - first_block['timestamp']
        target_time = DIFFICULTY_ADJUSTMENT_INTERVAL * TARGET_BLOCK_TIME

        current_bits = last_block.get('bits', MAX_TARGET)
        current_target = DifficultyAdjustment.bits_to_target(current_bits)

        # Calculate new target
        new_target = current_target * actual_time // target_time

        # Clamp the change to 4x easier or 4x harder
        new_target = max(current_target // 4, min(new_target, current_target * 4))

        # Cap at MAX_TARGET
        if new_target > DifficultyAdjustment.bits_to_target(MAX_TARGET):
            new_target = DifficultyAdjustment.bits_to_target(MAX_TARGET)

        return DifficultyAdjustment.target_to_bits(new_target)


class UTXOValidator:
    """Automatic UTXO validation and repair system"""
    
    @staticmethod
    def validate_utxo_consistency() -> bool:
        """Check if UTXO set matches blockchain state"""
        try:
            with UTXO_LOCK:
                utxos = load_json(UTXO_FILE, [])
            
            with BLOCKCHAIN_LOCK:
                blockchain = load_json(BLOCKCHAIN_FILE, [])
            
            if not blockchain:
                return True  # Empty blockchain is consistent
            
            # Calculate expected UTXO count vs actual
            expected_utxos = UTXOValidator.calculate_expected_utxos(blockchain)
            actual_utxos = len(utxos)
            
            # Allow small variance due to recent transactions
            variance_threshold = 10
            if abs(expected_utxos - actual_utxos) > variance_threshold:
                print(f"⚠️  UTXO inconsistency detected:")
                print(f"   Expected UTXOs: ~{expected_utxos}")
                print(f"   Actual UTXOs: {actual_utxos}")
                return False
            
            return True
            
        except Exception as e:
            print(f"❌ UTXO validation error: {e}")
            return False
    
    @staticmethod
    def calculate_expected_utxos(blockchain: List[Dict]) -> int:
        """Calculate expected UTXO count from blockchain"""
        try:
            utxo_count = 0
            spent_outputs = set()
            
            for block in blockchain:
                for tx in block.get('transactions', []):
                    # Track spent outputs from inputs
                    if 'inputs' in tx:
                        for inp in tx['inputs']:
                            # Skip coinbase inputs (they don't spend previous outputs)
                            if inp.get('txid', '') != '0' * 64:
                                spent_key = f"{inp.get('txid')}:{inp.get('index') if 'index' in inp else inp.get('vout', 0)}"
                                spent_outputs.add(spent_key)
                    
                    # Count all outputs (including both miner reward and genesis fee)
                    if 'outputs' in tx:
                        for idx, output in enumerate(tx['outputs']):
                            tx_string = json.dumps(tx, sort_keys=True)
                            tx_id = tx.get('txid') or double_sha256(tx_string)
                            output_key = f"{tx_id}:{idx}"
                            
                            # Only count if not spent
                            if output_key not in spent_outputs:
                                utxo_count += 1
            
            return utxo_count
        
        except Exception as e:
                print(f"Error calculating expected UTXOs: {e}")
        return 0
    
    @staticmethod
    def repair_utxo_set() -> bool:
        """Automatically repair corrupted UTXO set"""
        try:
            print("🔧 AUTO-REPAIRING UTXO set.")
            
            with BLOCKCHAIN_LOCK:
                blockchain = load_json(BLOCKCHAIN_FILE, [])
            
            print(f"🔄 Rebuilding UTXO set from {len(blockchain)} blocks.")
            
            # Use the rebuild function instead
            rebuild_utxo_set(blockchain)
            
            print("✅ UTXO auto-repair completed successfully")
            return True
            
        except Exception as e:
            print(f"❌ UTXO auto-repair failed: {e}")
            return False
                    

class ChainSwitchTracker:
    """Track chain switches to prevent rapid oscillation"""
    
    def __init__(self, dampening_period: int = 30):
        self.dampening_period = dampening_period
        self.switch_file = 'chain_switch_history.json'
        self.load_history()
    
    def load_history(self):
        """Load switch history from file"""
        self.history = load_json(self.switch_file, {
            'last_switch': 0,
            'last_height': 0,
            'switch_count': 0,
            'switches': []
        })
    
    def save_history(self):
        """Save switch history to file"""
        save_json(self.switch_file, self.history)
    
    def can_switch(self, current_height: int, new_height: int) -> tuple[bool, int]:
        """Check if we can switch chains and return required improvement"""
        time_since_switch = time.time() - self.history['last_switch']
        
        if time_since_switch < self.dampening_period:
            # During dampening, require more improvement
            required_improvement = MIN_IMPROVEMENT_DAMPENED
            can_switch = (new_height - current_height) >= required_improvement
            return can_switch, required_improvement
        else:
            # Normal operation
            required_improvement = MIN_IMPROVEMENT_NORMAL
            can_switch = (new_height - current_height) >= required_improvement
            return can_switch, required_improvement
    
    def record_switch(self, old_height: int, new_height: int):
        """Record a chain switch"""
        self.history['last_switch'] = time.time()
        self.history['last_height'] = new_height
        self.history['switch_count'] += 1
        
        # Keep last 100 switches for analysis
        self.history['switches'].append({
            'timestamp': time.time(),
            'from_height': old_height,
            'to_height': new_height,
            'improvement': new_height - old_height
        })
        
        if len(self.history['switches']) > 100:
            self.history['switches'] = self.history['switches'][-100:]
        
        self.save_history()
        print(f"📊 Chain switch recorded: {old_height} → {new_height} (improvement: {new_height - old_height})")


class ReorgProtection:
    """Protect against deep reorgs that exchanges hate"""
    
    MAX_REORG_DEPTH = 100  # Never reorg more than 100 blocks
    EXCHANGE_CONFIRMATION_DEPTH = 6  # Standard exchange requirement
    
    def __init__(self):
        self.reorg_history = []
        self.max_observed_reorg = 0
    
    def is_reorg_acceptable(self, current_chain: List[Dict], new_chain: List[Dict]) -> tuple[bool, str]:
        """Check if reorg is within acceptable bounds"""
        
        # Find common ancestor
        fork_point = self.find_common_ancestor(current_chain, new_chain)
        reorg_depth = len(current_chain) - fork_point - 1
        
        # Update max observed
        if reorg_depth > self.max_observed_reorg:
            self.max_observed_reorg = reorg_depth
        
        # Record reorg attempt
        self.reorg_history.append({
            'timestamp': time.time(),
            'depth': reorg_depth,
            'from_height': len(current_chain),
            'to_height': len(new_chain)
        })
        
        # Never allow extremely deep reorgs
        if reorg_depth > self.MAX_REORG_DEPTH:
            return False, f"Reorg too deep: {reorg_depth} blocks (max: {self.MAX_REORG_DEPTH})"
        
        # For deep-ish reorgs, require significant improvement
        if reorg_depth > self.EXCHANGE_CONFIRMATION_DEPTH:
            improvement = len(new_chain) - len(current_chain)
            required_improvement = max(6, reorg_depth // 10)  # 10% of reorg depth, minimum 6
            
            if improvement < required_improvement:
                return False, f"Deep reorg requires {required_improvement} block improvement, only {improvement} provided"
        
        # Check if this would invalidate exchange deposits
        if reorg_depth > self.EXCHANGE_CONFIRMATION_DEPTH:
            print(f"⚠️  WARNING: Reorg depth {reorg_depth} exceeds exchange confirmations!")
        
        return True, f"Reorg acceptable: depth {reorg_depth}, improvement {len(new_chain) - len(current_chain)}"
    
    def find_common_ancestor(self, chain1: List[Dict], chain2: List[Dict]) -> int:
        """Find the index of the last common block"""
        min_length = min(len(chain1), len(chain2))
        
        for i in range(min_length):
            if chain1[i]['hash'] != chain2[i]['hash']:
                return i - 1
        
        return min_length - 1
    
    def get_safe_confirmation_depth(self) -> int:
        """Get recommended confirmation depth based on network history"""
        if not self.reorg_history:
            return self.EXCHANGE_CONFIRMATION_DEPTH
        
        # Look at recent reorgs (last 24 hours)
        recent_reorgs = [r for r in self.reorg_history 
                        if time.time() - r['timestamp'] < 86400]
        
        if not recent_reorgs:
            return self.EXCHANGE_CONFIRMATION_DEPTH
        
        # Recommend confirmations based on largest recent reorg
        max_recent = max(r['depth'] for r in recent_reorgs)
        return max(self.EXCHANGE_CONFIRMATION_DEPTH, max_recent + 3)
    
class AttackPrevention:
    """Prevent common attacks that concern exchanges"""
    
    def __init__(self):
        self.block_release_times = {}  # Track when blocks were first seen
        self.peer_block_counts = {}    # Track blocks per peer
        self.connection_attempts = {}   # Track connection attempts per IP
        self.suspicious_peers = set()   # Blacklist for suspicious peers
        
    def detect_selfish_mining(self, peer_blocks: List[Dict], peer_ip: str) -> bool:
        """Detect potential selfish mining attacks"""
        
        if not peer_blocks or len(peer_blocks) < 2:
            return False
            
        # Track blocks from this peer
        if peer_ip not in self.peer_block_counts:
            self.peer_block_counts[peer_ip] = []
            
        # Look for suspicious patterns
        timestamps = [b['timestamp'] for b in peer_blocks[-20:]]
        current_time = time.time()
        
        # Check for blocks withheld then released in batches
        time_gaps = []
        for i in range(1, len(timestamps)):
            gap = timestamps[i] - timestamps[i-1]
            time_gaps.append(gap)
        
        # Suspicious if multiple blocks with very small gaps
        small_gaps = sum(1 for gap in time_gaps if gap < 30)  # Less than 30 seconds
        
        if small_gaps > 5:  # More than 5 blocks released rapidly
            print(f"⚠️  SELFISH MINING DETECTED from {peer_ip}: {small_gaps} blocks with <30s gaps")
            self.suspicious_peers.add(peer_ip)
            return True
            
        # Check if blocks are significantly older than they should be
        for i, block in enumerate(peer_blocks[-10:]):
            block_age = current_time - block['timestamp']
            expected_age = (len(peer_blocks) - len(peer_blocks[-10:]) + i) * TARGET_BLOCK_TIME
            
            if block_age > expected_age * 2:  # Block is twice as old as expected
                print(f"⚠️  OLD BLOCK DETECTED from {peer_ip}: Block age {block_age}s, expected ~{expected_age}s")
                return True
                
        return False
    
    def validate_block_timestamp(self, block: Dict, blockchain: List[Dict]) -> tuple[bool, str]:
        """Enhanced timestamp validation to prevent manipulation"""
        
        current_time = time.time()
        
        # Rule 1: Block can't be more than 2 hours in the future
        if block['timestamp'] > current_time + 7200:
            return False, f"Block timestamp {block['timestamp']} is >2 hours in future"
        
        # Rule 2: Block can't be too far in the past (24 hours)
        if block['timestamp'] < current_time - 86400:
            return False, f"Block timestamp {block['timestamp']} is >24 hours in past"
        
        # Rule 3: Must be greater than median of last 11 blocks
        if len(blockchain) >= 11:
            last_11_timestamps = sorted([b['timestamp'] for b in blockchain[-11:]])
            median_timestamp = last_11_timestamps[5]
            if block['timestamp'] <= median_timestamp:
                return False, f"Block timestamp {block['timestamp']} <= median {median_timestamp}"
        
        # Rule 4: Check for timestamp manipulation patterns
        if len(blockchain) >= 20:
            recent_timestamps = [b['timestamp'] for b in blockchain[-20:]]
            
            # Check if timestamps are artificially increasing
            perfect_increases = sum(1 for i in range(1, len(recent_timestamps)) 
                                  if recent_timestamps[i] - recent_timestamps[i-1] == TARGET_BLOCK_TIME)
            
            if perfect_increases > 15:  # Too many perfect intervals
                return False, "Suspicious timestamp pattern detected"
        
        return True, "Timestamp valid"
    
    def check_double_spend(self, transaction: Dict, blockchain: List[Dict], mempool: List[Dict]) -> bool:
        """Check if transaction attempts to double-spend"""
        
        spent_outputs = set()
        
        # Collect all spent outputs from blockchain
        for block in blockchain:
            for tx in block.get('transactions', []):
                if 'inputs' in tx:
                    for inp in tx['inputs']:
                        spent_outputs.add(f"{inp['txid']}:{inp['index']}")
        
        # Check mempool
        for tx in mempool:
            if 'inputs' in tx:
                for inp in tx['inputs']:
                    spent_outputs.add(f"{inp['txid']}:{inp['index']}")
        
        # Check current transaction
        if 'inputs' in transaction:
            for inp in transaction['inputs']:
                output_id = f"{inp['txid']}:{inp['index']}"
                if output_id in spent_outputs:
                    print(f"❌ DOUBLE SPEND DETECTED: Output {output_id} already spent")
                    return True
        
        return False
    
    def rate_limit_connection(self, peer_ip: str) -> bool:
        """Rate limit connections from peers"""
        
        current_time = time.time()
        
        # Clean old attempts
        self.connection_attempts = {
            ip: attempts for ip, attempts in self.connection_attempts.items()
            if any(t > current_time - 3600 for t in attempts)  # Keep last hour
        }
        
        # Check if peer is blacklisted
        if peer_ip in self.suspicious_peers:
            return False
        
        # Track this attempt
        if peer_ip not in self.connection_attempts:
            self.connection_attempts[peer_ip] = []
        
        self.connection_attempts[peer_ip].append(current_time)
        
        # Check rate limits
        attempts_last_minute = sum(1 for t in self.connection_attempts[peer_ip] 
                                 if t > current_time - 60)
        attempts_last_hour = len(self.connection_attempts[peer_ip])

        # Limits: 100 per minute, 1000 per hour
        if attempts_last_minute > 100:
            print(f"⚠️  RATE LIMIT: {peer_ip} exceeded minute limit ({attempts_last_minute}/10)")
            return False
        
        if attempts_last_hour > 1000:
            print(f"⚠️  RATE LIMIT: {peer_ip} exceeded hour limit ({attempts_last_hour}/100)")
            self.suspicious_peers.add(peer_ip)  # Blacklist repeat offenders
            return False
        
        return True
    
class GeographicTracker:
    """Track geographic distribution of peers"""
    
    def __init__(self):
        self.peer_locations = {}
        self.country_counts = {}
        self.last_update = 0
        
    def get_ip_location(self, ip: str) -> Dict:
        """Get geographic location for IP using ip-api.com (free tier)"""
        try:
            # Skip local IPs
            if ip in ['127.0.0.1', 'localhost', '0.0.0.0'] or ip.startswith('192.168.'):
                return {'country': 'Local', 'city': 'Local', 'lat': 0, 'lon': 0}
            
            # Cache check
            if ip in self.peer_locations:
                return self.peer_locations[ip]
            
            # Rate limit - only update every 5 minutes
            if time.time() - self.last_update < 300:
                return {}
            
            # Free API - no key required, 45 requests per minute limit
            response = requests.get(f'http://ip-api.com/json/{ip}', timeout=5)
            if response.status_code == 200:
                data = response.json()
                if data['status'] == 'success':
                    location = {
                        'country': data.get('country', 'Unknown'),
                        'countryCode': data.get('countryCode', 'XX'),
                        'city': data.get('city', 'Unknown'),
                        'lat': data.get('lat', 0),
                        'lon': data.get('lon', 0),
                        'isp': data.get('isp', 'Unknown')
                    }
                    self.peer_locations[ip] = location
                    self.last_update = time.time()
                    return location
            
        except Exception as e:
            print(f"GeoIP lookup failed for {ip}: {e}")
        
        return {'country': 'Unknown', 'city': 'Unknown', 'lat': 0, 'lon': 0}
    
    def update_peer_geography(self, peers: List[Tuple[str, int]]):
        """Update geographic distribution of peers"""
        self.country_counts = {}
        
        for ip, port in peers:
            location = self.get_ip_location(ip)
            if location:
                country = location.get('country', 'Unknown')
                self.country_counts[country] = self.country_counts.get(country, 0) + 1
    
    def get_geographic_distribution(self) -> Dict:
        """Get summary of geographic distribution"""
        total_peers = sum(self.country_counts.values())
        
        return {
            'total_countries': len(self.country_counts),
            'country_distribution': self.country_counts,
            'geographic_diversity_score': self.calculate_diversity_score(),
            'peer_locations': self.peer_locations,
            'total_peers': total_peers
        }
    
    def calculate_diversity_score(self) -> float:
        """Calculate geographic diversity score (0-100)"""
        if not self.country_counts:
            return 0
        
        total_peers = sum(self.country_counts.values())
        if total_peers == 0:
            return 0
        
        # Shannon diversity index
        diversity = 0
        for count in self.country_counts.values():
            if count > 0:
                proportion = count / total_peers
                diversity -= proportion * math.log(proportion)
        
        # Normalize to 0-100 scale
        # Max diversity with 50 countries equally distributed = ~3.9
        max_diversity = 3.9
        score = (diversity / max_diversity) * 100
        
        # Bonus for number of countries
        country_bonus = min(len(self.country_counts) * 2, 20)  # Max 20 point bonus
        
        return min(100, score + country_bonus)

class EmergencyResponseSystem:
    """Emergency response system for critical network events"""
    
    def __init__(self):
        self.emergency_contacts = []
        self.active_alerts = {}
        self.incident_log = []
        self.checkpoint_activated = False
        self.alert_file = 'emergency_alerts.json'
        self.incident_file = 'incident_log.json'
        self.load_state()
        
    def load_state(self):
        """Load emergency system state from files"""
        self.active_alerts = load_json(self.alert_file, {})
        self.incident_log = load_json(self.incident_file, [])
    
    def save_state(self):
        """Save emergency system state"""
        save_json(self.alert_file, self.active_alerts)
        save_json(self.incident_file, self.incident_log)
    
    def activate_checkpoint(self, block_height: int, block_hash: str, reason: str) -> bool:
        """Activate emergency checkpoint"""
        if self.checkpoint_activated:
            print("⚠️  Checkpoint already activated")
            return False
        
        # Verify the block exists
        blockchain = load_json(BLOCKCHAIN_FILE, [])
        if block_height >= len(blockchain):
            print(f"❌ Cannot checkpoint future block {block_height}")
            return False
        
        if blockchain[block_height]['hash'] != block_hash:
            print(f"❌ Block hash mismatch at height {block_height}")
            return False
        
        # Activate checkpoint
        CHECKPOINTS[block_height] = block_hash
        self.checkpoint_activated = True
        
        # Log incident
        incident = {
            'type': 'CHECKPOINT_ACTIVATION',
            'timestamp': time.time(),
            'block_height': block_height,
            'block_hash': block_hash,
            'reason': reason
        }
        self.incident_log.append(incident)
        self.save_state()
        
        # Broadcast to network
        self.broadcast_emergency_checkpoint(block_height, block_hash, reason)
        
        print(f"🚨 EMERGENCY CHECKPOINT ACTIVATED at height {block_height}")
        print(f"📍 Hash: {block_hash}")
        print(f"📝 Reason: {reason}")
        
        return True
    
    def broadcast_alert(self, alert_level: str, message: str, action_required: str = None):
        """Broadcast emergency alert to all nodes"""
        alert_id = hashlib.sha256(f"{time.time()}{message}".encode()).hexdigest()[:16]
        
        alert = {
            'id': alert_id,
            'level': alert_level,  # CRITICAL, HIGH, MEDIUM, LOW
            'message': message,
            'action_required': action_required,
            'timestamp': time.time(),
            'expires': time.time() + 86400  # 24 hour expiry
        }
        
        self.active_alerts[alert_id] = alert
        self.save_state()
        
        # Log incident
        self.incident_log.append({
            'type': 'ALERT_BROADCAST',
            'timestamp': time.time(),
            'alert_id': alert_id,
            'level': alert_level,
            'message': message
        })
        
        # Broadcast to peers
        peers = load_json(PEERS_FILE, [])
        broadcast_count = 0
        
        for ip, port in peers[:50]:  # Limit to 50 peers
            if self.send_emergency_alert(ip, port, alert):
                broadcast_count += 1
        
        print(f"🚨 EMERGENCY ALERT: {message}")
        print(f"📡 Broadcast to {broadcast_count} peers")
        
        return alert_id
    
    def send_emergency_alert(self, ip: str, port: int, alert: Dict) -> bool:
        """Send emergency alert to specific peer"""
        try:
            sock = create_safe_connection(ip, port, timeout=5)
            if not sock:
                return False
            
            message = {
                'type': 'emergency_alert',
                'data': alert
            }
            
            sock.sendall(json.dumps(message).encode())
            sock.close()
            return True
            
        except Exception as e:
            return False
    
    def broadcast_emergency_checkpoint(self, height: int, hash: str, reason: str):
        """Broadcast checkpoint to all peers"""
        checkpoint_msg = {
            'type': 'emergency_checkpoint',
            'data': {
                'height': height,
                'hash': hash,
                'reason': reason,
                'timestamp': time.time()
            }
        }
        
        peers = load_json(PEERS_FILE, [])
        for ip, port in peers[:50]:
            try:
                sock = create_safe_connection(ip, port, timeout=5)
                if sock:
                    sock.sendall(json.dumps(checkpoint_msg).encode())
                    sock.close()
            except:
                pass
    
    def check_emergency_conditions(self) -> List[str]:
        """Check for conditions requiring emergency response"""
        warnings = []
        
        # Check for deep reorgs
        if hasattr(reorg_protection, 'max_observed_reorg'):
            if reorg_protection.max_observed_reorg > 10:
                warnings.append(f"Deep reorg detected: {reorg_protection.max_observed_reorg} blocks")
        
        # Check for selfish mining
        if hasattr(attack_prevention, 'suspicious_peers'):
            if len(attack_prevention.suspicious_peers) > 5:
                warnings.append(f"Multiple suspicious peers detected: {len(attack_prevention.suspicious_peers)}")
        
        # Check for timestamp attacks
        blockchain = load_json(BLOCKCHAIN_FILE, [])
        if len(blockchain) >= 20:
            recent_timestamps = [b['timestamp'] for b in blockchain[-20:]]
            time_diffs = [recent_timestamps[i] - recent_timestamps[i-1] for i in range(1, len(recent_timestamps))]
            
            if min(time_diffs) < 1:  # Blocks less than 1 second apart
                warnings.append("Timestamp manipulation detected")
            
            if max(time_diffs) > 3600:  # Gap over 1 hour
                warnings.append("Network stall detected")
        
        # Check consensus health
        if hasattr(consensus_analytics, 'get_network_health_score'):
            health_score = consensus_analytics.get_network_health_score()
            if health_score < 50:
                warnings.append(f"Low network health score: {health_score}")
        
        return warnings
    
    def log_incident(self, incident_type: str, details: Dict):
        """Log security incident"""
        incident = {
            'id': hashlib.sha256(f"{time.time()}{incident_type}".encode()).hexdigest()[:16],
            'type': incident_type,
            'timestamp': time.time(),
            'details': details
        }
        
        self.incident_log.append(incident)
        self.save_state()
        
        # Auto-alert for critical incidents
        if incident_type in ['DOUBLE_SPEND_ATTEMPT', '51_PERCENT_ATTACK', 'CONSENSUS_FAILURE']:
            self.broadcast_alert('CRITICAL', f"{incident_type}: {details.get('description', 'Check logs')}")
        
        return incident['id']
    
    def get_incident_report(self, last_hours: int = 24) -> Dict:
        """Generate incident report"""
        cutoff_time = time.time() - (last_hours * 3600)
        recent_incidents = [i for i in self.incident_log if i['timestamp'] > cutoff_time]
        
        # Group by type
        by_type = {}
        for incident in recent_incidents:
            incident_type = incident['type']
            if incident_type not in by_type:
                by_type[incident_type] = []
            by_type[incident_type].append(incident)
        
        return {
            'period_hours': last_hours,
            'total_incidents': len(recent_incidents),
            'incidents_by_type': {k: len(v) for k, v in by_type.items()},
            'active_alerts': len(self.active_alerts),
            'checkpoint_active': self.checkpoint_activated,
            'recent_incidents': recent_incidents[-10:]  # Last 10
        }

def is_peer_blacklisted(ip: str) -> bool:
    """Check if peer is blacklisted"""
    return ip in attack_prevention.suspicious_peers

def blacklist_peer(ip: str, reason: str):
    """Add peer to blacklist"""
    attack_prevention.suspicious_peers.add(ip)
    print(f"🚫 Blacklisted peer {ip}: {reason}")
    
    # Remove from peer list
    with PEERS_LOCK:
        peers = load_json(PEERS_FILE, [])
        peers = [(p_ip, p_port) for p_ip, p_port in peers if p_ip != ip]
        save_json(PEERS_FILE, peers)

def get_blacklist_stats() -> Dict:
    """Get blacklist statistics"""
    return {
        'blacklisted_count': len(attack_prevention.suspicious_peers),
        'blacklisted_ips': list(attack_prevention.suspicious_peers),
        'connection_attempts': {
            ip: len(attempts) 
            for ip, attempts in attack_prevention.connection_attempts.items()
        }
    }

def validate_block(block: dict, previous_block: dict) -> bool:
    """Validate a single block against its predecessor"""
    # Check index
    if block['index'] != previous_block['index'] + 1:
        return False
    
    # Check previous hash
    if block['previous_hash'] != previous_block['hash']:
        return False
    
    # Check timestamp is greater than previous
    if block['timestamp'] <= previous_block['timestamp']:
        return False
    
    # NEW: Validate timestamp against median time
    blockchain = load_json(BLOCKCHAIN_FILE, [])
    if blockchain and not validate_timestamp(block, blockchain):
        return False
    
    # Check block hash
    calculated_hash = calculate_block_hash(block)
    if block['hash'] != calculated_hash:
        return False
    
    # Check proof of work
    if not block['hash'].startswith('0' * get_required_zeros(block['index'])):
        return False
    
    return True
    
    return True

def validate_timestamp(block: Dict, previous_blocks: List[Dict]) -> bool:
    """Prevent timestamp manipulation attacks"""
    
    current_time = time.time()
    
    # Block timestamp can't be too far in future (2 hours like Bitcoin)
    if block['timestamp'] > current_time + 7200:
        print(f"❌ Block timestamp too far in future: {block['timestamp']} > {current_time + 7200}")
        return False
    
    # Block timestamp must be greater than median of last 11 blocks
    if len(previous_blocks) >= 11:
        last_11_timestamps = [b['timestamp'] for b in previous_blocks[-11:]]
        median_timestamp = sorted(last_11_timestamps)[5]
        if block['timestamp'] <= median_timestamp:
            print(f"❌ Block timestamp {block['timestamp']} <= median {median_timestamp}")
            return False
    
    return True

def calculate_block_hash(block: dict) -> str:
    """Calculate the hash of a block"""
    block_copy = block.copy()
    block_copy.pop('hash', None)  # Remove hash field if present
    
    # Create string in deterministic order
    block_string = json.dumps(block_copy, sort_keys=True)
    return hashlib.sha256(block_string.encode()).hexdigest()

def get_required_zeros(block_height: int) -> int:
    """Get the number of leading zeros required for a block at given height"""
    # This should match your difficulty adjustment logic
    # For now, returning a simple calculation
    base_zeros = 4
    # Add more zeros every 10000 blocks (simplified)
    additional_zeros = block_height // 10000
    return min(base_zeros + additional_zeros, 6)  # Cap at 6 zeros

def calculate_chain_work(chain: List[Dict]) -> int:
    """Calculate total proof of work for a chain"""
    if not chain:
        return 0
    
    total_work = 0
    for block in chain:
        # Count leading zeros as proxy for work
        zeros = len(block['hash']) - len(block['hash'].lstrip('0'))
        # Each additional zero represents 16x more work
        total_work += 16 ** zeros
    
    return total_work

def check_exchange_readiness() -> Dict[str, any]:
        """Check if network meets exchange listing requirements"""
        blockchain = load_json(BLOCKCHAIN_FILE, [])
        peers = load_json(PEERS_FILE, [])
        
        requirements = {
            'min_height': 10000,
            'min_peers': 50,
            'max_reorg_depth': 6,
            'min_hashrate': 1e6,
            'stable_block_time': True
        }
        
        status = {
            'ready': False,
            'height': len(blockchain),
            'peers': len(peers),
            'max_reorg': reorg_protection.max_observed_reorg,
            'safe_confirmations': reorg_protection.get_safe_confirmation_depth(),
            'checks': {}
        }
        
        # Check each requirement
        status['checks']['height'] = status['height'] >= requirements['min_height']
        status['checks']['peers'] = status['peers'] >= requirements['min_peers']
        status['checks']['reorg'] = status['max_reorg'] <= requirements['max_reorg_depth']

        geo_stats = geographic_tracker.get_geographic_distribution()
        status['checks']['geographic_diversity'] = geo_stats['total_countries'] >= 5
        status['geographic_distribution'] = geo_stats
        
        # Check block time stability
        if len(blockchain) >= 144:  # Last 24 hours
            recent_blocks = blockchain[-144:]
            block_times = []
            for i in range(1, len(recent_blocks)):
                block_times.append(recent_blocks[i]['timestamp'] - recent_blocks[i-1]['timestamp'])
            avg_block_time = sum(block_times) / len(block_times)
            status['checks']['block_time'] = abs(avg_block_time - TARGET_BLOCK_TIME) < TARGET_BLOCK_TIME * 0.2
        else:
            status['checks']['block_time'] = False
        
        # Overall readiness
        status['ready'] = all(status['checks'].values())
        
        return status

def enhanced_startup_validation():
    """Comprehensive startup validation with auto-repair"""
    print("🔍 Starting up with UTXO validation...")
    
    if not UTXOValidator.validate_utxo_consistency():
        print("⚠️  UTXO corruption detected - auto-repairing...")
        
        if UTXOValidator.repair_utxo_set():
            print("✅ UTXO auto-repair successful")
            if UTXOValidator.validate_utxo_consistency():
                print("✅ UTXO validation passed after repair")
            else:
                print("❌ UTXO still inconsistent after repair")
                return False
        else:
            print("❌ UTXO auto-repair failed")
            return False
    else:
        print("✅ UTXO validation passed")
    
    return True

class CypherMintValidator:
    """CypherMint consensus rule validation"""
    
    @staticmethod
    def validate_block_header(new_block: Dict, previous_block: Dict) -> bool:
        """Validate block header according to CypherMint rules"""
        try:
            # Check block index sequencing
            if new_block['index'] != previous_block['index'] + 1:
                print(f"❌ Block index mismatch: expected {previous_block['index'] + 1}, got {new_block['index']}")
                return False
            
            # Check previous hash linkage
            if new_block['previous_hash'] != previous_block['hash']:
                print(f"❌ Previous hash mismatch")
                print(f"   Expected: {previous_block['hash']}")
                print(f"   Got: {new_block['previous_hash']}")
                return False
            
            # Check proof of work
            if 'bits' in new_block:
                target = DifficultyAdjustment.bits_to_target(new_block['bits'])
                block_hash_int = int(new_block['hash'], 16)
                if block_hash_int >= target:
                    print(f"❌ Proof of work insufficient")
                    print(f"   Hash: {new_block['hash']}")
                    print(f"   Target: {hex(target)}")
                    return False
            
            # Check timestamp (must be greater than previous)
            if new_block['timestamp'] < previous_block['timestamp']:
                print(f"❌ Timestamp regression: {new_block['timestamp']} < {previous_block['timestamp']}")
                return False
            
            # Validate merkle root if present
            if 'merkle_root' in new_block and 'transactions' in new_block:
                calculated_merkle = MerkleTree.calculate_merkle_root(new_block['transactions'])
                if calculated_merkle != new_block['merkle_root']:
                    print(f"❌ Merkle root mismatch")
                    print(f"   Expected: {calculated_merkle}")
                    print(f"   Got: {new_block['merkle_root']}")
                    return False
            
            # Validate block hash
            calculated_hash = calculate_block_hash(new_block)
            if calculated_hash != new_block['hash']:
                print(f"❌ Block hash mismatch")
                print(f"   Expected: {calculated_hash}")
                print(f"   Got: {new_block['hash']}")
                return False
            
            # Validate checkpoint if applicable
            if not validate_checkpoint(new_block):
                print(f"❌ Checkpoint validation failed for block {new_block['index']}")
                return False
            
            print(f"✅ Block {new_block['index']} validation passed")
            return True
            
        except Exception as e:
            print(f"❌ Block validation error: {e}")
            return False
    
    @staticmethod
    def validate_transaction(transaction: Dict, utxos: List[Dict]) -> tuple[bool, str]:
        """Comprehensive transaction validation with double-spend protection"""
        try:
            # ADD THIS: Check for double-spend first
            blockchain = load_json(BLOCKCHAIN_FILE, [])
            mempool = load_json(MEMPOOL_FILE, [])
            if attack_prevention.check_double_spend(transaction, blockchain, mempool):
                return False, "Double spend detected"
            
            # Check transaction structure
            if 'inputs' not in transaction or 'outputs' not in transaction:
                return False, "Transaction missing inputs or outputs"
            
            # Coinbase transactions (no inputs)
            if len(transaction['inputs']) == 0:
                # Must be first transaction in block
                return True, "Valid coinbase transaction"
            
            # Calculate input amount
            input_amount = 0
            spent_utxos = []
            
            for inp in transaction['inputs']:
                # Find the UTXO being spent
                utxo_found = False
                for utxo in utxos:
                    if utxo['txid'] == inp['txid'] and utxo['index'] == inp['index']:
                        # Verify ownership (simplified - real Bitcoin uses script verification)
                        if 'signature' not in inp or 'public_key' not in inp:
                            return False, f"Input missing signature or public key"
                        
                        # Verify the signature
                        if not CypherMintValidator.verify_input_signature(transaction, inp, utxo):
                            return False, f"Invalid signature for input {inp['txid']}:{inp['index']}"
                        
                        input_amount += utxo['amount']
                        spent_utxos.append(utxo)
                        utxo_found = True
                        break
                
                if not utxo_found:
                    return False, f"UTXO not found for input {inp['txid']}:{inp.get('index', inp.get('vout', 0))}"
            
            # Calculate output amount
            output_amount = sum(out['amount'] for out in transaction['outputs'])
            
            # Verify amounts (inputs >= outputs, difference is fee)
            if input_amount < output_amount:
                return False, f"Insufficient inputs: {input_amount} < {output_amount}"
            
            # Check for duplicate inputs within transaction
            input_refs = [f"{inp['txid']}:{inp['index']}" for inp in transaction['inputs']]
            if len(input_refs) != len(set(input_refs)):
                return False, "Transaction contains duplicate inputs"
            
            # Verify each output has valid amount
            for out in transaction['outputs']:
                if out['amount'] <= 0:
                    return False, f"Invalid output amount: {out['amount']}"
                if 'address' not in out:
                    return False, "Output missing address"
            
            # Transaction is valid
            fee = input_amount - output_amount
            return True, f"Valid transaction with fee: {fee}"
            
        except Exception as e:
            return False, f"Transaction validation error: {str(e)}"

        
    @staticmethod
    def validate_transactions_unique(new_block: Dict, existing_chain: List[Dict]) -> bool:
        """DOUBLE-SPEND FIX: Ensure no transaction ID appears twice in the blockchain"""
        try:
            existing_txids = set()
            
            # Collect all existing TX IDs from the blockchain
            for block in existing_chain:
                for tx in block.get('transactions', []):
                    tx_data = json.dumps(tx, sort_keys=True)
                    txid = double_sha256(tx_data)
                    existing_txids.add(txid)
            
            # Check new block for duplicate transactions
            new_block_txids = set()  # Track TXs in this block
            for tx in new_block.get('transactions', []):
                tx_data = json.dumps(tx, sort_keys=True)
                txid = double_sha256(tx_data)
                
                # Check against existing blockchain
                if txid in existing_txids:
                    print(f"❌ DOUBLE-SPEND DETECTED: Transaction {txid[:16]}... already exists in blockchain")
                    return False
                
                # Check against transactions already processed in this block
                if txid in new_block_txids:
                    print(f"❌ DUPLICATE TRANSACTION in same block: {txid[:16]}...")
                    return False
                    
                new_block_txids.add(txid)  # Add to this block's set
            
            return True
            
        except Exception as e:
            print(f"❌ Transaction uniqueness validation error: {e}")
            return False

# Configuration - set this to current height when deploying the fix
DUPLICATE_CLEANUP_HEIGHT = 150  # Blocks after this height must be duplicate-free

class ProductionValidator:
    """Enhanced validation for production deployment"""
    
    @staticmethod
    def validate_block_production(new_block: Dict, existing_chain: List[Dict]) -> bool:
        """Production-grade block validation with legacy support"""
        
        # Basic block validation first
        if not CypherMintValidator.validate_block_header(new_block, existing_chain[-1]):
            return False
        

        
        # Duplicate transaction handling based on block height
        if new_block['index'] > DUPLICATE_CLEANUP_HEIGHT:
            # NEW BLOCKS: Strict duplicate prevention
            return ProductionValidator.strict_duplicate_validation(new_block, existing_chain)
        else:
            # LEGACY BLOCKS: Accept historical duplicates for compatibility
            return ProductionValidator.legacy_validation(new_block, existing_chain)
    
    @staticmethod
    def strict_duplicate_validation(new_block: Dict, existing_chain: List[Dict]) -> bool:
        """Strict validation for new blocks - NO duplicates allowed"""
        try:
            all_existing_txids = set()
            
            # Collect ALL transaction IDs from entire blockchain
            for block in existing_chain:
                for tx in block.get('transactions', []):
                    # Skip coinbase transactions
                    if not (len(tx.get('inputs', [])) == 1 and tx['inputs'][0].get('txid', '') == '0' * 64):
                        tx_data = json.dumps(tx, sort_keys=True)
                        txid = double_sha256(tx_data)
                        all_existing_txids.add(txid)
            
            # Check new block for ANY duplicates
            new_block_txids = set()
            for tx in new_block.get('transactions', []):
                # Skip coinbase transactions
                if len(tx.get('inputs', [])) == 1 and tx['inputs'][0].get('txid', '') == '0' * 64:
                    continue
                    
                tx_data = json.dumps(tx, sort_keys=True)
                txid = double_sha256(tx_data)
                
                # Check against entire blockchain history
                if txid in all_existing_txids:
                    print(f"❌ PRODUCTION VALIDATION: Transaction {txid[:16]}... already exists in blockchain")
                    return False
                
                # Check against other transactions in this block
                if txid in new_block_txids:
                    print(f"❌ PRODUCTION VALIDATION: Duplicate transaction {txid[:16]}... in same block")
                    return False
                
                new_block_txids.add(txid)
            
            return True
            
        except Exception as e:
            print(f"❌ Production validation error: {e}")
            return False
    
    @staticmethod
    def legacy_validation(new_block: Dict, existing_chain: List[Dict]) -> bool:
        """Legacy validation - basic checks only, allows historical duplicates"""
        try:
            # Only validate block structure and proof of work
            # Don't check for duplicate transactions in legacy blocks
            
            # Validate merkle root
            if 'merkle_root' in new_block and 'transactions' in new_block:
                calculated_merkle = MerkleTree.calculate_merkle_root(new_block['transactions'])
                if calculated_merkle != new_block['merkle_root']:
                    print(f"❌ Legacy validation: Merkle root mismatch")
                    return False
            
            # Basic reward validation
            if new_block.get('transactions'):
                coinbase = new_block['transactions'][0]
                expected_reward = get_block_reward(new_block['index'])
                actual_reward = sum(out.get('amount', 0) for out in coinbase.get('outputs', []))
                
                if actual_reward > expected_reward * 1.1:  # Allow 10% variance for fees
                    print(f"❌ Legacy validation: Excessive reward")
                    return False
            
            return True
            
        except Exception as e:
            print(f"❌ Legacy validation error: {e}")
            return False

# Add to cyphermint.py

class BlockHeader:
    """Lightweight block header for fast sync"""
    @staticmethod
    def extract_header(block: Dict) -> Dict:
        """Extract just the header from a full block"""
        return {
            'version': block.get('version', 1),
            'index': block['index'],
            'timestamp': block['timestamp'],
            'previous_hash': block['previous_hash'],
            'merkle_root': block['merkle_root'],
            'bits': block['bits'],
            'nonce': block['nonce'],
            'hash': block['hash']
        }
    
    @staticmethod
    def validate_header_chain(headers: List[Dict]) -> bool:
        """Validate a chain of headers (much faster than full validation)"""
        if not headers:
            return False
            
        # Check genesis
        if headers[0]['index'] != 0 or headers[0]['previous_hash'] != '0' * 64:
            return False
            
        # Validate each header
        for i in range(1, len(headers)):
            curr = headers[i]
            prev = headers[i-1]
            
            # Check sequence
            if curr['index'] != prev['index'] + 1:
                return False
                
            # Check previous hash link
            if curr['previous_hash'] != prev['hash']:
                return False
                
            # Verify PoW
            target = DifficultyAdjustment.bits_to_target(curr['bits'])
            if int(curr['hash'], 16) >= target:
                return False
                
        return True

def sync_headers_first(peer_ip: str, peer_port: int) -> Optional[List[Dict]]:
    """Download headers first, then full blocks"""
    try:
        sock = create_safe_connection(peer_ip, peer_port, timeout=30)
        if not sock:
            return None
            
        # Step 1: Get all headers
        print(f"📊 Downloading headers from {peer_ip}...")
        request = {'type': 'get_headers', 'data': {'start_height': 0}}
        sock.sendall(json.dumps(request).encode())
        
        # Receive headers (much smaller than full blocks)
        chunks = []
        sock.settimeout(60)
        while True:
            try:
                chunk = sock.recv(BUFFER_SIZE)
                if not chunk:
                    break
                chunks.append(chunk)
            except socket.timeout:
                break
                
        if not chunks:
            return None
            
        data = b''.join(chunks)
        response = json.loads(data.decode())
        
        if response.get('type') != 'headers_response':
            return None
            
        headers = response.get('data', [])
        print(f"📊 Received {len(headers)} headers")
        
        # Step 2: Validate headers chain
        if not BlockHeader.validate_header_chain(headers):
            print("❌ Invalid header chain")
            return None
            
        # Step 3: Download full blocks in chunks (simple sequential for now)
        blockchain = []
        chunk_size = 250
        
        for i in range(0, len(headers), chunk_size):
            end = min(i + chunk_size, len(headers))
            print(f"📦 Downloading blocks {i}-{end}...")
            
            request = {
                'type': 'get_blocks_range',
                'data': {'start': i, 'end': end}
            }
            sock.sendall(json.dumps(request).encode())
            
            chunks = []
            sock.settimeout(30)
            while True:
                try:
                    chunk = sock.recv(BUFFER_SIZE)
                    if not chunk:
                        break
                    chunks.append(chunk)
                except socket.timeout:
                    break
                    
            if chunks:
                block_data = b''.join(chunks)
                block_response = json.loads(block_data.decode())
                if block_response.get('type') == 'blocks_range':
                    blocks = block_response.get('data', [])
                    blockchain.extend(blocks)
                    
            time.sleep(0.1)  # Small delay between chunks
        
        sock.close()
        
        # Verify we got all blocks
        if len(blockchain) == len(headers):
            print(f"✅ Successfully downloaded {len(blockchain)} blocks")
            return blockchain
        else:
            print(f"❌ Block download incomplete: {len(blockchain)}/{len(headers)}")
            return None
        
    except Exception as e:
        print(f"Header sync error: {e}")
        return None
    finally:
        if sock:
            try:
                sock.close()
            except:
                pass

class ConsensusHealing:
    """Automatic consensus healing for production networks"""
    
    @staticmethod
    def find_cleanest_chain(peer_chains: List[List[Dict]]) -> Optional[List[Dict]]:
        """Find the chain with fewest duplicates among peers"""
        
        if not peer_chains:
            return None
        
        chain_scores = []
        
        for chain in peer_chains:
            duplicate_count = ConsensusHealing.count_duplicates(chain)
            score = {
                'chain': chain,
                'height': len(chain),
                'duplicates': duplicate_count,
                'work': calculate_chain_work(chain)
            }
            chain_scores.append(score)
        
        # Sort by: 1) Fewest duplicates, 2) Highest work, 3) Longest chain
        chain_scores.sort(key=lambda x: (x['duplicates'], -x['work'], -x['height']))
        
        best_chain = chain_scores[0]
        print(f"🔍 Cleanest chain found: height {best_chain['height']}, duplicates {best_chain['duplicates']}")
        
        return best_chain['chain']
    
    @staticmethod
    def count_duplicates(chain: List[Dict]) -> int:
        """Count duplicate transactions in a blockchain"""
        tx_counts = {}
        duplicates = 0
        
        for block in chain:
            for tx in block.get('transactions', []):
                # Skip coinbase transactions
                if len(tx.get('inputs', [])) == 1 and tx['inputs'][0].get('txid', '') == '0' * 64:
                    continue
                    
                tx_data = json.dumps(tx, sort_keys=True)
                txid = double_sha256(tx_data)
                
                if txid in tx_counts:
                    duplicates += 1
                else:
                    tx_counts[txid] = 1
        
        return duplicates
    
    @staticmethod
    def production_consensus_healing(peers: List[Tuple[str, int]]) -> List[Dict]:
        """Production consensus with automatic healing"""
        
        # Download chains from multiple peers, skipping our own address
        peer_chains = []
        count = 0
        for ip, port in peers:
            if count >= 5:
                break
            if is_self_peer(ip):
                continue
            try:
                chain = ConsensusHealing.download_peer_chain(ip, port)
                if chain and len(chain) > 0:
                    peer_chains.append(chain)
                    count += 1
            except Exception as e:
                print(f"Failed to download chain from {ip}:{port}: {e}")
        
        if not peer_chains:
            print("No peer chains available for healing")
            return load_json(BLOCKCHAIN_FILE, [])
        
        # Find the cleanest chain
        cleanest_chain = ConsensusHealing.find_cleanest_chain(peer_chains)
        
        if cleanest_chain:
            current_chain = load_json(BLOCKCHAIN_FILE, [])
            current_duplicates = ConsensusHealing.count_duplicates(current_chain)
            cleanest_duplicates = ConsensusHealing.count_duplicates(cleanest_chain)
            
            # Adopt cleanest chain if it's better
            if (len(cleanest_chain) >= len(current_chain) and 
                cleanest_duplicates <= current_duplicates):
                print(f"🔄 Adopting cleaner chain: {cleanest_duplicates} vs {current_duplicates} duplicates")
                return cleanest_chain
        
        return load_json(BLOCKCHAIN_FILE, [])
    
    @staticmethod
    def download_peer_chain(ip: str, port: int) -> Optional[List[Dict]]:
        """Download blockchain with proper connection handling"""
        try:
            sock = create_safe_connection(ip, port, timeout=300)  # Long timeout
            if not sock:
                return None
            
            request = {'type': 'get_chain'}
            sock.sendall(json.dumps(request).encode())
            
            # Read size first
            size_data = sock.recv(4)
            if not size_data or len(size_data) < 4:
                print(f"❌ No size header from {ip}:{port}")
                return None
                
            expected_size = struct.unpack('!I', size_data)[0]
            print(f"📊 Expecting {expected_size} bytes from {ip}:{port}")
            
            # Read exact amount
            chunks = []
            received = 0
            
            while received < expected_size:
                chunk_size = min(65536, expected_size - received)
                chunk = sock.recv(chunk_size)
                if not chunk:
                    break
                chunks.append(chunk)
                received += len(chunk)
                
                if received % (1024 * 1024) == 0:  # Progress every MB
                    print(f"📥 Downloaded {received}/{expected_size} bytes...")
            
            if received == expected_size:
                # Send ACK
                sock.sendall(b'ACK')
                
                data = b''.join(chunks)
                message = json.loads(data.decode())
                
                if message.get('type') == 'full_chain':
                    peer_chain = message.get('data', [])
                    print(f"✅ Successfully downloaded {len(peer_chain)} blocks from {ip}")
                    return peer_chain
            else:
                print(f"❌ Size mismatch: got {received}, expected {expected_size}")
                
            return None
            
        except Exception as e:
            print(f"Error downloading chain from {ip}:{port}: {e}")
            return None
        finally:
            try:
                sock.close()
            except:
                pass
        
# Integration Functions
def enhanced_validate_and_add_block(new_block: Dict, current_chain: List[Dict]) -> bool:
    """Enhanced block validation using production validator with witness weights"""
    try:
        if not current_chain:
            return False
            
        expected_index = len(current_chain)
        
        if new_block['index'] == expected_index:
    # Use production validation
            if ProductionValidator.validate_block_production(new_block, current_chain):
                with BLOCKCHAIN_LOCK:
                    fresh_chain = load_json(BLOCKCHAIN_FILE, [])
                    if len(fresh_chain) == expected_index:
                        fresh_chain.append(new_block)
                        save_json(BLOCKCHAIN_FILE, fresh_chain)
                        
                        with UTXO_LOCK:
                            safe_update_utxos(new_block)
                    
                        # Update witness node validation count
                        witness_node.update_validation_count(new_block['index'])
                        witness_node.save_witness_data()
                    
                        # Update checkpoint if this is a checkpoint block
                        update_checkpoint(new_block)
                        
                        # CRITICAL FIX: Remove confirmed transactions from mempool
                        mempool = load_json(MEMPOOL_FILE, [])
                        confirmed_tx_ids = set()
                        
                        # Get all transaction IDs from the accepted block
                        for tx in new_block.get('transactions', []):
                            tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                            confirmed_tx_ids.add(tx_id)
                        
                        # Remove confirmed transactions from mempool
                        remaining_mempool = []
                        for mem_tx in mempool:
                            mem_tx_id = mem_tx.get('txid') or double_sha256(json.dumps(mem_tx, sort_keys=True))
                            if mem_tx_id not in confirmed_tx_ids:
                                remaining_mempool.append(mem_tx)
                        
                        save_json(MEMPOOL_FILE, remaining_mempool)
                        print(f"🧹 Removed {len(mempool) - len(remaining_mempool)} confirmed transactions from mempool")
                    
                        print(f"✅ Block {new_block['index']} validated and added (production rules)")
                        return True

            else:
                print(f"❌ Block {new_block['index']} failed production validation")
                return False
       
        return False
       
    except Exception as e:
        print(f"❌ Enhanced block validation error: {e}")
        return False

def production_consensus_with_healing(peers: List[Tuple[str, int]], is_seed: bool = False) -> List[Dict]:
   """Production consensus with automatic healing and witness weights"""
   
   # Try normal consensus first
   try:
       consensus_chain = enhanced_consensus_check(peers, is_seed)
       current_chain = load_json(BLOCKCHAIN_FILE, [])
       
       if consensus_chain and len(consensus_chain) > len(current_chain):
           return consensus_chain
   except Exception as e:
       print(f"Normal consensus failed: {e}")
   
   # Fall back to healing consensus
   print("🔄 Attempting consensus healing...")
   return ConsensusHealing.production_consensus_healing(peers)

# Enhanced Connection Management
def create_safe_connection(ip: str, port: int, timeout: int = CONNECTION_TIMEOUT) -> Optional[socket.socket]:
   """Create a safe connection with proper error handling and connection pooling"""
   if is_self_peer(ip):
       print(f"🚫 Skipping self-peer connection: {ip}:{port}")
       return None

   connection_key = f"{ip}:{port}"
   
   try:
       with CONNECTION_POOL_LOCK:
           # Check per-peer connection limit
           current_count = ACTIVE_CONNECTIONS.get(connection_key, 0)
           
           if current_count >= CONNECTIONS_PER_PEER:
               print(f"🚫 Per-peer limit reached for {connection_key} ({current_count}/{CONNECTIONS_PER_PEER})")
               return None
               
           # Check global limit
           total_connections = sum(ACTIVE_CONNECTIONS.values())
           if total_connections >= MAX_CONCURRENT_CONNECTIONS:
               print(f"🚫 Global connection limit reached ({total_connections}/{MAX_CONCURRENT_CONNECTIONS})")
               # Try to clean up stale connections
               cleanup_stale_connections()
               return None
               
           ACTIVE_CONNECTIONS[connection_key] = current_count + 1
   
       # Create connection with enhanced settings
       sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
       sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
       sock.settimeout(timeout)
       sock.connect((ip, port))
       return sock
       
   except Exception as e:
       print(f"⚠️  Connection failed to {ip}:{port}: {e}")
       # Decrement connection count on failure
       with CONNECTION_POOL_LOCK:
           if connection_key in ACTIVE_CONNECTIONS:
               ACTIVE_CONNECTIONS[connection_key] -= 1
               if ACTIVE_CONNECTIONS[connection_key] <= 0:
                   del ACTIVE_CONNECTIONS[connection_key]
       return None

def close_safe_connection(sock: socket.socket, ip: str, port: int):
   """Safely close connection and update connection pool"""
   connection_key = f"{ip}:{port}"
   
   try:
       sock.close()
   except:
       pass
   
   # Update connection count
   with CONNECTION_POOL_LOCK:
       if connection_key in ACTIVE_CONNECTIONS:
           ACTIVE_CONNECTIONS[connection_key] -= 1
           if ACTIVE_CONNECTIONS[connection_key] <= 0:
               del ACTIVE_CONNECTIONS[connection_key]

def cleanup_stale_connections():
   """Clean up stale connections periodically"""
   with CONNECTION_POOL_LOCK:
       global ACTIVE_CONNECTIONS
       stale_connections = []
       total_connections = sum(ACTIVE_CONNECTIONS.values())
       
       print(f"🔍 Connection pool status: {len(ACTIVE_CONNECTIONS)} peers, {total_connections} total connections")
       
       for connection_key, count in ACTIVE_CONNECTIONS.items():
           # Clean up pools that are stuck or excessive
           if count > MAX_CONCURRENT_CONNECTIONS:
               stale_connections.append(connection_key)
               print(f"🧹 Marking {connection_key} for cleanup (count: {count})")
           elif count < 0:  # Negative counts (shouldn't happen but safety check)
               stale_connections.append(connection_key)
               print(f"🧹 Fixing negative count for {connection_key}")
       
       # Reset stale connection counts
       for key in stale_connections:
           old_count = ACTIVE_CONNECTIONS[key]
           ACTIVE_CONNECTIONS[key] = 0
           print(f"🧹 Cleaned connection pool for {key} (was: {old_count}, now: 0)")
       
       # Remove empty entries
       empty_keys = [k for k, v in ACTIVE_CONNECTIONS.items() if v <= 0]
       for key in empty_keys:
           del ACTIVE_CONNECTIONS[key]
           
       print(f"✅ Connection cleanup complete. Active pools: {len(ACTIVE_CONNECTIONS)}")

def connection_pool_monitor():
   """Background thread to monitor and clean connection pools"""
   while True:
       try:
           time.sleep(120)  # Run every 2 minutes
           cleanup_stale_connections()
       except Exception as e:
           print(f"Connection pool monitor error: {e}")

# Peer Discovery Functions
def get_canonical_peer_address(ip: str, connection_port: int) -> Tuple[str, int]:
   """PORT FIX: Always return server port 8334, ignore any random client ports"""
   return (ip, PEER_PORT)  # PEER_PORT = 8334 - ALWAYS

def discover_bootstrap_peers() -> List[Tuple[str, int]]:
    """
    Enhanced bootstrap discovery – try ALL hardcoded nodes and collect ALL peers.
    
    This function connects to ALL reachable seeds and collects their peer lists,
    creating a comprehensive view of the network instead of stopping at the first success.
    """
    bootstrap_candidates = [
        ('3.149.130.220', 8334),  # Server 1
        ('35.81.59.214', 8334),   # Server 2
        ('52.209.95.50', 8334),   # Server 3
        ('108.168.27.45', 8334),  # Local machine
    ]

    all_discovered_peers: Set[Tuple[str, int]] = set()
    successful_seeds = 0
    
    print("🔍 Starting comprehensive bootstrap discovery...")
    
    for ip, port in bootstrap_candidates:
        # Avoid dialing our own address
        if is_self_peer(ip):
            continue
            
        print(f"📡 Attempting to connect to bootstrap node {ip}:{port}...")
        sock = create_safe_connection(ip, port, timeout=10)
        
        if sock:
            try:
                # This seed is alive, add it to discovered peers
                all_discovered_peers.add((ip, port))
                successful_seeds += 1
                
                # Request its peer list
                request = {'type': 'get_peers'}
                sock.sendall(json.dumps(request).encode())
                sock.settimeout(10)
                data = sock.recv(BUFFER_SIZE)
                
                if data:
                    message = json.loads(data.decode())
                    if message.get('type') == 'peer_list':
                        peer_list = message.get('data', [])
                        peers_added = 0
                        
                        for peer_ip, peer_port in peer_list:
                            canonical_peer = get_canonical_peer_address(peer_ip, peer_port)
                            # Skip our own address to prevent self-dialing
                            if not is_self_peer(canonical_peer[0]):
                                all_discovered_peers.add(canonical_peer)
                                peers_added += 1
                                
                        print(f"✅ Bootstrap {ip}:{port}: Found {peers_added} unique peers")
                        
            except Exception as e:
                print(f"⚠️  Bootstrap discovery error for {ip}:{port}: {e}")
            finally:
                close_safe_connection(sock, ip, port)
        else:
            print(f"❌ Bootstrap node {ip}:{port} unreachable")

    final_peer_list = list(all_discovered_peers)
    print(f"🌐 Bootstrap discovery complete: {successful_seeds} seeds responded, {len(final_peer_list)} total unique peers found")

    # Update geographic distribution
    if final_peer_list:
        geographic_tracker.update_peer_geography(final_peer_list)
        geo_stats = geographic_tracker.get_geographic_distribution()
        print(f"🌍 Geographic distribution: {geo_stats['total_countries']} countries")

    return final_peer_list

def resilient_peer_discovery():
    """Production-grade peer discovery that survives seed node failures (randomized + throttled)"""
    while True:
        time.sleep(BASE_PEER_BROADCAST_INTERVAL)
        try:
            # Load and drop self up-front
            with PEERS_LOCK:
                current_peers = load_json(PEERS_FILE, [])
                current_peers = [
                    p for p in current_peers
                    if isinstance(p, (list, tuple)) and len(p) >= 2 and not is_self_peer(p[0])
                ]

            # Phase 1: bootstrap if depleted
            if len(current_peers) < 2:
                print("🔄 Peer list depleted, attempting bootstrap discovery...")
                bootstrap_peers = discover_bootstrap_peers()
                if bootstrap_peers:
                    clean_peers = sanitize_peer_list(bootstrap_peers)
                    with PEERS_LOCK:
                        save_json(PEERS_FILE, clean_peers)
                    current_peers = clean_peers
                    print(f"✅ Bootstrap recovery: Found {len(clean_peers)} peers")

            # Phase 2: cross-discovery from existing peers (randomized & rate-limited)
            if current_peers:
                # Canonicalize and filter self once
                candidates = []
                for ip, port in current_peers:
                    cip, cport = get_canonical_peer_address(ip, port)
                    if not is_self_peer(cip):
                        candidates.append((cip, cport))

                # Randomize which peers we try this round
                random.shuffle(candidates)

                live_peers = set()
                pinged = 0
                now = time.time()

                for ip, port in candidates:
                    if pinged >= DISCOVERY_FANOUT:
                        break

                    # Respect per-peer backoff and TTL
                    if now < PEER_BACKOFF.get((ip, port), 0):
                        continue
                    if now - LAST_GETPEERS.get((ip, port), 0) < GETPEERS_TTL:
                        continue

                    sock = create_safe_connection(ip, port, timeout=15)
                    if not sock:
                        # schedule backoff
                        next_wait = min(MAX_BACKOFF, (PEER_BACKOFF.get((ip, port), 0) - now) * 2 if (ip, port) in PEER_BACKOFF else DEFAULT_BACKOFF)
                        PEER_BACKOFF[(ip, port)] = now + max(DEFAULT_BACKOFF, next_wait)
                        continue

                    try:
                        live_peers.add((ip, port))
                        # Ask for peers once, then cool down this peer
                        sock.settimeout(10)
                        sock.sendall(json.dumps({'type': 'get_peers'}).encode())
                        data = sock.recv(BUFFER_SIZE)
                        LAST_GETPEERS[(ip, port)] = now
                        if data:
                            message = json.loads(data.decode())
                            if message.get('type') == 'peer_list':
                                peer_list = message.get('data', [])
                                added = 0
                                for peer_ip, peer_port in peer_list:
                                    pi, pp = get_canonical_peer_address(peer_ip, peer_port)
                                    if not is_self_peer(pi):
                                        live_peers.add((pi, pp))
                                        added += 1
                                print(f"🔍 Cross-discovery: got {len(peer_list)} (added {added}) from {ip}:{port}")
                        pinged += 1
                    except Exception as e:
                        # exponential-ish backoff with a cap
                        prev = PEER_BACKOFF.get((ip, port), 0)
                        wait = min(MAX_BACKOFF, DEFAULT_BACKOFF if prev <= now else (prev - now) * 2)
                        PEER_BACKOFF[(ip, port)] = now + wait
                        print(f"🔍 Cross-discovery failed for {ip}:{port}: {e} (backoff ~{int(wait)}s)")
                    finally:
                        close_safe_connection(sock, ip, port)

                # Persist union of known + live + seeds; never include self
                if live_peers:
                    with PEERS_LOCK:
                        current = load_json(PEERS_FILE, [])
                        def canonize(lst):
                            out = []
                            for it in lst:
                                if isinstance(it, (list, tuple)) and len(it) >= 2:
                                    out.append(get_canonical_peer_address(it[0], it[1]))
                            return out

                        known = set(canonize(current))
                        live  = set(live_peers)
                        seeds = set(canonize(HARDCODED_SEEDS))
                        union = {p for p in (known | live | seeds) if not is_self_peer(p[0])}
                        clean_peers = sanitize_peer_list(list(union))

                        # Only write if content changed
                        if set(known) != set(clean_peers):
                            save_json(PEERS_FILE, clean_peers)
                            print(f"🌐 Peer discovery updated: {len(live)} live / {len(clean_peers)} known")
                        else:
                            print(f"🌐 Peer discovery: {len(live)} live / {len(clean_peers)} known (no change)")

        except Exception as e:
            print(f"🔍 Resilient peer discovery error: {e}")

# Core blockchain functions
def double_sha256(data: str) -> str:
   """Bitcoin's double SHA256 hash function"""
   first_hash = hashlib.sha256(data.encode()).digest()
   second_hash = hashlib.sha256(first_hash).digest()
   return second_hash.hex()

def load_json(filename: str, default):
   """Enhanced thread-safe JSON file loading with better error handling"""
   if not os.path.exists(filename):
       return default
   
   max_retries = 3
   for attempt in range(max_retries):
       try:
           with open(filename, 'r') as f:
               return json.load(f)
       except (json.JSONDecodeError, IOError) as e:
           print(f"⚠️  Error loading {filename} (attempt {attempt + 1}): {e}")
           if attempt < max_retries - 1:
               time.sleep(0.1)  # Brief delay before retry
           else:
               print(f"❌ Failed to load {filename} after {max_retries} attempts, using default")
               return default
   return default

consensus_analytics = ConsensusAnalytics.load_analytics()
fork_memory = ForkMemory()
witness_node = ConsensusWitness.load_witness_data()
adaptive_consensus = AdaptiveConsensus(consensus_analytics)
reorg_protection = ReorgProtection()
attack_prevention = AttackPrevention()
geographic_tracker = GeographicTracker()
emergency_system = EmergencyResponseSystem()
chain_switch_tracker = ChainSwitchTracker(CHAIN_SWITCH_DAMPENING)

# Genesis puzzle is disabled; placeholder for future implementation
genesis_puzzle = None

def save_json(filename: str, data):
   """Enhanced thread-safe JSON file saving with atomic operations"""
   try:
       # Write to temporary file first, then atomic rename
       temp_file = filename + '.tmp'
       with open(temp_file, 'w') as f:
           json.dump(data, f, indent=2)
       
       # Atomic rename (works on both Unix and Windows)
       if os.path.exists(filename):
           if sys.platform.startswith('win'):
               os.remove(filename)  # Windows requires this
       os.rename(temp_file, filename)
       
   except Exception as e:
       print(f"⚠️  Error saving {filename}: {e}")
       if os.path.exists(temp_file):
           try:
               os.remove(temp_file)
           except:
               pass

def create_wallet(wallet_file: str) -> Dict:
   """Create a new CypherMint-style wallet"""
   sk = ecdsa.SigningKey.generate(curve=ecdsa.SECP256k1)
   vk = sk.get_verifying_key()
   
   private_key = base64.b64encode(sk.to_string()).decode()
   public_key = base64.b64encode(vk.to_string()).decode()
   
   # CypherMint address generation (simplified)
   pubkey_hash = hashlib.sha256(public_key.encode()).digest()
   ripemd160 = hashlib.new('ripemd160')
   ripemd160.update(pubkey_hash)
   address = ripemd160.hexdigest()
   
   wallet = {
       "private_key": private_key,
       "public_key": public_key,
       "address": address
   }
   save_json(wallet_file, wallet)
   return wallet

def load_wallet(wallet_file: str) -> Dict:
   """Load wallet from file"""
   if not os.path.exists(wallet_file):
       print(f"Wallet file '{wallet_file}' not found.")
       sys.exit(1)
   return load_json(wallet_file, {})

def calculate_block_hash(block: Dict) -> str:
   """Calculate block hash using Bitcoin's method"""
   # Create block header (simplified version of Bitcoin's 80-byte header)
   header_data = {
       'version': block.get('version', 1),
       'previous_hash': block['previous_hash'],
       'merkle_root': block['merkle_root'],
       'timestamp': block['timestamp'],
       'bits': block['bits'],
       'nonce': block['nonce']
   }
   
   header_string = json.dumps(header_data, sort_keys=True)
   return double_sha256(header_string)

def get_block_reward(block_height: int) -> int:
   """Calculate block reward with Bitcoin's halving schedule"""
   halvings = block_height // HALVING_INTERVAL
   if halvings >= 64:  # After 64 halvings, reward becomes 0
       return 0
   return INITIAL_REWARD >> halvings
def get_puzzle_clue(block_height: int) -> Optional[str]:
    """Return puzzle clue for specific block heights"""
    clues = {
        2016: "Put your first clue here",
        4032: "Put your second clue here",
        210000: "Put your final clue here"
    }
    return clues.get(block_height)


def is_valid_chain(chain: List[Dict]) -> bool:
   """Validate entire blockchain after normalization (contiguous prefix)."""
   if not chain:
       return False
   if not chain:
        return False

    # CRITICAL: First check indices match positions
   if not validate_chain_indices_match_positions(chain):
        return False

    # Then check indices are sequential
   if not validate_blockchain_indices(chain):
        return False

   chain = sort_and_dedupe_by_index(chain)

   # Validate genesis block
   genesis = chain[0]
   if genesis.get('index') != 0 or genesis.get('previous_hash') != '0' * 64:
       return False

   # Validate each subsequent block
   for i in range(1, len(chain)):
       current_block = chain[i]
       previous_block = chain[i - 1]

       # Validate block header
       if not CypherMintValidator.validate_block_header(current_block, previous_block):
           return False

       # Validate block hash
       if current_block.get('hash') != calculate_block_hash(current_block):
           return False

       # Validate merkle root
       expected_merkle = MerkleTree.calculate_merkle_root(current_block.get('transactions', []))
       if current_block.get('merkle_root') != expected_merkle:
           return False

   return True


def calculate_chain_work(chain: List[Dict]) -> int:
   """Calculate total work in chain using Bitcoin's method"""
   total_work = 0
   for block in chain:
       target = DifficultyAdjustment.bits_to_target(block.get('bits', MAX_TARGET))
       # Work = 2^256 / (target + 1)
       work = (1 << 256) // (target + 1)
       total_work += work
   return total_work

def sign_data(private_key_b64: str, data: str) -> str:
   """Sign data with private key"""
   sk = ecdsa.SigningKey.from_string(base64.b64decode(private_key_b64), curve=ecdsa.SECP256k1)
   return base64.b64encode(sk.sign(data.encode())).decode()

def verify_signature(public_key_b64: str, signature_b64: str, data: str) -> bool:
   """Verify signature"""
   try:
       vk = ecdsa.VerifyingKey.from_string(base64.b64decode(public_key_b64), curve=ecdsa.SECP256k1)
       return vk.verify(base64.b64decode(signature_b64), data.encode())
   except:
       return False

def create_coinbase_transaction(miner_address: str, block_height: int, fees: int = 0) -> Dict:
    reward = get_block_reward(block_height)
    fee_to_foundation = int(reward * 0.02)
    miner_reward = reward - fee_to_foundation

    txid = hashlib.sha256(f"coinbase-{block_height}".encode()).hexdigest()

    coinbase_tx = {
        "type": "coinbase",
        "id": txid,
        "inputs": [{
            "txid": txid,
            "index": 0xffffffff,
            "script_sig": f"Block reward for height {block_height}",
            "sequence": 0xffffffff
        }],
        "outputs": [
            {
                "amount": miner_reward,
                "address": miner_address
            },
            {
                "amount": fee_to_foundation,
                "address": get_genesis_address()
            }
        ],
        "lock_time": 0
    }

    clue = get_puzzle_clue(block_height)
    if clue:
        coinbase_tx["message"] = clue

    return coinbase_tx


def normalize_transaction_output(output: Dict) -> Dict:
   """Normalize transaction output format to ensure consistency"""
   # Handle both 'amount'/'value' and 'address'/'to' formats
   amount = output.get('amount', output.get('value', 0))
   address = output.get('address', output.get('to', ''))
   
   # Extract address from script_pubkey if needed (for genesis compatibility)
   if not address and 'script_pubkey' in output:
       script = output['script_pubkey']
       # Extract address from "OP_DUP OP_HASH160 ADDRESS OP_EQUALVERIFY OP_CHECKSIG"
       parts = script.split()
       if len(parts) >= 3:
           address = parts[2]
   
   return {
       'address': address,
       'amount': int(amount),
       'script_pubkey': output.get('script_pubkey', f"OP_DUP OP_HASH160 {address} OP_EQUALVERIFY OP_CHECKSIG")
   }

def update_treasure_hunt_status(solver_address: str, block_height: int):
    """Track treasure hunt progress"""
    status = load_json('treasure_hunt.json', {
        'solvers': {},
        'clues_found': [],
        'winner': None
    })
    
    if solver_address not in status['solvers']:
        status['solvers'][solver_address] = {
            'clues_found': [],
            'first_seen': time.time()
        }
    
    status['solvers'][solver_address]['clues_found'].append(block_height)
    save_json('treasure_hunt.json', status)

# Part 6: Mining and Network Functions

def mine_block_competitive(miner_address: str, previous_block: Dict, transactions: List[Dict], 
                         bits: int, stop_event: threading.Event, block_height: int) -> Dict:
   """Mine a block competitively with witness node tracking"""
   
   # Calculate fees
   fees = 0
   
   # Create coinbase transaction
   coinbase_tx = create_coinbase_transaction(miner_address, block_height)
   all_transactions = [coinbase_tx] + transactions
   
   # Calculate merkle root
   merkle_root = MerkleTree.calculate_merkle_root(all_transactions)
   
   # Create block template with FIXED timestamp (Bitcoin-style)
   fixed_timestamp = int(time.time())
   block = {
       'version': 1,
       'index': block_height,
       'timestamp': fixed_timestamp,  # Fixed at start - NO updates during mining
       'previous_hash': previous_block['hash'],
       'merkle_root': merkle_root,
       'bits': bits,
       'nonce': 0,
       'transactions': all_transactions
   }
   
   # Mine the block until solution found or cancelled
   target = DifficultyAdjustment.bits_to_target(bits)
   
   start_time = time.time()
   hash_attempts = 0
   last_status_time = start_time
   
   while not stop_event.is_set():
       block['hash'] = calculate_block_hash(block)
       block_hash_int = int(block['hash'], 16)
       hash_attempts += 1
       
       # Show progress every 10 seconds
       current_time = time.time()
       if current_time - last_status_time >= 10:
           elapsed = current_time - start_time
           hash_rate = hash_attempts / elapsed if elapsed > 0 else 0
           print(f"⛏️  Block {block_height}: {hash_attempts:,} attempts, {elapsed:.1f}s elapsed, {hash_rate:.0f} H/s")
           last_status_time = current_time
       
       if block_hash_int < target:
           mining_time = time.time() - start_time
           hash_rate = hash_attempts / mining_time if mining_time > 0 else 0
           
           print(f"✅ Block {block_height} SOLUTION FOUND!")
           print(f"🔗 Hash: {block['hash']}")
           print(f"🎯 Nonce: {block['nonce']}")
           print(f"⏱️  Mining time: {mining_time:.1f} seconds")
           print(f"⚡ Hash rate: {hash_rate:.0f} H/s")
           print(f"🎯 Leading zeros: {len(block['hash']) - len(block['hash'].lstrip('0'))}")
           
           # Update witness node stats
           witness_node.update_validation_count(block_height)
           witness_node.save_witness_data()
           
           return block
       
       block['nonce'] += 1
   
   # Mining was cancelled
   print(f"⏹️  Mining block {block_height} cancelled (someone else won)")
   raise InterruptedError("Mining cancelled")

def enhanced_consensus_check(peers: List[Tuple[str, int]], is_seed: bool = False) -> List[Dict]:
    """Enhanced consensus mechanism with adaptive checks, witness nodes, and chain switch dampening"""
    with CONSENSUS_LOCK:
        local_chain = load_json(BLOCKCHAIN_FILE, [])
        if not local_chain:
            print("📭 No local blockchain for consensus")
            return []
        
        print(f"\n🔄 ENHANCED CONSENSUS CHECK - Local height: {len(local_chain)}")
        
        # SEED/SOLO MINING FIX: If no peers or seed node, skip consensus
        if not peers or (is_seed and len(peers) == 0):
            print("🔨 SOLO/SEED MODE: Skipping consensus, continuing with local chain")
            return local_chain
        
        # SMALL NETWORK FIX: Adjust threshold for small networks
        if len(peers) <= 3:
            consensus_threshold = 1  # Only need 1 peer agreement in tiny network
            print(f"🔧 Small network detected: Using threshold of {consensus_threshold}")
        else:
            # Dynamic consensus parameters based on network state
            network_maturity = min(len(local_chain) / 10000, 1.0)
            consensus_threshold = max(1, int(CONSENSUS_THRESHOLD_PEER * (1 + network_maturity)))
        
        # Witness node weight adjustment
        witness_weight = 1.0
        if witness_node.witness_status:
            witness_weight = witness_node.calculate_witness_weight()
            print(f"⭐ Witness node weight: {witness_weight:.2f}")
        
        peer_chains = []
        better_chains_found = 0
        valid_peer_responses = 0
        witness_peer_count = 0
        
        # Check each peer
        for ip, port in peers[:MAX_CONSENSUS_PEERS]:
            if is_self_peer(ip, port):
                continue
                
            try:
                sock = create_safe_socket()
                sock.settimeout(PEER_TIMEOUT)
                
                if sock.connect_ex((ip, port)) == 0:
                    # Send blockchain request
                    request = create_message("get_blockchain", {})
                    sock.sendall(request)
                    
                    # Receive response
                    response = receive_full_message(sock)
                    
                    if response and response.get('type') == 'blockchain':
                        peer_chain = response.get('data', [])
                        
                        if peer_chain and validate_blockchain(peer_chain):
                            valid_peer_responses += 1

                            if attack_prevention.detect_selfish_mining(peer_chain, ip):
                                print(f"⚠️  Ignoring chain from {ip} due to selfish mining detection")
                                continue
                            
                            # Check if peer is a witness node
                            if response.get('witness_node', False):
                                witness_peer_count += 1
                            
                            # Check if peer has better chain
                            if len(peer_chain) > len(local_chain):
                                better_chains_found += 1
                                print(f"📊 Better chain from {ip}:{port} - Height: {len(peer_chain)}")
                            
                            peer_chains.append(peer_chain)
                        else:
                            if peer_chain:
                                print(f"❌ Invalid chain from {ip}:{port}")
                            else:
                                print(f"📭 Empty chain from {ip}:{port}")
                    
            except Exception as e:
                print(f"❌ Consensus check failed with {ip}:{port}: {e}")
            finally:
                close_safe_connection(sock, ip, port)
        
        # Apply witness weight to consensus threshold
        witness_peer_ratio = witness_peer_count / max(len(peers), 1)
        effective_threshold = max(1, int(consensus_threshold / witness_weight))
        
        print(f"📊 Consensus results: {valid_peer_responses} valid responses, "
              f"{better_chains_found} better chains, threshold: {effective_threshold}")
        
        # Find the best chain
        best_chain = local_chain
        best_height = len(local_chain)
        
        for chain in peer_chains:
            if len(chain) > best_height and validate_blockchain(chain):
                best_chain = chain
                best_height = len(chain)
        
        should_adopt = False
        required_improvement = MIN_IMPROVEMENT_NORMAL
        
        if best_chain != local_chain:
            # Check if we can switch based on dampening
            can_switch, required_improvement = chain_switch_tracker.can_switch(
                len(local_chain), len(best_chain)
            )
            
            if better_chains_found >= effective_threshold and can_switch:
                should_adopt = True
                print(f"🔄 ADOPTING: {better_chains_found} better chains found (required improvement: {required_improvement})")
            elif valid_peer_responses > 0 and len(best_chain) > len(local_chain) and can_switch:
                should_adopt = True
                print(f"🔄 ADOPTING: Longer chain found (height {len(best_chain)} > {len(local_chain)}, improvement: {len(best_chain) - len(local_chain)})")
            else:
                if not can_switch:
                    time_until_switch = chain_switch_tracker.dampening_period - (time.time() - chain_switch_tracker.history['last_switch'])
                    print(f"⏳ Chain switch dampening active: {time_until_switch:.1f}s remaining (need {required_improvement} blocks improvement)")
        
        if should_adopt:
            if should_adopt:
    # Check if reorg is acceptable
                reorg_acceptable, reorg_reason = reorg_protection.is_reorg_acceptable(local_chain, best_chain)
                
                if not reorg_acceptable:
                    print(f"❌ REORG REJECTED: {reorg_reason}")
                    consensus_analytics.record_rejection("deep_reorg")
                    should_adopt = False
                else:
                    print(f"✅ REORG CHECK: {reorg_reason}")
                    
                    # Record the switch before adopting
                    chain_switch_tracker.record_switch(len(local_chain), len(best_chain))
            
            # Record fork if switching chains
            if best_chain != local_chain:
                fork_depth = len(local_chain) - fork_memory.find_common_ancestor(local_chain, best_chain)
                consensus_analytics.record_fork(fork_depth)
                fork_memory.record_chain_switch(local_chain, best_chain)
            
            print(f"🔄 CONSENSUS ADOPTION: New chain with height {len(best_chain)}")
            
            # Validate chain for duplicate transactions
            print("🔍 CONSENSUS: Validating chain for duplicate transactions...")
            chain_valid = True
            
            for i in range(1, len(best_chain)):
                current_block = best_chain[i]
                previous_blocks = best_chain[:i]
                
                if not CypherMintValidator.validate_transactions_unique(current_block, previous_blocks):
                    print(f"❌ CONSENSUS REJECTED: Block {i} contains duplicate transactions")
                    chain_valid = False
                    break
            
            if chain_valid:

                if not validate_blockchain_indices(best_chain):
                    print("❌ CONSENSUS REJECTED: Chain has invalid block indices")
                    return local_chain
                
                print("✅ CONSENSUS: Chain validation passed - no duplicate transactions")
                with BLOCKCHAIN_LOCK:
                    save_json(BLOCKCHAIN_FILE, best_chain)
                
                # Trigger UTXO rebuild after consensus
                print("🔧 CONSENSUS: Rebuilding UTXO set from new chain...")
                wallet_manager.rebuild_utxo_from_blockchain(best_chain)
                
                # Broadcast our chain info
                broadcast_chain_info(peers)
                
                return best_chain
            else:
                print("❌ CONSENSUS: New chain rejected due to validation failure")
                consensus_analytics.record_rejection("duplicate_transactions")
        
        # Update adaptive interval
        global LAST_CONSENSUS_TIME, ADAPTIVE_CONSENSUS_INTERVAL
        LAST_CONSENSUS_TIME = time.time()
        
        # Adjust interval based on network state
        if better_chains_found > 0:
            ADAPTIVE_CONSENSUS_INTERVAL = max(MIN_CONSENSUS_INTERVAL, 
                                            ADAPTIVE_CONSENSUS_INTERVAL * 0.8)
        else:
            ADAPTIVE_CONSENSUS_INTERVAL = min(MAX_CONSENSUS_INTERVAL,
                                            ADAPTIVE_CONSENSUS_INTERVAL * 1.2)
        
        return local_chain
    
def _single_allowed(ip, port):
    return time.time() >= _single_sync_backoff.get((ip, port), 0)

def _single_backoff(ip, port, secs=60):
    _single_sync_backoff[(ip, port)] = time.time() + secs

def single_peer_consensus_sync(peer: Tuple[str, int]) -> Optional[List[Dict]]:
    """Sync from exactly one peer, but only if it's provably ahead. P2P ranges only."""
    ip, port = peer
    if is_self_peer(ip) or not _single_allowed(ip, port):
        return None

    # 1) Preflight: only if peer is ahead by height or same height w/ higher work
    local_h, local_w = _local_tip_info()
    info = get_peer_info_quick(ip, port, timeout=5)
    if not info:
        _single_backoff(ip, port, 60)
        return None

    if not (info['height'] > local_h or (info['height'] == local_h and info['total_work'] > local_w)):
        # Not ahead -> don't fetch
        return None

    target_h = int(info['height'])
    start = 0
    blocks_out: List[Dict] = []

    # 2) Sequential range fetches; one request per connection (no reuse)
    while start < target_h:
        end = min(start + CHAIN_SEGMENT_MAX, target_h)
        s = create_safe_connection(ip, port, timeout=8)
        if not s:
            _single_backoff(ip, port, 60)
            return None
        try:
            s.settimeout(8)
            req = {"type": "get_blocks_range", "data": {"start": start, "end": end}}
            s.sendall(json.dumps(req).encode())
            buf = s.recv(4 * 1024 * 1024)
            if not buf:
                _single_backoff(ip, port, 60)
                return None

            msg = json.loads(buf.decode())
            # Accept either 'blocks' or legacy 'data'
            if msg.get("type") != "blocks_range":
                _single_backoff(ip, port, 60)
                return None

            segment = msg.get("blocks") or msg.get("data") or []
            if not isinstance(segment, list) or (not segment and start < target_h):
                _single_backoff(ip, port, 60)
                return None

            blocks_out.extend(segment)
            # Advance using server's 'to' if present, else our 'end'
            start = (msg.get("to", end - 1)) + 1
        except Exception:
            _single_backoff(ip, port, 60)
            return None
        finally:
            try: s.close()
            except: pass

    # 3) Adopt if strictly better by work (height breaks ties)
    if blocks_out and is_valid_chain(blocks_out):
        cand_w = calculate_chain_work(blocks_out)
        if cand_w > local_w or (cand_w == local_w and len(blocks_out) - 1 > local_h):
            return blocks_out
    return None

def enhanced_consensus_recovery(peers: List, is_seed: bool = False, max_failures: int = 5):
   """Hierarchical consensus with fallback recovery"""
   
   # Validate inputs
   if not peers:
       print("⚠️ No peers available for consensus")
       return load_json(BLOCKCHAIN_FILE, [])
   
   print(f"🔄 Starting consensus recovery with {len(peers)} peers")
   
   # Phase 1: Try normal multi-peer consensus
   for attempt in range(max_failures):
       try:
           print(f"🔄 Consensus attempt {attempt + 1}/{max_failures}")
           consensus_chain = production_consensus_with_healing(peers, is_seed)
           current_chain = load_json(BLOCKCHAIN_FILE, [])
           
           # Safe None check
           if consensus_chain is None:
               print(f"⚠️ Consensus attempt {attempt + 1} returned None - no valid responses")
               continue
               
           if not isinstance(consensus_chain, list):
               print(f"⚠️ Consensus attempt {attempt + 1} returned invalid type: {type(consensus_chain)}")
               continue
           
           if len(consensus_chain) > len(current_chain):
               print(f"✅ Multi-peer consensus successful: {len(consensus_chain)} blocks")
               return consensus_chain
           else:
               print(f"📊 Consensus chain not longer: {len(consensus_chain)} vs current {len(current_chain)}")
               
       except Exception as e:
           print(f"⚠️ Consensus attempt {attempt + 1} failed: {e}")
           if attempt < max_failures - 1:
               time.sleep(2)  # Wait before retry
   
   # Phase 2: Fallback to single-peer **ahead** of us
   if not is_seed and peers:
        print("🚨 Multi-peer consensus failed - attempting single-peer recovery")

        local_h, local_w = _local_tip_info()
        ahead_candidates: List[Tuple[str,int,int,int]] = []  # ip, port, h, work

        # Probe peers for height/work and keep only those ahead
        for p in peers:
            if not (isinstance(p, (list, tuple)) and len(p) >= 2):
                continue
            ip, port = p[0], p[1]
            if is_self_peer(ip):
                continue
            info = get_peer_info_quick(ip, port, timeout=5)
            if not info:
                continue
            if info['height'] > local_h or (info['height'] == local_h and info['total_work'] > local_w):
                ahead_candidates.append((ip, port, info['height'], info['total_work']))

        if ahead_candidates:
            # Prefer best-first; you can randomize within the top few to spread load
            ahead_candidates.sort(key=lambda x: (x[2], x[3]), reverse=True)
            # Optionally: random.shuffle(ahead_candidates[:3])
            for ip, port, _, _ in ahead_candidates[:5]:
                print(f"🔄 Attempting single-peer recovery from {ip}:{port}")
                single_chain = single_peer_consensus_sync((ip, port))
                if isinstance(single_chain, list) and single_chain and try_adopt_chain(single_chain):
                    print(f"✅ Successfully synced from {ip} - height {len(single_chain)}")
                    return single_chain
        else:
            print("↩️  No peers ahead; skipping single-peer recovery")

   
   # Phase 3: Return current chain if all else fails
   print("⚠️ All consensus methods failed - maintaining current chain")
   current_chain = load_json(BLOCKCHAIN_FILE, [])
   return current_chain if current_chain is not None else []

def safe_discover_peers(known_peers: List[Tuple[str, int]]) -> List[Tuple[str, int]]:
    """
    Perform peer discovery from a list of known peers.

    This helper canonicalizes the peers, then connects to a limited number of
    them to request their peer lists.  It will skip any peer whose IP matches
    this node (see :func:`is_self_peer`).  Discovered peers are canonicalized
    and deduplicated.  If new peers are found, the peer list on disk is
    updated.
    """
    # Convert known peers into a set of canonical addresses, skipping self
    all_peers: Set[Tuple[str, int]] = set()
    for peer in known_peers:
        if isinstance(peer, (list, tuple)) and len(peer) == 2:
            canonical = get_canonical_peer_address(peer[0], peer[1])
            if not is_self_peer(canonical[0]):
                all_peers.add(canonical)

    # Limit the number of peers we interrogate to prevent spamming the network
    discovery_count = 0
    max_discoveries = min(len(known_peers), 10)

    # Loop over a copy of the peer set so we can modify all_peers while iterating
    for ip, port in list(all_peers)[:max_discoveries]:
        if discovery_count >= max_discoveries:
            break
        if is_self_peer(ip):
            continue
        sock = create_safe_connection(ip, port, timeout=15)
        if not sock:
            continue
        try:
            # Request the peer list from this node
            request = {'type': 'get_peers'}
            sock.sendall(json.dumps(request).encode())
            sock.settimeout(10)
            data = sock.recv(BUFFER_SIZE)
            if data:
                message = json.loads(data.decode())
                if message.get('type') == 'peer_list':
                    peer_list = message.get('data', [])
                    for p in peer_list:
                        if isinstance(p, (list, tuple)) and len(p) == 2:
                            canonical_peer = get_canonical_peer_address(p[0], p[1])
                            if not is_self_peer(canonical_peer[0]):
                                all_peers.add(canonical_peer)
                    print(f"📡 Discovered {len(peer_list)} peers from {ip}:{port}")
                    discovery_count += 1
        except Exception as e:
            print(f"🔍 Safe peer discovery failed for {ip}:{port}: {e}")
        finally:
            close_safe_connection(sock, ip, port)

    # Convert back to a list of tuples
    new_peer_list = list(all_peers)
    if len(new_peer_list) > len(known_peers):
        # Sanitize before saving
        clean_peers = sanitize_peer_list(new_peer_list)
        with PEERS_LOCK:
            save_json(PEERS_FILE, clean_peers)
        print(f"✅ Updated peer list: {len(clean_peers)} total peers")

    if len(new_peer_list) > len(known_peers):
        geographic_tracker.update_peer_geography(new_peer_list)
    
    return new_peer_list

def force_initial_consensus(peers: List[Tuple[str, int]], is_seed: bool = False) -> List[Dict]:
   """CONSENSUS FIX: Mandatory initial sync before any mining"""
   print(f"🔄 FORCE INITIAL CONSENSUS - attempting {INITIAL_SYNC_ATTEMPTS} sync attempts...")
   
   best_chain = []
   
   for attempt in range(INITIAL_SYNC_ATTEMPTS):
       print(f"🔄 Consensus attempt {attempt + 1}/{INITIAL_SYNC_ATTEMPTS}")
       
       try:
           consensus_chain = enhanced_consensus_recovery(peers, is_seed=is_seed)
           
           if len(consensus_chain) > len(best_chain):
               best_chain = consensus_chain
               print(f"✅ Improved consensus: height {len(best_chain)}")
           
           # If we got a reasonable chain, we can proceed
           if len(best_chain) > 0:
               print(f"✅ Initial consensus successful: height {len(best_chain)}")
               return best_chain
               
       except Exception as e:
           print(f"⚠️  Consensus attempt {attempt + 1} failed: {e}")
           
       if attempt < INITIAL_SYNC_ATTEMPTS - 1:
           time.sleep(2)  # Wait between attempts
   
   print(f"⚠️  Initial consensus completed with height {len(best_chain)}")
   return best_chain

def start_mining(miner_address: str, seed: bool = False):
   """Start mining process with enhanced consensus and witness node tracking"""
   # Check if node qualifies as witness
   allow_solo_mining = seed
   if witness_node.should_become_witness():
       witness_node.witness_status = True
       print(f"⭐ Node qualified as WITNESS NODE! Weight: {witness_node.calculate_witness_weight():.2f}")
   
   # Load existing genesis block and convert to blockchain
   genesis_block = load_existing_genesis()

   
   
   # Initialize genesis block if needed (compute merkle root and hash)
   if genesis_block['index'] == 0:
       # Compute merkle root and block hash for loaded genesis block
       genesis_block['merkle_root'] = MerkleTree.calculate_merkle_root(genesis_block.get('transactions', []))
       genesis_block['hash'] = calculate_block_hash(genesis_block)
       # Update checkpoint for genesis
       CHECKPOINTS[0] = genesis_block['hash']
   
   # Check if blockchain.json already exists
   with BLOCKCHAIN_LOCK:
       existing_blockchain = load_json(BLOCKCHAIN_FILE, [])
       if existing_blockchain:
           blockchain = existing_blockchain
           print(f"Loaded existing blockchain with {len(blockchain)} blocks")
       else:
           blockchain = [genesis_block]
           save_json(BLOCKCHAIN_FILE, blockchain)
           print(f"Created new blockchain from genesis block")
   
   # CONSENSUS FIX: Universal bootstrap discovery for all nodes
   with PEERS_LOCK:
       if seed:
           # Seed node: Start with bootstrap list but discover others
           initial_peers = discover_bootstrap_peers()
           # Sanitize before saving
           clean_peers = sanitize_peer_list(initial_peers)
           save_json(PEERS_FILE, clean_peers)
           print(f"✅ SEED NODE: Bootstrap discovery found {len(clean_peers)} peers")
       else:
           # Peer node: Aggressive bootstrap discovery
           bootstrap_peers = discover_bootstrap_peers()
           if bootstrap_peers:
               clean_peers = sanitize_peer_list(bootstrap_peers)
               save_json(PEERS_FILE, clean_peers)
               peers = clean_peers
               print(f"🔍 PEER NODE: Bootstrap discovery found {len(clean_peers)} peers")
           else:
               # Fallback to hardcoded seeds
               peers = HARDCODED_SEEDS
               clean_peers = sanitize_peer_list(peers)
               save_json(PEERS_FILE, clean_peers)
               print(f"🔍 PEER NODE: Using hardcoded seeds ({len(clean_peers)} peers)")
   
   print(f"Starting mining to address: {miner_address}")
   print(f"Blockchain height: {len(blockchain)}")
   print(f"Running as: {'SEED node' if seed else 'PEER node'}")
   print(f"Network health: {consensus_analytics.get_network_health_score():.0f}/100")
   print(f"Witness status: {'ACTIVE' if witness_node.witness_status else 'BUILDING REPUTATION'}")
   
   with PEERS_LOCK:
       current_peers = load_json(PEERS_FILE, [])
       print(f"Known peers: {len(current_peers)}")
   
   # Start peer server first
   start_peer_server(blockchain)
   start_backfill_worker()
   time.sleep(3)  # Give server more time to start properly

   external_ip = setup_upnp_port()
   if external_ip:
       print(f"🎉 Network-accessible at {external_ip}:{PEER_PORT}")
   else:
       print(f"⚠️  May not be reachable from internet - check router settings")
   
   # Start resilient peer discovery background process
   threading.Thread(target=resilient_peer_discovery, daemon=True).start()
   print("🌐 Resilient peer discovery enabled")

   # Start connection pool monitoring
   threading.Thread(target=connection_pool_monitor, daemon=True).start()
   print("🧹 Connection pool monitoring enabled")
   
   # CONSENSUS FIX: MANDATORY initial consensus for ALL nodes
   with PEERS_LOCK:
       peers = load_json(PEERS_FILE, [])
   
   if peers:
       print("🔄 CONSENSUS FIX: Mandatory initial consensus sync...")
       
       # CONSENSUS FIX: No delays, immediate aggressive sync
       with BLOCKCHAIN_LOCK:
           blockchain = force_initial_consensus(peers, is_seed=seed)
           save_json(BLOCKCHAIN_FILE, blockchain)
           print(f"After initial consensus - Blockchain height: {len(blockchain)}")
   else:
       print("⚠️  No peers available for initial consensus")
       print("🧱 Bootstrapping mining from local genesis block (SEED mode fallback)")
       with BLOCKCHAIN_LOCK:
            blockchain = load_json(BLOCKCHAIN_FILE, [])
            if not blockchain:
                genesis_block = load_existing_genesis()
                blockchain = [genesis_block]
                save_json(BLOCKCHAIN_FILE, blockchain)
                print("✅ Initialized blockchain with genesis block")
   
   # Initialize UTXO set if empty
   with UTXO_LOCK:
       utxos = load_json(UTXO_FILE, [])
       if not utxos and blockchain:
           print("Initializing UTXO set from blockchain...")
           for block in blockchain:
               update_utxo_set(block)
           print("UTXO set initialized")
   
   # CONSENSUS FIX: Adaptive consensus monitoring
   def adaptive_consensus_monitor():
       while True:
           # Get adaptive interval
           interval = adaptive_consensus.get_consensus_interval()
           time.sleep(interval)
           
           try:
               with PEERS_LOCK:
                   current_peers = load_json(PEERS_FILE, [])
                   # Fix peer format issues
                   current_peers = [get_canonical_peer_address(peer[0], peer[1]) if isinstance(peer, (list, tuple)) and len(peer) == 2 else peer 
                                  for peer in current_peers if len(peer) == 2]
               
               if current_peers:
                   consensus_chain = enhanced_consensus_recovery(current_peers, is_seed=seed)
                   with BLOCKCHAIN_LOCK:
                       current_chain = load_json(BLOCKCHAIN_FILE, [])
                       if len(consensus_chain) != len(current_chain):
                           print(f"🔄 CONSENSUS UPDATE: height {len(current_chain)} -> {len(consensus_chain)}")
                           save_json(BLOCKCHAIN_FILE, consensus_chain)
           except Exception as e:
               print(f"Adaptive consensus monitor error: {e}")
   
   threading.Thread(target=adaptive_consensus_monitor, daemon=True).start()
   print("🔄 ADAPTIVE consensus monitoring enabled")
   
   print(f"🚀 CypherMint node ready - ENHANCED CONSENSUS ENABLED")
   
   # UTXO Auto-repair: Validate on startup
   if not enhanced_startup_validation():
       print("❌ Startup validation failed - check UTXO integrity manually")
       return
   
   print(f"Starting mining to address: {miner_address}")
   print(f"Blockchain height: {len(blockchain)}")
   
   while True:
       # UTXO Auto-repair: Periodic validation every 50 blocks
       with BLOCKCHAIN_LOCK:
           current_height = len(load_json(BLOCKCHAIN_FILE, []))
       
       # Emergency system monitoring every 50 blocks
           if current_height > 0 and current_height % 50 == 0:
                warnings = emergency_system.check_emergency_conditions()
                if warnings:
                    print(f"⚠️  EMERGENCY WARNINGS DETECTED:")
                    for warning in warnings:
                        print(f"   - {warning}")
                    
                    # Log as incident
                    emergency_system.log_incident('SECURITY_WARNING', {
                        'warnings': warnings,
                        'block_height': current_height
                    })
                
                # Exchange readiness check
                readiness = check_exchange_readiness()
                if readiness['ready']:
                    print("🎉 NETWORK IS EXCHANGE READY!")
                else:
                    print(f"📊 Exchange Readiness: {sum(readiness['checks'].values())}/{len(readiness['checks'])} requirements met")
       
       # Check for chain pruning needs
       if current_height > PRUNE_THRESHOLD:
           print(f"🔄 Chain pruning check at height {current_height}...")
           pruned_chain = prune_blockchain(load_json(BLOCKCHAIN_FILE, []))
           if len(pruned_chain) < current_height:
               with BLOCKCHAIN_LOCK:
                   save_json(BLOCKCHAIN_FILE, pruned_chain)
               print(f"✅ Chain pruned to {len(pruned_chain)} blocks")
            
       
       # Pre-mining consensus check
       with PEERS_LOCK:
           peers = load_json(PEERS_FILE, [])
           peers = [get_canonical_peer_address(peer[0], peer[1]) if isinstance(peer, (list, tuple)) and len(peer) == 2 else peer 
                   for peer in peers if len(peer) == 2]
       
       if peers:
           try:
               print(f"🔄 PRE-MINING CONSENSUS CHECK...")
               consensus_blockchain = enhanced_consensus_recovery(peers, is_seed=seed)
               with BLOCKCHAIN_LOCK:
                   current_blockchain = load_json(BLOCKCHAIN_FILE, [])
                   if len(consensus_blockchain) > len(current_blockchain):
                       blockchain = consensus_blockchain
                       save_json(BLOCKCHAIN_FILE, blockchain)
                       # Rebuild UTXO set from consensus chain
                       print("🔄 Pre-mining: Rebuilding UTXO set after consensus update...")
                       with UTXO_LOCK:
                           save_json(UTXO_FILE, [])
                           for block in blockchain:
                               update_utxo_set(block)
                       print(f"🔄 Pre-mining consensus: Updated to height {len(blockchain)}")
                   else:
                       blockchain = current_blockchain
           except Exception as e:
               print(f"Pre-mining consensus error: {e}")
               with BLOCKCHAIN_LOCK:
                   blockchain = load_json(BLOCKCHAIN_FILE, [])
       elif allow_solo_mining:
        print("🚀 Solo mining enabled - no peers found (SEED MODE)")
        with BLOCKCHAIN_LOCK:
            blockchain = load_json(BLOCKCHAIN_FILE, [])
       else:
        print("⏳ No peers available and not in solo mode - waiting...")
        time.sleep(5)
        continue
       
       mempool = load_json(MEMPOOL_FILE, [])
       
       if not blockchain:
           print("Blockchain file corrupted or missing.")
           break
       
       previous_block = blockchain[-1]
       next_block_height = len(blockchain)
       
       print(f"⛏️  Starting to mine block {next_block_height}")
       print(f"📊 Network health: {consensus_analytics.get_network_health_score():.0f}/100")
       
       # Calculate difficulty for next block

       # Calculate difficulty for next block
       height = len(blockchain)

       if height < DIFFICULTY_ADJUSTMENT_INTERVAL:
            new_bits = DifficultyAdjustment.calculate_next_difficulty(blockchain)
       elif height % DIFFICULTY_ADJUSTMENT_INTERVAL == 0:
            new_bits = DifficultyAdjustment.calculate_next_difficulty(blockchain)
       else:
            # carry forward between retargets
            new_bits = previous_block.get('bits', MAX_TARGET)

       print(f"🎯 Difficulty at height {height}: {hex(int(new_bits))}")
       
       # Select transactions from mempool (simplified)
       selected_transactions = mempool[:10]  # Limit to 10 transactions
       
       # Create mining cancellation flag
       mining_cancelled = threading.Event()
       
       # Start mining in background thread
       mining_result = {'block': None, 'error': None}
       
       def background_mine():
           try:
               mining_result['block'] = mine_block_competitive(
                   miner_address, previous_block, selected_transactions, 
                   new_bits, mining_cancelled, next_block_height
               )
           
           except Exception as e:
             mining_result['error'] = e
       
       mining_thread = threading.Thread(target=background_mine, daemon=True)
       mining_thread.start()
       
       # Ultra-fast mining monitoring (100ms checks)
       check_interval = 0.1  # 100ms
       last_check = time.time()
       
       while mining_thread.is_alive():
           time.sleep(check_interval)
           current_time = time.time()
           
           # Check blockchain every 100ms
           if current_time - last_check >= 0.1:
               with BLOCKCHAIN_LOCK:
                   current_blockchain = load_json(BLOCKCHAIN_FILE, [])
               if len(current_blockchain) > len(blockchain):
                if not validate_blockchain_indices(current_blockchain):
                    print("❌ Rejecting chain with mismatched indices")
                    continue
                    
                print(f"🏁 Block {next_block_height} mined by someone else first!")
                blockchain = current_blockchain
                print(f"✅ Accepted block {next_block_height} from network")
                
                # CRITICAL FIX: Remove confirmed transactions from mempool
                accepted_block = blockchain[next_block_height]
                if accepted_block and 'transactions' in accepted_block:
                    mempool = load_json(MEMPOOL_FILE, [])
                    confirmed_tx_ids = set()
                    
                    # Get all transaction IDs from the accepted block
                    for tx in accepted_block['transactions']:
                        tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                        confirmed_tx_ids.add(tx_id)
                    
                    # Remove confirmed transactions from mempool
                    remaining_mempool = []
                    for mem_tx in mempool:
                        mem_tx_id = mem_tx.get('txid') or double_sha256(json.dumps(mem_tx, sort_keys=True))
                        if mem_tx_id not in confirmed_tx_ids:
                            remaining_mempool.append(mem_tx)
                    
                    save_json(MEMPOOL_FILE, remaining_mempool)
                    print(f"🧹 Removed {len(mempool) - len(remaining_mempool)} confirmed transactions from mempool")
            
                # Rebuild UTXO if needed
                with UTXO_LOCK:
                    utxos = load_json(UTXO_FILE, [])
                    expected_blocks = next_block_height + 1
                    if len(utxos) < expected_blocks:  # Simple heuristic
                        print("🔄 Rebuilding UTXO set after accepting peer block")
                        rebuild_utxo_set(blockchain)

                mining_cancelled.set()  # Cancel our mining since someone else won
                break  # Exit the mining monitoring loop     
               
               last_check = current_time
       
       # Wait for mining thread to finish
       mining_thread.join(timeout=3)
       
       # Check results and verify we still won
       if mining_result['block'] and not mining_cancelled.is_set():
           # We successfully mined the block!
           new_block = mining_result['block']
           
           # CRITICAL: Double-check blockchain AGAIN before claiming victory
           with BLOCKCHAIN_LOCK:
               final_blockchain = load_json(BLOCKCHAIN_FILE, [])
               if len(final_blockchain) == len(blockchain):
                   # We still have the right to add our block
                   final_blockchain.append(new_block)
                   save_json(BLOCKCHAIN_FILE, final_blockchain)
                   
                   # Clear processed transactions from mempool
                   remaining_mempool = [tx for tx in mempool if tx not in selected_transactions]
                   save_json(MEMPOOL_FILE, remaining_mempool)
                   
                   # Update UTXO set
                   with UTXO_LOCK:
                       safe_update_utxos(new_block)

                   # Update checkpoint if needed
                   update_checkpoint(new_block)
                   
                   # ENHANCED: Broadcast to peers with better error handling
                   with PEERS_LOCK:
                       peers = load_json(PEERS_FILE, [])
                   
                   if peers:
                       print(f"📡 Broadcasting our block {new_block['index']} to network...")
                       enhanced_broadcast_new_block(peers, new_block)

                   # Verify our block was accepted
                   time.sleep(1)

                   # Check if OUR block hash is in the canonical chain
                   verification_blockchain = load_json(BLOCKCHAIN_FILE, [])
                   if (len(verification_blockchain) > new_block['index'] and 
                       verification_blockchain[new_block['index']]['hash'] == new_block['hash']):
                       
                       # Check if this block pays US
                       coinbase_tx = new_block['transactions'][0]
                       coinbase_address = coinbase_tx['outputs'][0]['address']
                       
                       if coinbase_address == miner_address:
                           print(f"🎉 WE MINED BLOCK {new_block['index']}!")
                           print(f"🔗 Hash: {new_block['hash']}")
                           print(f"✅ Block confirmed in canonical chain")
                           print(f"💰 Earned {get_block_reward(new_block['index'])/100000000:.8f} CPM")
                           
                           # Update witness stats
                           witness_node.blocks_validated += 1
                           witness_node.save_witness_data()
                       else:
                           print(f"🏁 Block {new_block['index']} confirmed but not ours")
                   else:
                       print(f"🏁 Block {new_block['index']} mined by someone else first!")
                       print(f"🔄 Our solution was valid but network accepted different block")
       
       elif mining_result['error']:
            print(f" Mining completed by another node: {mining_result['error']}")
            time.sleep(1)
           
       
       # Continue to next block

def enhanced_broadcast_new_block(peers: List[Tuple[str, int]], block: Dict):
   """ENHANCED: Broadcast new block with better connection management"""
   print(f"📡 Broadcasting block {block['index']} to {len(peers)} peers...")
   
   # Ensure all peers use canonical addresses
   canonical_peers = []
   for peer in peers:
        # Ensure peer is a tuple/list of length 2
        if isinstance(peer, (list, tuple)) and len(peer) == 2:
            canonical_peer = get_canonical_peer_address(peer[0], peer[1])
            # Skip self peers to avoid self-dialing
            if is_self_peer(canonical_peer[0]):
                continue
            canonical_peers.append(canonical_peer)
   
   success_count = 0
   max_broadcast_peers = min(len(canonical_peers), 8)
   
   for ip, port in canonical_peers[:max_broadcast_peers]:
       # Enhanced: Multiple attempts with exponential backoff
       for attempt in range(3):
           sock = create_safe_connection(ip, port, timeout=BROADCAST_TIMEOUT)
           if not sock:
               if attempt < 2:
                   time.sleep(1 * (attempt + 1))  # 1s, 2s delays
               continue
               
           try:
               message = {'type': 'new_block', 'data': block}
               sock.sendall(json.dumps(message).encode())
               success_count += 1
               print(f"✅ Sent block {block['index']} to {ip}:{port} (attempt {attempt + 1})")
               break  # Success, exit retry loop
               
           except Exception as e:
               if attempt == 2:  # Last attempt
                   print(f"❌ Failed to send block to {ip}:{port} after 3 attempts: {e}")
               else:
                   print(f"⚠️  Retry {attempt+1} failed for {ip}:{port}: {e}")
           finally:
               close_safe_connection(sock, ip, port)
               
           if attempt < 2:
               time.sleep(1)  # Wait before retry
   
   print(f"📡 Block broadcast complete: {success_count}/{min(len(canonical_peers), max_broadcast_peers)} peers reached")

def update_utxo_set(block: Dict):
    """Update UTXO set when a new block is added"""
    with UTXO_LOCK:
        utxos = load_json(UTXO_FILE, [])

        # Check if this block has already been processed
        block_already_processed = any(
            utxo['block_height'] == block['index']
            for utxo in utxos
        )
        if block_already_processed:
            print(f"⚠️  Block {block['index']} already processed for UTXOs, skipping")
            return

        # Process each transaction
        for tx in block['transactions']:
            # Remove spent UTXOs
            for inp in tx.get('inputs', []):
                # Skip coinbase inputs
                if inp.get('txid') != '0' * 64:
                    utxos = [
                        utxo for utxo in utxos
                        if not (utxo['txid'] == inp['txid'] and utxo['index'] == inp.get('index', inp.get('vout', 0)))
                    ]

            # Add new UTXOs only if not already present
            tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
            for idx, output in enumerate(tx.get('outputs', [])):
                key = f"{tx_id}:{idx}"
                if not any(u['txid'] == tx_id and u['index'] == idx for u in utxos):
                    utxos.append({
                        'txid': tx_id,
                        'index': idx,
                        'amount': output['amount'],
                        'address': output['address'],
                        'block_height': block['index']
                    })

        save_json(UTXO_FILE, utxos)
        print(f"💰 UTXO set updated: {len(utxos)} unspent outputs")


def rebuild_utxo_set(blockchain: List[Dict]):
    """Rebuild entire UTXO set from blockchain - used during sync/repair"""
    with UTXO_LOCK:
        utxos = []  # Start fresh, don't load existing
        spent_outputs = set()
        
        # First pass: collect all spent outputs
        for block in blockchain:
            for tx in block.get('transactions', []):
                if 'inputs' in tx:
                    for inp in tx['inputs']:
                        if inp.get('txid') != '0' * 64:  # Not coinbase
                            spent_key = f"{inp.get('txid')}:{inp.get('index') if 'index' in inp else inp.get('vout', 0)}"
                            spent_outputs.add(spent_key)
        
        # Second pass: add all unspent outputs
        for block in blockchain:
            for tx in block.get('transactions', []):
                tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                for idx, output in enumerate(tx.get('outputs', [])):
                    utxo_key = f"{tx_id}:{idx}"
                    if utxo_key not in spent_outputs:
                        utxo = {
                            'txid': tx_id,
                            'index': idx,
                            'amount': output['amount'],
                            'address': output['address'],
                            'block_height': block['index']
                        }
                        utxos.append(utxo)

        save_json(UTXO_FILE, utxos)
        print(f"♻️ Rebuilt UTXO set: {len(utxos)} unspent outputs")

def get_utxos(address: str) -> List[Dict]:
   """Get UTXOs for a specific address"""
   with UTXO_LOCK:
       utxos = load_json(UTXO_FILE, [])
       return [utxo for utxo in utxos if utxo['address'] == address]

def send_transaction(from_addr: str, to_addr: str, amount: int, wallet_file: str):
   """Send a transaction with enhanced format consistency and efficient broadcast"""
   wallet = load_wallet(wallet_file)
   if wallet['address'] != from_addr:
       print("Cannot send from an address not owned by this wallet.")
       return
   
   

   utxos = get_utxos(from_addr)
   print(f"Available UTXOs: {len(utxos)}")
   
   if not utxos:
       print("No UTXOs available for this address.")
       return
   
   # Select UTXOs to cover the amount
   selected = []
   total = 0
   for utxo in utxos:
       selected.append(utxo)
       total += int(utxo['amount'])
       if total >= amount:
           break

   if total < amount:
       print(f"Insufficient funds. Need: {amount/100000000:.8f} CPM, Have: {total/100000000:.8f} CPM")
       return
   
   # Before creating transaction, check if inputs are recently spent
   blockchain = load_json(BLOCKCHAIN_FILE, [])
   recent_blocks = blockchain[-10:] if len(blockchain) >= 10 else blockchain

   recent_spent = set()
   for block in recent_blocks:
        for tx in block.get('transactions', []):
            if tx.get('inputs'):
                for inp in tx['inputs']:
                    if inp.get('txid') != '0' * 64:
                        recent_spent.add(f"{inp['txid']}:{inp.get('index', 0)}")

    # Check selected UTXOs against recent spends
   for utxo in selected:
        utxo_key = f"{utxo['txid']}:{utxo['index']}"
        if utxo_key in recent_spent:
            print(f"⚠️  WARNING: UTXO {utxo_key} was recently spent! Possible double-spend risk.")
            return

   # Create transaction inputs and outputs with consistent format
   inputs = [{"txid": utxo['txid'], "index": utxo['index']} for utxo in selected]
   outputs = [{"address": to_addr, "amount": amount}]  # Use 'address' consistently
   
   # Add change output if needed
   if total > amount:
       change = total - amount
       outputs.append({"address": from_addr, "amount": change})

   # Sign transaction
   tx_data = json.dumps({"inputs": inputs, "outputs": outputs}, sort_keys=True)
   signature = sign_data(wallet['private_key'], tx_data)

   tx = {
       "inputs": inputs,
       "outputs": outputs,
       "public_key": wallet['public_key'],
       "signature": signature
   }

   # Calculate transaction ID
   tx_id = double_sha256(json.dumps(tx, sort_keys=True))

   # Print transaction details
   print("\n" + "="*50)
   print("🔄 TRANSACTION CREATED")
   print("="*50)
   print(f"📋 Transaction ID: {tx_id}")
   print(f"💸 From: {from_addr}")
   print(f"💰 To: {to_addr}")
   print(f"💵 Amount: {amount/100000000:.8f} CPM")
   if total > amount:
       print(f"🔄 Change: {(total-amount)/100000000:.8f} CPM")
   print(f"💳 Fee: 0.00000000 CPM")
   print("="*50)

   # Efficient peer management - get peers ONCE
   print("🔍 Discovering network peers...")
   with PEERS_LOCK:
       peers = load_json(PEERS_FILE, HARDCODED_SEEDS)
       # Ensure all peers use canonical addresses and skip self
       canonical_peers = []
       for peer in peers:
           if isinstance(peer, (list, tuple)) and len(peer) == 2:
               canonical_peer = get_canonical_peer_address(peer[0], peer[1])
               if is_self_peer(canonical_peer[0]):
                   continue
               canonical_peers.append(canonical_peer)

   # Try to discover more peers ONCE
   if canonical_peers:
       print(f"📡 Expanding peer network from {len(canonical_peers)} known peers...")
       expanded_peers = safe_discover_peers(canonical_peers)
       # Filter out self peers from expanded list
       canonical_peers = [p for p in expanded_peers if not is_self_peer(p[0])]
   
   print(f"🌐 Found {len(canonical_peers)} total peers for broadcast")
   
   # Efficient broadcast - each peer contacted ONCE
   broadcast_results = {"success": 0, "failed": 0, "errors": []}
   max_broadcast_attempts = min(len(canonical_peers), 8)  # Limit to 8 peers max
   
   print(f"📡 Broadcasting transaction to {max_broadcast_attempts} peers...")
   
   for ip, port in canonical_peers[:max_broadcast_attempts]:
       # Skip self
       if is_self_peer(ip):
           continue
       sock = create_safe_connection(ip, port, timeout=10)
       if not sock:
           broadcast_results["failed"] += 1
           broadcast_results["errors"].append(f"{ip}:{port} - Connection failed")
           continue

       try:
           message = {"type": "transaction", "data": tx}
           sock.sendall(json.dumps(message).encode())
           broadcast_results["success"] += 1
           print(f"✅ Sent to {ip}:{port}")
       except Exception as e:
           broadcast_results["failed"] += 1
           broadcast_results["errors"].append(f"{ip}:{port} - {str(e)}")
           print(f"❌ Failed to send to {ip}:{port}: {e}")
       finally:
           close_safe_connection(sock, ip, port)

   # Clear broadcast summary
   print("\n" + "="*50)
   print("📡 BROADCAST SUMMARY")
   print("="*50)
   print(f"✅ Successful: {broadcast_results['success']} peers")
   print(f"❌ Failed: {broadcast_results['failed']} peers")
   
   if broadcast_results["success"] > 0:
       print(f"🎉 Transaction successfully broadcast to network!")
       print(f"⏳ Transaction will be included in the next mined block")
       print(f"🔍 Track status: python3 cyphermint.py status --txid {tx_id}")
       
       # Add transaction to local mempool for tracking
       mempool = load_json(MEMPOOL_FILE, [])
       mempool.append(tx)
       save_json(MEMPOOL_FILE, mempool)
       print(f"📝 Added to local mempool for tracking")
       
   else:
       print(f"❌ Transaction broadcast FAILED - No peers reachable")
       print(f"💡 Network may be down. Try again later when peers are online.")
       
       # Show specific errors
       if broadcast_results["errors"]:
           print(f"\n🔍 Error details:")
           for error in broadcast_results["errors"][:3]:  # Show first 3 errors
               print(f"   • {error}")
   
   print("="*50)

def get_balance(address: str) -> int:
    """Get balance for address with consistent transaction format handling"""
    # First try UTXO set (faster)
    with UTXO_LOCK:
        utxos = load_json(UTXO_FILE, [])
        utxo_balance = sum(utxo['amount'] for utxo in utxos if utxo['address'] == address)
    
    # For now, trust the UTXO set if it exists
    if len(utxos) > 0:
        return utxo_balance
    
    # Only rebuild if UTXO set is completely empty
    if len(utxos) == 0:
        print("📭 Empty UTXO set - rebuilding from blockchain...")
        with BLOCKCHAIN_LOCK:
            blockchain = load_json(BLOCKCHAIN_FILE, [])
        rebuild_utxo_set(blockchain)
        
        # Recalculate after rebuild
        with UTXO_LOCK:
            utxos = load_json(UTXO_FILE, [])
            utxo_balance = sum(utxo['amount'] for utxo in utxos if utxo['address'] == address)
    
    return utxo_balance

def get_blockchain_info() -> Dict:
   """Get current blockchain status"""
   with BLOCKCHAIN_LOCK:
       blockchain = load_json(BLOCKCHAIN_FILE, [])
   
   with PEERS_LOCK:
       peers = load_json(PEERS_FILE, [])
   
   mempool = load_json(MEMPOOL_FILE, [])
   
   with UTXO_LOCK:
       utxos = load_json(UTXO_FILE, [])
   
   if not blockchain:
       return {'error': 'No blockchain found'}
   
   latest_block = blockchain[-1]
   
   return {
       'height': len(blockchain),
       'latest_hash': latest_block.get('hash', 'Unknown'),
       'latest_timestamp': latest_block.get('timestamp', 0),
       'known_peers': len(peers),
       'peer_list': peers,
       'mempool_size': len(mempool),
       'utxo_count': len(utxos),
       'total_work': calculate_chain_work(blockchain),
       'network_health': consensus_analytics.get_network_health_score(),
       'witness_status': witness_node.witness_status,
       'witness_weight': witness_node.calculate_witness_weight()
   }

def check_sync_status(target_peers: List[Tuple[str, int]]) -> Dict:
   """Check sync status with other peers"""
   local_info = get_blockchain_info()
   peer_status = []
   
   # Ensure all peers use canonical addresses and exclude self
   canonical_peers = []
   for peer in target_peers:
       if isinstance(peer, (list, tuple)) and len(peer) == 2:
           canonical_peer = get_canonical_peer_address(peer[0], peer[1])
           if is_self_peer(canonical_peer[0]):
               continue
           canonical_peers.append(canonical_peer)
   
   for ip, port in canonical_peers[:5]:  # Limit to 5 peers for status check
       sock = create_safe_connection(ip, port, timeout=10)
       if not sock:
           peer_status.append({
               'peer': f"{ip}:{port}",
               'error': 'Connection failed',
               'synced': False
           })
           continue
           
       try:
           # Request blockchain info
           request = {'type': 'get_info'}
           sock.sendall(json.dumps(request).encode())
           
           sock.settimeout(10)
           data = sock.recv(BUFFER_SIZE)
           if data:
               response = json.loads(data.decode())
               if response.get('type') == 'info_response':
                   peer_data = response.get('data', {})
                   peer_status.append({
                       'peer': f"{ip}:{port}",
                       'height': peer_data.get('height', 0),
                       'latest_hash': peer_data.get('latest_hash', 'Unknown'),
                       'synced': peer_data.get('height') == local_info['height'] and 
                                peer_data.get('latest_hash') == local_info['latest_hash']
                   })
                   
       except Exception as e:
           peer_status.append({
               'peer': f"{ip}:{port}",
               'error': str(e),
               'synced': False
           })
       finally:
           close_safe_connection(sock, ip, port)
   
   return {
       'local': local_info,
       'peers': peer_status
   }

def check_transaction_status(txid: str) -> Dict:
   """Check if a transaction has been mined"""
   with BLOCKCHAIN_LOCK:
       blockchain = load_json(BLOCKCHAIN_FILE, [])
   
   for block in blockchain:
       for tx in block.get('transactions', []):
           # Calculate transaction ID
           tx_data = json.dumps(tx, sort_keys=True)
           calculated_txid = double_sha256(tx_data)
           
           if calculated_txid == txid:
               return {
                   'status': 'confirmed',
                   'block_height': block['index'],
                   'block_hash': block['hash'],
                   'transaction': tx
               }
   
   # Check mempool
   mempool = load_json(MEMPOOL_FILE, [])
   for tx in mempool:
       tx_data = json.dumps(tx, sort_keys=True)
       calculated_txid = double_sha256(tx_data)
       
       if calculated_txid == txid:
           return {
               'status': 'pending',
               'transaction': tx
           }
   
   return {'status': 'not_found'}

def start_peer_server(chain_ref: List[Dict]):
   """ENHANCED: Start peer server with better connection handling"""
   def run():
       with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
           s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
           s.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)  # Keep connections alive
           
           # Bind to all interfaces
           s.bind(('0.0.0.0', PEER_PORT))
           s.listen(20)  # Increased backlog for better connection handling
           
           print(f"🌐 CypherMint server listening on 0.0.0.0:{PEER_PORT}")
           print(f"🚀 ENHANCED CONSENSUS enabled")
           print(f"⭐ Witness node support active")
           print(f"🔧 Adaptive consensus intervals enabled")
           print(f"🌍 Bootstrap seeds available:")
           for ip, port in HARDCODED_SEEDS:
               print(f"   📡 {ip}:{port}")
               
           while True:
               try:
                   conn, addr = s.accept()
                   print(f"🔗 New connection from {addr[0]}:{addr[1]}")
                   
                   # Get fresh blockchain data for each request
                   with BLOCKCHAIN_LOCK:
                       current_chain = load_json(BLOCKCHAIN_FILE, [])
                   
                   # Handle each connection in a separate thread
                   threading.Thread(
                       target=handle_peer_enhanced, 
                       args=(conn, current_chain, addr), 
                       daemon=True
                   ).start()
                   
               except Exception as e:
                   print(f"Peer server error: {e}")
   
   threading.Thread(target=run, daemon=True).start()

def process_backfill_once(state_chain_path: str) -> None:
    try:
        missing = BACKFILL_QUEUE.pop()
    except KeyError:
        return
    fetched = None
    for ip, port in HARDCODED_SEEDS:
        fetched = request_block_by_hash(ip, port, missing)
        if fetched:
            break
    if not fetched:
        BACKFILL_QUEUE.add(missing)
        return
    with BLOCKCHAIN_LOCK:
        chain = load_json(BLOCKCHAIN_FILE, [])
    validate_and_add_block(fetched, chain)
    parent_hash = (fetched.get('hash') or fetched.get('block_hash'))
    for h, ob in list(ORPHAN_BLOCKS.items()):
        if ob.get('previous_hash') == parent_hash:
            ORPHAN_BLOCKS.pop(h, None)
            with BLOCKCHAIN_LOCK:
                chain2 = load_json(BLOCKCHAIN_FILE, [])
            validate_and_add_block(ob, chain2)

def backfill_worker():
    while True:
        process_backfill_once(BLOCKCHAIN_FILE)
        time.sleep(1.0)

def start_backfill_worker():
    t = threading.Thread(target=backfill_worker, name='backfill', daemon=True)
    t.start()



def register_connection(conn, addr):
    """Register a new connection (placeholder)"""
    return f"{addr[0]}:{addr[1]}"

def handle_peer_enhanced(conn, chain: List[Dict], addr):
    """Enhanced peer handler with witness node support and automatic peer sharing"""
   
    ip = addr[0]
    
    # Rate limit check
    if not attack_prevention.rate_limit_connection(ip):
        conn.close()
        return
    
    # Register connection
    conn_id = register_connection(conn, addr)
    
    # NEW: Automatic peer sharing on connection (prefer LIVE peers)
    #if addr[0] not in ['127.0.0.1', '::1', 'localhost']:
     #   with PEERS_LOCK:
      #      our_peers = load_json(PEERS_FILE, [])

       # with LIVE_PEERS_LOCK:
        #    live_list = list(LIVE_PEERS_CACHE)

        # prefer live; fall back to known
        #source = live_list if live_list else our_peers

        # Filter out self and the connecting peer
        #peers_to_share = []
        #for p in source:
          #  if isinstance(p, (list, tuple)) and len(p) >= 2:
         #       ip, prt = get_canonical_peer_address(p[0], p[1])
          #      if not is_self_peer(ip) and ip != addr[0]:
           #         peers_to_share.append((ip, prt))

        #if peers_to_share:
         #   peer_share = {'type': 'peer_announcement', 'data': peers_to_share}
          #  try:
           #     conn.sendall(json.dumps(peer_share).encode())
            #    print(f"📡 Automatically shared {len(peers_to_share)} peers (live-first) with {addr[0]}:{addr[1]}")
            #except:
             #   pass

    try:
       conn.settimeout(300)
       
       data = conn.recv(BUFFER_SIZE)
       if not data:
           return
           
       message = json.loads(data.decode())
       message_type = message.get('type')
       
       print(f"📡 Received {message_type} from {addr[0]}:{addr[1]} (client port: {addr[1]})")
       
       if message_type == 'get_chain' or message_type == 'get_blockchain':
            with BLOCKCHAIN_LOCK:
                current_chain = load_json(BLOCKCHAIN_FILE, [])
            
            response = {'type': 'full_chain', 'data': current_chain}
            response_json = json.dumps(response)
            response_bytes = response_json.encode()
            
            # Send in chunks but DON'T close connection
            print(f"📤 Sending {len(response_bytes)} bytes to {addr[0]}:{addr[1]}")
            
            # Send size first
            size_bytes = struct.pack('!I', len(response_bytes))
            conn.sendall(size_bytes)
            
            # Send data in chunks
            bytes_sent = 0
            chunk_size = 65536  # 64KB chunks
            
            while bytes_sent < len(response_bytes):
                chunk = response_bytes[bytes_sent:bytes_sent + chunk_size]
                conn.sendall(chunk)
                bytes_sent += len(chunk)
                
            print(f"✅ Sent {bytes_sent} bytes successfully")

            # Keep connection open for ACK or additional requests
            conn.settimeout(10)
            try:
                ack = conn.recv(1024)
                if ack:
                    print(f"✅ Received ACK from {addr[0]}:{addr[1]}")
            except socket.timeout:
                pass

       elif message_type == 'get_peers':
                # Only send peers when explicitly requested
                with PEERS_LOCK:
                    peers = load_json(PEERS_FILE, [])
                
                response = {'type': 'peer_list', 'data': peers}
                conn.sendall(json.dumps(response).encode())
                print(f"📤 Sent peer list to {addr[0]}:{addr[1]}")
            
       elif message_type == 'get_headers':
        # Send just headers
        start = message.get('data', {}).get('start_height', 0)
        with BLOCKCHAIN_LOCK:
            chain = load_json(BLOCKCHAIN_FILE, [])
            headers = [BlockHeader.extract_header(block) for block in chain[start:]]
        
        response = {'type': 'headers_response', 'data': headers}
        conn.sendall(json.dumps(response).encode())
    
       elif message_type == 'get_snapshot':
            # Send latest UTXO snapshot
            height = message.get('data', {}).get('height')
            if os.path.exists(f'snapshot_{height}.json'):
                snapshot = load_json(f'snapshot_{height}.json')
                response = {'type': 'snapshot_response', 'data': snapshot}
                conn.sendall(json.dumps(response).encode())
                
       elif message_type == 'peer_announcement' or message_type == 'peer_exchange':
           # NEW: Handle incoming peer announcements
           new_peers = message.get('data', [])
           if new_peers:
               with PEERS_LOCK:
                   current_peers = load_json(PEERS_FILE, [])
                   added_count = 0
                   for peer in new_peers:
                       if isinstance(peer, (list, tuple)) and len(peer) == 2:
                           canonical_peer = get_canonical_peer_address(peer[0], peer[1])
                           if not is_self_peer(canonical_peer[0]) and canonical_peer not in current_peers:
                               current_peers.append(canonical_peer)
                               added_count += 1
                   
                   if added_count > 0:
                       clean_peers = sanitize_peer_list(current_peers)
                       save_json(PEERS_FILE, clean_peers)
                       print(f"📡 Added {added_count} new peers from {addr[0]}")
       
       elif message_type == 'get_block_by_hash':
           q = message.get('data') or {}
           want = (q.get('hash') or '').strip()
           blk = None
           if want:
               with BLOCKCHAIN_LOCK:
                   current_chain = load_json(BLOCKCHAIN_FILE, [])
               for b in current_chain:
                   if (b.get('hash') or b.get('block_hash')) == want:
                       blk = b
                       break
           response = {'type': 'block_response', 'data': blk}
           conn.sendall(json.dumps(response).encode())

               
       elif message_type == 'new_block':
            new_block = message.get('data')
            if new_block:
                print(f"📥 Received new block {new_block.get('index', '?')} from {addr[0]}:{addr[1]}")
                with BLOCKCHAIN_LOCK:
                    current_chain = load_json(BLOCKCHAIN_FILE, [])
                    
                    # CRITICAL FIX: Check for duplicate transactions in recent blocks
                    recent_blocks_to_check = 10
                    existing_tx_ids = set()
                    
                    # Get starting point for recent block check
                    start_index = max(0, len(current_chain) - recent_blocks_to_check)
                    
                    # Collect transaction IDs from recent blocks
                    for i in range(start_index, len(current_chain)):
                        block = current_chain[i]
                        for tx in block.get('transactions', []):
                            # Skip coinbase transactions
                            if tx.get('type') == 'coinbase':
                                continue
                            tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                            existing_tx_ids.add(tx_id)
                    
                    # Check new block for duplicates
                    block_has_duplicates = False
                    for tx in new_block.get('transactions', []):
                        # Skip coinbase
                        if tx.get('type') == 'coinbase':
                            continue
                        
                        tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                        if tx_id in existing_tx_ids:
                            print(f"❌ Block {new_block['index']} contains duplicate tx from recent blocks: {tx_id[:16]}...")
                            block_has_duplicates = True
                            break
                    
                    if not block_has_duplicates and validate_and_add_block(new_block, current_chain):
                        print(f"✅ Block {new_block['index']} accepted")
                        
                        # CRITICAL FIX: Remove confirmed transactions from mempool
                        mempool = load_json(MEMPOOL_FILE, [])
                        confirmed_tx_ids = set()
                        
                        # Get all transaction IDs from the accepted block
                        for tx in new_block.get('transactions', []):
                            tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                            confirmed_tx_ids.add(tx_id)
                        
                        # Remove confirmed transactions from mempool
                        remaining_mempool = []
                        for mem_tx in mempool:
                            mem_tx_id = mem_tx.get('txid') or double_sha256(json.dumps(mem_tx, sort_keys=True))
                            if mem_tx_id not in confirmed_tx_ids:
                                remaining_mempool.append(mem_tx)
                        
                        save_json(MEMPOOL_FILE, remaining_mempool)
                        print(f"🧹 Removed {len(mempool) - len(remaining_mempool)} confirmed transactions from mempool")
                    else:
                        if block_has_duplicates:
                            print(f"❌ Block {new_block['index']} rejected - contains duplicate transactions")
                        else:
                            print(f"❌ Block {new_block['index']} rejected - validation failed")
                   
       elif message_type == 'get_info':
           # Send blockchain info including witness status
           info = get_blockchain_info()
           response = {'type': 'info_response', 'data': info}
           conn.sendall(json.dumps(response).encode())
           print(f"📤 Sent blockchain info to {addr[0]}:{addr[1]}")
           
       elif message_type == 'transaction':
           tx = message.get('data')
           if tx:
               print(f"📥 Received transaction from {addr[0]}:{addr[1]}")
               # Add to mempool with basic validation
               mempool = load_json(MEMPOOL_FILE, [])
               
               # Simple duplicate check
               tx_id = double_sha256(json.dumps(tx, sort_keys=True))
               existing_tx_ids = [double_sha256(json.dumps(existing_tx, sort_keys=True)) for existing_tx in mempool]
               
               if tx_id not in existing_tx_ids:
                   mempool.append(tx)
                   save_json(MEMPOOL_FILE, mempool)
                   print(f"✅ Transaction {tx_id[:16]}... added to mempool")
               else:
                   print(f"⚠️  Transaction {tx_id[:16]}... already in mempool")

       elif message_type == 'emergency_alert':
            alert = message.get('data')
            if alert:
                print(f"🚨 EMERGENCY ALERT from {addr[0]}: {alert['message']}")
                # Store and propagate alert
                emergency_system.active_alerts[alert['id']] = alert
                emergency_system.save_state()
                # Rebroadcast to other peers
                peers = load_json(PEERS_FILE, [])
                for p_ip, p_port in peers[:10]:  # Limit propagation
                    if (p_ip, p_port) != (addr[0], PEER_PORT):
                        emergency_system.send_emergency_alert(p_ip, p_port, alert)

       elif message_type == 'emergency_checkpoint':
           checkpoint = message.get('data')
           if checkpoint:
               print(f"📍 EMERGENCY CHECKPOINT from {addr[0]}: Block {checkpoint['height']}")
               # Verify and apply checkpoint
               height = checkpoint['height']
               hash = checkpoint['hash']
               if height not in CHECKPOINTS:
                   CHECKPOINTS[height] = hash
                   print(f"✅ Checkpoint applied at height {height}")        
               
    except Exception as e:
        print(f"❌ Peer handling error from {addr}: {e}")
    finally:
        # Graceful shutdown
        try:
            conn.shutdown(socket.SHUT_RDWR)
        except:
            pass
        conn.close()

def validate_and_add_block(new_block: Dict, blockchain: List[Dict]) -> bool:
    """Validate and add a new block with normalization and ancestor backfill."""
    try:
        with BLOCKCHAIN_LOCK:
            current_chain = load_json(BLOCKCHAIN_FILE, [])
            if not current_chain:
                if new_block.get('index') == 0 and new_block.get('previous_hash') == '0'*64:
                    if not new_block.get('hash'):
                        new_block['hash'] = calculate_block_hash(new_block)
                    save_json(BLOCKCHAIN_FILE, [new_block])
                    try:
                        safe_update_utxos(new_block)
                    except Exception:
                        pass
                    return True
                print("❌ First block must be genesis (index 0)")
                return False

            current_chain = sort_and_dedupe_by_index(current_chain)
            tip = current_chain[-1]

            # Straight append
            if (_block_prev_hash_of(new_block) == _block_hash_of(tip) and
                _block_index_of(new_block) == _block_index_of(tip) + 1):
                if not CypherMintValidator.validate_block_header(new_block, tip):
                    return False
                
                if new_block['index'] != len(current_chain):
                    print(f"❌ Block index {new_block['index']} doesn't match expected position {len(current_chain)}")
                    return False

                # Duplicate & double-spend checks against recent history
                recent_blocks_to_check = RECENT_DUP_WINDOW
                existing_tx_ids = set()
                start_index = max(0, len(current_chain) - recent_blocks_to_check)
                for i in range(start_index, len(current_chain)):
                    blk = current_chain[i]
                    for tx in blk.get('transactions', []):
                        if tx.get('type') == 'coinbase':
                            continue
                        tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))
                        existing_tx_ids.add(tx_id)
                recent_spent_inputs = set()
                for i in range(start_index, len(current_chain)):
                    blk = current_chain[i]
                    for tx in blk.get('transactions', []):
                        for inp in tx.get('inputs', []):
                            if len(tx.get('inputs', [])) == 1 and inp.get('txid') == '0'*64:
                                continue
                            input_key = f"{inp.get('txid')}:{inp.get('index', inp.get('vout', 0))}"
                            recent_spent_inputs.add(input_key)
                filtered_txs = []
                rejected_count = 0

                for tx in new_block.get('transactions', []):
                    if tx.get('type') == 'coinbase'or (
                        len(tx.get('inputs', [])) == 1 and tx['inputs'][0].get('txid', '') == '0' * 64
                    ):
                        filtered_txs.append(tx)
                        continue

                    tx_id = tx.get('txid') or double_sha256(json.dumps(tx, sort_keys=True))

                    if tx_id in existing_tx_ids:
                        print(f"❌ Duplicate transaction detected in new block: {tx_id[:16]}...")
                        rejected_count +=1
                        continue

                    is_double_spend = False
                    for inp in tx.get('inputs', []):
                        if len(tx.get('inputs', [])) == 1 and inp.get('txid') == '0'*64:
                            continue
                        input_key = f"{inp.get('txid')}:{inp.get('index', inp.get('vout', 0))}"
                        if input_key in recent_spent_inputs:
                            print(f"🚫 Filtering double-spend input in block {new_block.get('index')}: {input_key}")
                            rejected_count += 1
                            is_double_spend = True
                            break
                        
                        if is_double_spend:
                            continue
                    
                if rejected_count > 0:
                    print(f"🧹 Block {new_block.get('index')} filtered {rejected_count} transaction(s)")
                    new_block = dict(new_block)  # avoid mutating shared refs
                    new_block['transactions'] = filtered_txs
                    # IMPORTANT: recompute Merkle root and hash since the tx set changed
                    try:
                        new_block['merkle_root'] = MerkleTree.calculate_merkle_root(new_block['transactions'])
                    except Exception:
                        # Fallback if MerkleTree isn't used consistently elsewhere
                        new_block['merkle_root'] = hashlib.sha256(
                            json.dumps(new_block['transactions'], sort_keys=True).encode()
                        ).hexdigest()
                    new_block['hash'] = calculate_block_hash(new_block)   

                current_chain.append(new_block)
                save_json(BLOCKCHAIN_FILE, current_chain)
                try:
                    safe_update_utxos(new_block)
                except Exception:
                    pass
                return True

            # Same-height competition -> replace tip if higher work and linked
            if _block_index_of(new_block) == _block_index_of(tip):
                prev = current_chain[-2] if len(current_chain) >= 2 else None
                if prev and _block_prev_hash_of(new_block) == _block_hash_of(prev):
                    new_w = _per_block_work(new_block.get('bits', MAX_TARGET))
                    old_w = _per_block_work(tip.get('bits', MAX_TARGET))
                    if new_w > old_w:
                        current_chain[-1] = new_block
                        save_json(BLOCKCHAIN_FILE, current_chain)
                        try:
                            rebuild_utxo_set(current_chain)
                        except Exception:
                            pass
                        print("🔁 Replaced same-height tip with higher-work block")
                        return True
                    else:
                        print("ℹ️ Keeping current tip (higher/equal work)")
                        return False

            # Unknown parent -> store as orphan and queue backfill
            existing_hashes = {(_block_hash_of(b)) for b in current_chain}
            parent_hash = _block_prev_hash_of(new_block)
            if parent_hash not in existing_hashes:
                h = _block_hash_of(new_block)
                if h:
                    ORPHAN_BLOCKS[h] = new_block
                if parent_hash:
                    BACKFILL_QUEUE.add(parent_hash)
                print("ℹ️ Queued ancestor for backfill; will retry after fetch")
                return False

            # Reorg one-deep off ancestor tail if better work
            index_map = {(_block_hash_of(b)): i for i, b in enumerate(current_chain)}
            fork_idx = index_map[parent_hash]
            expected_new_index = _block_index_of(current_chain[fork_idx]) + 1
            if _block_index_of(new_block) != expected_new_index:
                print(f"❌ Fork candidate has wrong index at {expected_new_index}")
                return False

            current_suffix = current_chain[fork_idx+1:]
            cur_work = sum(_per_block_work(b.get('bits', MAX_TARGET)) for b in current_suffix)
            new_work = _per_block_work(new_block.get('bits', MAX_TARGET))
            if new_work <= cur_work:
                print("ℹ️ New branch does not exceed current work; keeping current")
                return False

            current_chain = current_chain[:fork_idx+1] + [new_block]
            save_json(BLOCKCHAIN_FILE, current_chain)
            try:
                rebuild_utxo_set(current_chain)
            except Exception:
                pass
            print(f"🔁 Reorged at height {fork_idx}; new branch adopted")
            return True
    except Exception as e:
        print(f"❌ validate_and_add_block error: {e}")
        return False

def validate_checkpoint(block: Dict) -> bool:
   """Validate block against known checkpoints"""
   if block['index'] in CHECKPOINTS and CHECKPOINTS[block['index']] is not None:
       return block['hash'] == CHECKPOINTS[block['index']]
   return True

def update_checkpoint(block: Dict):
   """Update checkpoint if this is a checkpoint block"""
   if block['index'] in CHECKPOINTS:
       CHECKPOINTS[block['index']] = block['hash']
       print(f"📍 Checkpoint updated at height {block['index']}")

def prune_blockchain(blockchain: List[Dict]) -> List[Dict]:
   """Prune old blocks while keeping UTXO data"""
   if len(blockchain) <= PRUNE_KEEP_RECENT:
       return blockchain
   
   # Keep genesis block and recent blocks
   pruned_chain = [blockchain[0]]  # Genesis
   pruned_chain.extend(blockchain[-PRUNE_KEEP_RECENT:])  # Recent blocks
   
   # Also keep checkpoint blocks
   for height, hash_val in CHECKPOINTS.items():
       if hash_val and height < len(blockchain) and height not in [b['index'] for b in pruned_chain]:
           pruned_chain.append(blockchain[height])
   
   # Sort by height
   pruned_chain.sort(key=lambda b: b['index'])
   
   return pruned_chain

def load_existing_genesis() -> Dict:
   """Load existing genesis block and convert to blockchain format"""
   genesis_data = load_json('genesis_block.json', None)
   if not genesis_data:
       print("Error: genesis_block.json not found. Please create it first using your genesis script.")
       sys.exit(1)
   
   print(f"Loading genesis block from genesis_block.json")
   
   # Always ensure proper blockchain format
   genesis_block = {
       'version': genesis_data.get('version', 1),
       'index': genesis_data.get('height', 0),  # Use 'height' or default to 0
       'timestamp': genesis_data.get('timestamp', int(time.time())),
       'previous_hash': genesis_data.get('prev_hash', '0' * 64),
       'merkle_root': genesis_data.get('merkle_root', ''),
       'bits': genesis_data.get('bits', MAX_TARGET),
       'nonce': genesis_data.get('nonce', 0),
       'hash': genesis_data.get('hash', ''),
       'transactions': genesis_data.get('transactions', [])
   }
   
   # If no hash exists, calculate it
   if not genesis_block['hash']:
       genesis_block['hash'] = calculate_block_hash(genesis_block)
   
   print(f"Genesis block loaded - Hash: {genesis_block['hash']}")
   print(f"Genesis block index: {genesis_block['index']}")
   
   return genesis_block

def setup_upnp_port():
    """Automatically open port 8334 using UPnP"""
    try:
        import miniupnpc
        upnp = miniupnpc.UPnP()
        upnp.discoverdelay = 200
        
        devices = upnp.discover()
        if devices:
            upnp.selectigd()
            external_ip = upnp.externalipaddress()
            
            # Try to add port mapping
            result = upnp.addportmapping(
                PEER_PORT, 'TCP', upnp.lanaddr, PEER_PORT,
                'CypherMint P2P', ''
            )
            
            if result:
                print(f"✅ UPnP: Automatically opened port {PEER_PORT}")
                print(f"📡 External IP: {external_ip}")
                # CRITICAL FIX: Add external IP to LOCAL_IPS
                if external_ip:
                    LOCAL_IPS.add(external_ip)
                    # Also cache it for later reference
                    save_json('external_ip_cache.json', {'ip': external_ip, 'timestamp': time.time()})
                return external_ip
            else:
                print(f"⚠️  UPnP: Could not open port {PEER_PORT}")
        else:
            print("⚠️  UPnP: No devices found")
    except ImportError:
        print("⚠️  UPnP: miniupnpc not installed (pip install miniupnpc)")
    except Exception as e:
        print(f"⚠️  UPnP setup failed: {e}")
    
    return None
    
def cleanup_development_files():
   """Development utility - removes all blockchain data files"""
   if not DEVELOPMENT_MODE:
       print("Cleanup disabled in production mode")
       return
   
   files_to_clean = [
       BLOCKCHAIN_FILE,
       WALLET_FILE_DEFAULT,
       PEERS_FILE,
       MEMPOOL_FILE,
       UTXO_FILE,
       CONSENSUS_ANALYTICS_FILE,
       WITNESS_FILE,
       'genesis_block.json',
       'genesis_puzzle_state.json',
       'network_config.json',
       'known_hosts',
       'debug.log',
       'pastebin_url.txt'
   ]
   
   removed_count = 0
   for filename in files_to_clean:
       try:
           if os.path.exists(filename):
               os.remove(filename)
               print(f"🗑️  Deleted {filename}")
               removed_count += 1
       except Exception as e:
           print(f"Error deleting {filename}: {e}")
   
   print(f"🧹 Cleanup complete. Removed {removed_count} files.")
   print("📝 Ready for fresh start - regenerate genesis block now!")

# Main execution
if __name__ == '__main__':
   parser = argparse.ArgumentParser(description='CypherMint blockchain - ENHANCED CONSENSUS with Witness Nodes')
   parser.add_argument('--wallet', default=WALLET_FILE_DEFAULT, help='Wallet file')
   
   # Add send command and update choices
   command_choices = ['mine', 'wallet', 'balance', 'validate', 'convert', 'send', 'status', 'info', 'repair']
   if DEVELOPMENT_MODE:
       command_choices.append('cleanup')
   
   parser.add_argument('command', choices=command_choices, help='Command to execute')
   parser.add_argument('--address', help='CypherMint address')
   parser.add_argument('--generate', action='store_true', help='Generate new wallet')
   parser.add_argument('--seed', action='store_true', help='Run as seed node')
   parser.add_argument('--utxos', action='store_true', help='Show UTXOs when checking balance')
   parser.add_argument('--to', help='Destination address for send command')
   parser.add_argument('--amount', type=Decimal, help='Amount for send command')
   parser.add_argument('--txid', help='Transaction ID for status command')
   parser.add_argument('--treasure', action='store_true', help='Check treasure hunt status')

   
   args = parser.parse_args()
   
   # Development command handling
   if DEVELOPMENT_MODE and args.command == 'cleanup':
       cleanup_development_files()
       sys.exit(0)
   
   if args.command == 'convert':
       # Convert genesis_block.json to blockchain.json format
       genesis_block = load_existing_genesis()
       blockchain = [genesis_block]
       save_json(BLOCKCHAIN_FILE, blockchain)
       print(f"Converted genesis_block.json to blockchain.json format")
       print(f"Genesis hash: {genesis_block.get('hash', 'Unknown')}")
    
   elif args.command == "repair":
    cmd_repair_duplicate_heights()
    sys.exit(0)


   elif args.command == 'wallet':
       if args.generate:
           wallet = create_wallet(args.wallet)
           print(f"New wallet created")
       else:
           wallet = load_wallet(args.wallet)
       print(f"Address: {wallet['address']}")
       print(f"Public key: {wallet['public_key']}")
       
   elif args.command == 'balance':
       if not args.address:
           print("Address required")
           sys.exit(1)
       balance = get_balance(args.address)
       print(f"Balance: {balance / 100000000:.8f} CPM")
       
       if args.utxos:
           utxos = get_utxos(args.address)
           print(f"\nUTXOs ({len(utxos)}):")
           for utxo in utxos:
               print(f"  txid: {utxo['txid'][:16]}... | index: {utxo['index']} | amount: {utxo['amount'] / 100000000:.8f} CPM | block: {utxo.get('block_height', '?')}")
       
   elif args.command == 'send':
       if not (args.address and args.to and args.amount):
           print("From address, to address, and amount are required.")
           print("Usage: python3 cyphermint.py send --address FROM --to TO --amount AMOUNT")
           sys.exit(1)
       send_transaction(args.address, args.to, int(args.amount * Decimal('100000000')), args.wallet)
       
   elif args.command == 'status':
       if not args.txid:
           print("Transaction ID required.")
           print("Usage: python3 cyphermint.py status --txid TRANSACTION_ID")
           sys.exit(1)
       
       status = check_transaction_status(args.txid)
       
       if status['status'] == 'confirmed':
           print(f"✅ Transaction CONFIRMED")
           print(f"📦 Block Height: {status['block_height']}")
           print(f"🔗 Block Hash: {status['block_hash'][:16]}...")
           print(f"💰 Transaction included in blockchain")
       elif status['status'] == 'pending':
           print(f"⏳ Transaction PENDING")
           print(f"📋 Transaction is in mempool waiting to be mined")
       else:
           print(f"❌ Transaction NOT FOUND")
           print(f"💡 Check the transaction ID or wait for network sync")
       
   elif args.command == 'info':
       if args.address:
           # Show info for specific address
           balance = get_balance(args.address)
           utxos = get_utxos(args.address)
           print(f"Address: {args.address}")
           print(f"Balance: {balance / 100000000:.8f} CPM")
           print(f"UTXOs: {len(utxos)}")
       else:
           # Show blockchain and sync info
           blockchain_info = get_blockchain_info()
           
           print("🔗 CypherMint Network Status:")
           print(f"  Height: {blockchain_info['height']}")
           print(f"  Latest Hash: {blockchain_info['latest_hash'][:16]}...")
           print(f"  Mempool: {blockchain_info['mempool_size']} transactions")
           print(f"  UTXOs: {blockchain_info['utxo_count']}")
           print(f"  Known Peers: {blockchain_info['known_peers']}")
           print(f"  Network Health: {blockchain_info['network_health']:.0f}/100")
           print(f"  Witness Status: {'ACTIVE' if blockchain_info['witness_status'] else 'BUILDING'}")
           print(f"  Witness Weight: {blockchain_info['witness_weight']:.2f}")
           print(f"\n📡 Enhanced Features:")
           print(f"  🔄 Adaptive Consensus: ENABLED")
           print(f"  ⭐ Witness Nodes: ENABLED")
           print(f"  🧠 Fork Memory: ENABLED")
           # Genesis puzzle disabled
           print(f"  🎯 Genesis Puzzle: ACTIVE")
           print(f"  🔧 UTXO Auto-Repair: ENABLED")
           
           current_interval = adaptive_consensus.get_consensus_interval()
           print(f"\n⚙️  Current Settings:")
           print(f"  Consensus Interval: {current_interval}s (adaptive)")
           print(f"  Peer Discovery: {BASE_PEER_BROADCAST_INTERVAL}s")
           print(f"  Mining Sync: {MINING_SYNC_INTERVAL}s")
           
           if blockchain_info['peer_list']:
               print(f"\n📡 Sync Status with Peers:")
               sync_status = check_sync_status(blockchain_info['peer_list'])
               
               for peer_info in sync_status['peers']:
                   if 'error' in peer_info:
                       print(f"  ❌ {peer_info['peer']}: {peer_info['error']}")
                   else:
                       status = "✅ SYNCED" if peer_info['synced'] else "⚠️  OUT OF SYNC"
                       print(f"  {status} {peer_info['peer']}: Height {peer_info['height']}")
                       if not peer_info['synced']:
                           print(f"     Their hash: {peer_info['latest_hash'][:16]}...")
                           print(f"     Our hash:   {sync_status['local']['latest_hash'][:16]}...")
           else:
               print(f"\n📡 No peers available for sync check")
               print(f"💡 Start other nodes or check network connectivity")
               
   elif args.command == 'info' and args.treasure:
    blockchain = load_json(BLOCKCHAIN_FILE, [])
    print("\n🧩 CYPHERMINT TREASURE HUNT STATUS")
    print("="*50)
    
    clue_blocks = [2016, 4032, 210000]
    current_height = len(blockchain)
    
    for clue_height in clue_blocks:
        if current_height >= clue_height:
            # Find and display the clue
            if clue_height < len(blockchain):
                block = blockchain[clue_height]
                for tx in block.get('transactions', []):
                    if tx.get('type') == 'coinbase' and 'message' in tx:
                        print(f"📍 Clue at block {clue_height}: {tx['message']}")
                        break
        else:
            blocks_until = clue_height - current_height
            print(f"⏳ Clue at block {clue_height}: {blocks_until} blocks remaining")
    
    print("\n💡 Hint: The genesis private key vulnerability is the answer")
    print("🎯 Find how the creator's identity created the first coins")
           
   elif args.command == 'mine':
       if not args.address:
           print("Address required for mining")
           sys.exit(1)
       
       print("🚀 Starting CypherMint ENHANCED Mining Node")
       print("=" * 80)
       print("📋 ENHANCED FEATURES:")
       print(f"   🔄 Adaptive consensus intervals")
       print(f"   ⭐ Witness node weight system")
       print(f"   🧠 Fork memory with chain quality scoring")
       # Genesis puzzle disabled for now
       print(f"   🎯 Genesis puzzle ACTIVE")
       print(f"   📊 Network health monitoring")
       print(f"   🔧 UTXO auto-repair system")
       print(f"   📍 Checkpoint validation")
       print(f"   ✂️  Chain pruning support")
       print("=" * 80)
       
       start_mining(args.address, args.seed)
       
   elif args.command == 'validate':
       with BLOCKCHAIN_LOCK:
           blockchain = load_json(BLOCKCHAIN_FILE, [])
       
       print("🔍 Validating blockchain...")
       
       # Full blockchain validation
       if is_valid_chain(blockchain):
           print("✅ Blockchain structure is valid")
       else:
           print("❌ Blockchain structure is invalid")
           print("💡 Try running 'cleanup' and restart from genesis")
           sys.exit(1)
       
       # UTXO consistency validation
       if UTXOValidator.validate_utxo_consistency():
           print("✅ UTXO set is consistent with blockchain")
       else:
           print("⚠️  UTXO set inconsistency detected")
           print("🔧 Auto-repairing UTXO set...")
           if UTXOValidator.repair_utxo_set():
               print("✅ UTXO set repaired successfully")
           else:
               print("❌ UTXO repair failed - manual intervention needed")
       
       # Check for duplicate transactions
       print("🔍 Checking for duplicate transactions...")
       duplicates_found = False
       tx_counts = {}
       
       for i, block in enumerate(blockchain):
           for tx in block.get('transactions', []):
               tx_data = json.dumps(tx, sort_keys=True)
               txid = double_sha256(tx_data)
               if txid in tx_counts:
                   print(f"❌ DUPLICATE TRANSACTION: {txid[:16]}... in blocks {tx_counts[txid]} and {i}")
                   duplicates_found = True
               else:
                   tx_counts[txid] = i
       
       if not duplicates_found:
           print("✅ No duplicate transactions found")
       
       # Validate checkpoints
       print("🔍 Validating checkpoints...")
       checkpoint_valid = True
       for height, expected_hash in CHECKPOINTS.items():
           if expected_hash and height < len(blockchain):
               actual_hash = blockchain[height]['hash']
               if actual_hash != expected_hash:
                   print(f"❌ Checkpoint mismatch at height {height}")
                   print(f"   Expected: {expected_hash}")
                   print(f"   Actual: {actual_hash}")
                   checkpoint_valid = False
       
       if checkpoint_valid:
           print("✅ All checkpoints validated")
       
       # Network health analysis
       print("\n📊 Network Health Analysis:")
       print(f"  Health Score: {consensus_analytics.get_network_health_score():.0f}/100")
       print(f"  Stability Score: {consensus_analytics.get_stability_score():.2f}")
       print(f"  Fork Count: {consensus_analytics.fork_count}")
       if consensus_analytics.reorg_depths:
           avg_depth = sum(consensus_analytics.reorg_depths) / len(consensus_analytics.reorg_depths)
           print(f"  Average Reorg Depth: {avg_depth:.1f}")
       
       # Witness node status
       print("\n⭐ Witness Node Status:")
       print(f"  Node ID: {witness_node.node_id}")
       print(f"  Uptime: {witness_node.get_uptime_days():.1f} days")
       print(f"  Blocks Validated: {witness_node.blocks_validated}")
       print(f"  Reliability Score: {witness_node.reliability_score:.2f}")
       print(f"  Witness Weight: {witness_node.calculate_witness_weight():.2f}")
       print(f"  Witness Status: {'ACTIVE' if witness_node.witness_status else 'BUILDING REPUTATION'}")
       
       # Summary
       print(f"\n📊 Validation Summary:")
       print(f"  📈 Chain height: {len(blockchain)}")
       print(f"  🔗 Total work: {calculate_chain_work(blockchain)}")
       print(f"  💰 Total UTXOs: {len(load_json(UTXO_FILE, []))}")
       print(f"  🔄 Total transactions: {sum(len(block.get('transactions', [])) for block in blockchain)}")
       
       if is_valid_chain(blockchain) and UTXOValidator.validate_utxo_consistency() and not duplicates_found and checkpoint_valid:
           print("🎉 BLOCKCHAIN FULLY VALIDATED - All checks passed!")
       else:
           print("⚠️  Blockchain has issues - see details above")

def cmd_repair_duplicate_heights():
    """Repair duplicate heights by choosing link-first + look-ahead chain and persist it."""
    print(f"🔧 Repair using {BLOCKCHAIN_FILE}")
    chain = load_json(BLOCKCHAIN_FILE, [])
    if not chain:
        print("❌ Empty chain"); return
    by_h: Dict[int, List[Dict]] = {}
    for b in chain:
        try:
            h = int(b.get('index', -1))
        except Exception:
            continue
        by_h.setdefault(h, []).append(b)
    if not by_h or (0 not in by_h):
        print("❌ No genesis at height 0"); return
    def per_work(b):
        try:
            return (1 << 256) // (DifficultyAdjustment.bits_to_target(b.get('bits', MAX_TARGET)) + 1)
        except Exception:
            return 0
    g = max(by_h[0], key=per_work)
    result = [g]
    expected = 1
    while expected in by_h:
        prev = result[-1]
        prevh = prev.get('hash') or prev.get('block_hash')
        cands = [c for c in by_h[expected] if (c.get('previous_hash') or c.get('prev_hash')) == prevh]
        if not cands:
            break
        next_h = expected + 1
        next_parents = set(cb.get('previous_hash') or cb.get('prev_hash') for cb in by_h.get(next_h, []))
        linked_and_parent = [c for c in cands if (c.get('hash') or c.get('block_hash')) in next_parents]
        chosen = max(linked_and_parent or cands, key=per_work)
        result.append(chosen)
        expected += 1
    save_json(BLOCKCHAIN_FILE, result)
    try:
        rebuild_utxo_set(load_json(BLOCKCHAIN_FILE, []))
        print(f"✅ Repaired to contiguous height {expected-1} and rebuilt UTXO")
    except Exception as e:
        print(f"⚠️ UTXO rebuild warning: {e}")
