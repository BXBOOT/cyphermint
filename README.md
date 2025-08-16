# 🚀 First Release: CypherMint CLI

I’ve decided to release the **CLI version** of CypherMint (CPM) while the block explorer and full UI/UX interface are still being completed. I’m about a week behind schedule and just want to ensure everything runs smoothly first.

The **block explorer** is partially live at [https://cyphermint.org](https://cyphermint.org), but more functionality is coming soon—including full transaction search.

I'm a single developer, and this project has been a massive effort—thank you for trying it out. I would love to see this project grow organically, and get listed on exchanges like bitmart, binance, Kraken, MEXC etc, and for early adopters to make it a viable asset with value! Dont trade it for Uber eats, or throw out your devices/harddrives, it could turn out to be the most expensive meal you order, or spend 12 years digging through the dump... neither seems like a good idea!

# CypherMint (CPM)

## Cryptocurrency Demonstrating Possible Human Crypto Vulnerabilities in coins like earll bitcoin development etc. 

**PRODUCTION MODE** - Full Bitcoin Style difficulty

CypherMint is a complete Bitcoin-style cryptocurrency (You cannot send or receive bitcoin to these addresses so dont try or you will lose what you send) that demonstrates how human behavioral patterns create vulnerabilities in cryptographic key generation.

### Security Notice
**ONLY THE GENESIS BLOCK** uses predictable key generation to demonstrate the vulnerability. Solving the puzzle for the genesis block does not get you access to the full chain or other wallets!! All subsequent addresses use cryptographically secure random generation.

### Purpose
This project proves that human weakness in cryptocurrency key generation exists **before** quantum computing threats, using a live, working blockchain.

### Network Details
- **Total Supply**: 21,000,000 CPM
- **Block Reward**: 50 CPM (halving every 210k blocks)
- **Block Time**: 10 minutes
- **Mining**: SHA-256 Proof of Work
- **Protocol**: Bitcoin-style (PoW)
- **Mode**: Production (full difficulty)

---

## ✅ What You’ll Need

- Windows / macOS / Linux with access to **Python 3.8+**
- Optionally, install **Git** and **Visual Studio Code** or just use **PowerShell** or **CMD**
- Download or clone the two essential files:
  - `cyphermint.py`
  - `genesis_block.json`

---

## 🛠️ Setup Steps

1. **Clone the repository from GitHub** 

```bash
git clone https://github.com/BXBOOT/cyphermint
cd cyphermint
```

2. **(Optional) Create a Python virtual environment:**

```bash
python -m venv venv
venv\Scripts\activate    # Windows
source venv/bin/activate # macOS/Linux
```

3. **Install dependencies:**

```bash
pip install flask schedule requests
pip install minupnpc
pip install ecdsa
(if you are having trouble with these check the python environment you are using and adjust if needed. Google can provide trouble shooting steps).
```

---

### Quick Start

#### 1. Generate Wallet
```bash
python3 cyphermint.py wallet --generate (Save this somewhere else also, just in case you lose your device. DO NOT SHARE PRIVATE KEY WITH ANYONE!!)
```
- This creates a secure `wallet.json` in your local folder.
- DO NOT share your private key with anyone.
- Your **public address** is safe to share for receiving CPM.

---

#### 2. Start Mining
```bash
python3 cyphermint.py mine --address YOUR_ADDRESS (optional to run as --seed to strengthen the network and peer discovery)
```

#### 3. Check Balance
```bash
python3 cyphermint.py balance --address YOUR_ADDRESS
```

#### 4. Send Transaction
```bash
python3 cyphermint.py send --address FROM_ADDRESS  --to TO_ADDRESS --amount X.X
(cyphermint will not allow you to send from an address you do not have the private ke for. the amount sends as you have it typed in ex 5.7892675 ot 0.6543 etc).
(as with bitcoin, ethereum etc, as the blocks get mined, the transactions are completed. once sent there is no going back, make sure you have the correct address!!)
```


## 🔐 Wallet Safety Tips

- Your wallet is everything. If you lose `wallet.json`, you lose your CPM.
- Back it up to:
  - An encrypted USB/thumb drive
  - Offline cold storage
- DO NOT email or cloud-sync your wallet file.
- DO NOT use the cleanup command. It deletes blockchain data—including your wallet in **development mode**.

---

## ⛏️ Mining Commands

- **Start mining**:
  ```bash
  python3 cyphermint.py mine --address <your_address>
  ```

- **Run as a seed node (helps the network)**:
  ```bash
  python3 cyphermint.py mine --address <your_address> --seed

  if it appears like your your miner has stalled stop your miner (ctrl C in most cases) use 'python3 cyphermint.py validate'. this will validate the chain and utxos and then restart your miner
  ```

Seed nodes **help bootstrap the network** by acting as hubs to share blocks and improve peer discovery. More seed nodes = stronger network.

---

## 📜 Useful Commands

| Command | Description |
|--------|-------------|
| `python3 cyphermint.py wallet` | Show your wallet address & public key |
| `python3 cyphermint.py balance --address <addr>` | View CPM balance for any address |
| `python3 cyphermint.py balance --address <addr> --utxos` | See UTXOs making up that balance |
| `python3 cyphermint.py mine --address <addr>` | Mine using your address |
| `python3 cyphermint.py mine --address <addr> --seed` | Mine and share data as a seed node |
| `python3 cyphermint.py send --address <your_addr> --to <other_addr> --amount X.X` | Send CPM |
| `python3 cyphermint.py mempool` | Show pending transactions |
| `python3 cyphermint.py validate` | Validate blockchain and trigger UTXO repair if needed |
| `python3 cyphermint.py info` | Show node status, difficulty, peers, mempool size, etc. |

---

## 🎯 Difficulty Ramping

To help you get started:

- The **first 100 blocks** use an easier mining target.
- Gradually, the difficulty increases every few hundred blocks.
- By **block 2016**, difficulty hits full production (Bitcoin-style) levels.

---

## 🎁 The Treasure Hunt

The **genesis block contains a quirk**—a hardcoded vulnerability that can **eventually be exploited** when the right clues are revealed.

How it works:
- **1 CPM per block** is sent to the genesis address.
- At certain block heights, **clues will be released** on [cyphermint.org](https://cyphermint.org) and [@satoshicypher](https://instagram.com/satoshicypher)
- Whoever solves the clues may unlock access to this growing stash of CPM.

This is **part social experiment**, part tribute to cryptography’s fragility in the hands of humans.

---

## ⚠️ Reminders

- **DO NOT DELETE your mining device or its wallet!** We will not be digging through landfills for hard drives.
- **DO NOT order Uber Eats using CPM**. It may become the most expensive meal of your life.
- **DO NOT share your private key or wallet file** with anyone.

---

### Disclaimer
This is a research and educational project. The Genesis block vulnerability is intentional to demonstrate security concepts. ONLY the genesis block ahs the purposeful 'quirk' all other addresses are created in the sae way Bitcoin addresses are. Do not try and hack or break an address, it wont work. Clues will be released over time about the genesis generation, and that will only get you access to the genesis address balance.

## 📣 Stay Connected

- Explorer: [https://cyphermint.org](https://cyphermint.org)
- IG: [@satoshicypher](https://instagram.com/satoshicypher)
- GitHub (release coming soon): `https://github.com/BXBOOT/cyphermint`

---

Let the mining begin.

— Team CypherMint 🌀
