# Atomic Commit Protocol Synthesis - C Version

CEGIS-based synthesis of Atomic Commit Protocol, mimicking the structure of `c_version` (Consensus).

## Properties

- **Agreement**: All alive nodes must decide the same (abort or commit)
- **Validity**: All vote abort → all decide abort; all vote commit → all decide commit

## Dependencies

- Z3 SMT solver (C library)
- GCC or Clang

### macOS

```bash
brew install z3
```

### Linux (Ubuntu/Debian)

```bash
sudo apt install z3 libz3-dev
```

## Build

```bash
cd atomic_commit
make
```

## Run

```bash
./cegis_atomic_commit
```

Or:

```bash
make run
```

## Configuration

Edit `config.h`:

- `NUM_NODES`: number of participants
- `NUM_ROUNDS`: number of rounds

## Output

- On success: protocol saved to `generated_protocol_atomic_commit.c`
- Message values: 0=abort, 1=commit, 2=missing
