# CEGIS Consensus Protocol Synthesis - C Version

C implementation, **same logic as the Python version in `v2`** (direct port), using the Z3 C API.

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
cd c_version
make
```

If Z3 is installed elsewhere:

```bash
make Z3_PREFIX=/opt/homebrew
```

## Run

```bash
./cegis
```

Or:

```bash
make run
```

If using Z3 from a Python install, set the library path (`make run` will try automatically):

```bash
export DYLD_LIBRARY_PATH=$(python3 -c "import z3,os; print(os.path.join(os.path.dirname(z3.__file__),'lib'))"):$DYLD_LIBRARY_PATH
./cegis
```

## Configuration

Edit `config.h`:

- `NUM_NODES`: number of nodes
- `NUM_ROUNDS`: number of rounds

`NUM_PATTERNS` is computed at runtime as 3^NUM_NODES (no need to edit).

## Output

- On success: protocol is saved to `generated_protocol_c.c`
- **Fresh context per round**: each CEGIS iteration creates a new Z3 context and calls `Z3_del_context` after synthesize + verify (same as Python; no AST accumulation).
- **Synthesis**: same as Python; each synthesis uses **all** current counterexamples (no sampling).
