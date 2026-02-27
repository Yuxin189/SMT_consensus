# Atomic Commit Protocol Synthesis - C Version

CEGIS-based synthesis of Atomic Commit Protocol, mimicking the structure of `c_version` (Consensus).

## States (match Python atomic_commit.py)

| 值 | 状态 | 类型 |
|----|------|------|
| 0 | Abort | 终态 |
| 1 | Commit | 终态 |
| 2 | DoNothing_Zero | 中间态 |
| 3 | DoNothing_One | 中间态 |
| 4 | Lost/Missing | 特殊（recv 中表示 missing） |
| 0/1 | LocalAbort/LocalCommit | 初始态（init） |

## Rules (5 条，与 Python 一致)

| 规则 | 描述 |
|------|------|
| **Rule 1** | 所有 uncrashed 节点必须到达终态 (0 或 1) |
| **Rule 2** | 只能在最后一轮做最终决定；中间轮只能输出 2 或 3 |
| **Rule 3** | Agreement：所有 uncrashed 节点决定相同 |
| **Rule 4** | 全 LocalCommit + 无 crash → 全 Commit |
| **Rule 5** | 任一 LocalAbort → 全 Abort |

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

## Verification

```bash
make run    # synthesize protocol
make check  # run trace checker on generated_protocol_atomic_commit.c
```

### Checker scenarios (A–F)

| 场景 | 描述 | 期望 | CEGIS 覆盖 |
|------|------|------|------------|
| **A** | 全员 LocalCommit，无 crash，无 missing | 全 Commit (Rule 4) | ✓ |
| **B** | 任一 LocalAbort，无 crash，无 missing | 全 Abort (Rule 5) | ✓ |
| **C** | 全员 LocalCommit，但有 missing | 不能 Commit（保守 Abort） | ✗ |
| **D** | 某节点早 crash，别人收不到它 | 存活节点必须 Abort | ✗ |
| **E** | 最后一轮才 crash | 无 split commit/abort（Agreement） | ✓ |
| **F** | 不能提前决定 | 非最后一轮不能出现 Commit/Abort | 需模型扩展 |

当前 CEGIS 只强制 Rule 3/4/5，未强制 Rule 6（any crash→abort）和 Rule 7（any missing→abort）。若 C/D 失败，说明协议未满足更保守的语义。
