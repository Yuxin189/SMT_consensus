# CEGIS Consensus Protocol Synthesis - C Version

C 语言实现，**与 `v2` 目录下 Python 版本逻辑完全一致**（原封不动移植），使用 Z3 C API。

## 依赖

- Z3 SMT solver (C 库)
- GCC 或 Clang

### macOS

```bash
brew install z3
```

### Linux (Ubuntu/Debian)

```bash
sudo apt install z3 libz3-dev
```

## 编译

```bash
cd c_version
make
```

若 Z3 安装在其他路径：

```bash
make Z3_PREFIX=/opt/homebrew
```

## 运行

```bash
./cegis
```

或：

```bash
make run
```

若使用 Python 安装的 Z3，需设置库路径（`make run` 会自动尝试）：

```bash
export DYLD_LIBRARY_PATH=$(python3 -c "import z3,os; print(os.path.join(os.path.dirname(z3.__file__),'lib'))"):$DYLD_LIBRARY_PATH
./cegis
```

## 配置

修改 `config.h`：

- `NUM_NODES`: 节点数
- `NUM_ROUNDS`: 轮数

修改 `NUM_NODES` 时需在 `config.h` 中同步更新 `NUM_PATTERNS` 的 `#if` 分支（3^NUM_NODES）。

## 输出

- 成功时：协议保存到 `generated_protocol_c.c`
- **每轮独立 context**：每轮 CEGIS 新建一个 Z3 context，本轮 synthesize + verify 用完后立即 `Z3_del_context`，与 Python 一致，不在多轮间累积 AST。
- **合成逻辑**：与 Python 一致，每次合成使用**全部**当前反例，不采样。
