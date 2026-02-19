# CEGIS 工具到底在做什么？

## 核心问题回答

### 1. **这个工具想生成什么协议？**

这个工具在**自动寻找共识协议的状态更新规则**。

具体来说，它在一个**参数化的协议模板**中搜索，找到满足以下**规范（Specification）**的参数组合：

**规范（硬编码在 Verifier 中）：**
1. **All-0 Validity（全0有效性）**：如果所有节点的初始输入都是 0，那么所有活着的节点必须最终决定 0
2. **All-1 Validity（全1有效性）**：如果所有节点的初始输入都是 1，那么所有活着的节点必须最终决定 1  
3. **Agreement（一致性）**：所有没有崩溃的节点必须做出相同的决策

**协议模板（当前有3个布尔参数）：**
- `keep_old`: 是否保留上一轮自己的状态 `S[i][t-1]`
- `use_incoming`: 是否使用本轮收到的其他节点的状态
- `use_const_one`: 是否允许无条件设置为 True

**生成的协议**就是：满足上述规范的状态更新规则。

---

### 2. **什么条件都没有？**

实际上**规范是有的**，只是硬编码在代码里了。规范就是上面说的三个性质：
- Validity（有效性）
- Agreement（一致性）

这些规范在 `verifier.py` 的 `verify_specification()` 函数中实现。

如果你想**自定义规范**，可以：
1. 修改 `verifier.py` 中的验证逻辑
2. 或者添加新的规范检查

---

### 3. **生成的协议在哪里？**

生成的协议会：

1. **在终端输出**：显示协议名称、状态更新公式、规则描述
2. **保存为 Python 文件**：如果使用 `run_cegis.py` 并指定输出文件，会生成可执行的协议代码

例如运行：
```bash
python cegis/run_cegis.py 4 3 10 my_protocol.py
```

会生成 `my_protocol.py`，里面包含：
- 完整的协议实现代码
- 可以直接导入使用的函数

---

## 生成的协议是什么？

### 协议的核心：状态更新规则

协议定义了每个节点在每一轮如何更新自己的状态 `S[i][t]`。

**当前模板生成的状态更新规则：**

```
S[i][t] = (keep_old ∧ S[i][t-1]) 
       ∨ (use_incoming ∧ incoming_messages)
       ∨ (use_const_one ∧ True)
```

其中：
- `S[i][t]`: 节点 i 在第 t 轮结束时是否"收到过 0"
- `S[i][t-1]`: 上一轮的状态
- `incoming_messages`: 本轮收到的其他节点发送的状态

### 决策规则（固定）

```
如果 S[i][R] = True（收到过 0），则决定 0
否则决定 1
```

---

## 示例：生成的 FloodSet 协议

当工具找到 `keep_old=True, use_incoming=True, use_const_one=False` 时，生成的协议是：

**状态更新公式：**
```
S[i][t] = S[i][t-1] ∨ (∃j≠i: M(j→i, t) ∧ S[j][t-1])
```

**含义：**
- 节点 i 在第 t 轮的状态 = 上一轮的状态 **或者** 本轮收到任何其他节点 j 的状态

这就是经典的 **FloodSet 协议**！

---

## 如何使用生成的协议？

### 方式1：查看生成的 Python 文件

```bash
python cegis/run_cegis.py 4 3 10 my_protocol.py
cat my_protocol.py
```

生成的代码可以直接导入使用：
```python
from my_protocol import synthesized_protocol

s, nodes, init, C, M, S, Decide1 = synthesized_protocol(N=4, R=3)
# 现在可以用这个 solver 进行验证或其他操作
```

### 方式2：在代码中使用参数

```python
from cegis.cegis_loop import CEGISLoop
from cegis.protocol_generator import ProtocolGenerator

# 运行合成
loop = CEGISLoop(N=4, R=3, max_iterations=10)
result = loop.run()

if result:
    generator = ProtocolGenerator(result)
    print(f"协议名称: {generator.get_protocol_name()}")
    print(f"状态更新公式: {generator.get_state_update_formula()}")
    
    # 生成代码
    code = generator.generate_python_code()
    print(code)
```

---

## 总结

1. **生成什么**：满足 Validity + Agreement 规范的状态更新规则
2. **规范在哪里**：硬编码在 `verifier.py` 中（可以修改）
3. **协议在哪里**：
   - 终端输出（协议描述）
   - 生成的 Python 文件（可执行代码）
   - 返回的参数字典（可以在代码中使用）

如果你想扩展这个工具：
- **添加更多协议参数**：修改 `protocol_template.py`
- **添加新的规范**：修改 `verifier.py`
- **改变输出格式**：修改 `protocol_generator.py`

