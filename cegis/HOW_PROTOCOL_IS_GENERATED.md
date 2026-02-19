# 协议是怎么生成的？在哪里？

## 协议生成的完整流程

### 第一步：定义协议模板（`protocol_template.py`）

**位置：** `cegis/protocol_template.py` 第 29-52 行

**作用：** 定义了一个**参数化的协议模板**，协议逻辑由 3 个布尔参数控制：

```python
def build_state_update(self, S_prev, incoming_any):
    terms = []
    
    # 根据参数决定是否包含各项
    terms.append(If(self.keep_old, S_prev, False))      # 是否保留旧状态
    terms.append(If(self.use_incoming, incoming_any, False))  # 是否使用接收的消息
    terms.append(If(self.use_const_one, True, False))   # 是否无条件设为True
    
    return Or(terms)  # S[i][t] = 各项的或
```

**关键点：** 
- 这里的 `keep_old`, `use_incoming`, `use_const_one` 是 **Z3 变量**（不是固定值）
- 模板定义了**所有可能的协议形式**，但具体是哪种形式由参数决定

---

### 第二步：Synthesizer 提出候选参数（`synthesizer.py`）

**位置：** `cegis/synthesizer.py` 第 35-61 行

**作用：** 用 Z3 求解器**自动搜索**满足约束的参数组合

```python
def propose_candidate(self):
    # 检查是否有解（满足所有约束的参数组合）
    if self.solver.check() == unsat:
        return None  # 没有解了
    
    # 获取一个满足约束的参数赋值
    model = self.solver.model()
    candidate = {
        'keep_old': model.evaluate(self.keep_old),
        'use_incoming': model.evaluate(self.use_incoming),
        'use_const_one': model.evaluate(self.use_const_one),
    }
    return candidate
```

**关键点：**
- Synthesizer 维护一个 Z3 solver，里面存储了**排除已知错误参数组合的约束**
- 每次调用 `propose_candidate()`，Z3 会找到一个**新的、还没被排除的参数组合**

---

### 第三步：Verifier 验证候选协议（`verifier.py`）

**位置：** `cegis/verifier.py` 第 104-114 行

**作用：** 将候选参数**实例化**到协议模板，生成具体的协议逻辑，然后验证

```python
# 6. Protocol state updates (using template)
for i in self.nodes:
    for t in self.ROUNDS:
        incoming = [And(M[(j, i, t)], S[j][t - 1]) for j in self.nodes if j != i]
        incoming_any = Or(incoming) if incoming else False
        
        # 这里！用模板和参数生成具体的状态更新规则
        s.add(S[i][t] == protocol_template.build_state_update(S[i][t - 1], incoming_any))
```

**关键点：**
- 当参数固定为具体值（如 `keep_old=True, use_incoming=True`）时
- `build_state_update()` 会生成具体的公式：`S[i][t] = S[i][t-1] ∨ incoming_any`
- 这就是**协议的核心逻辑**！

---

### 第四步：CEGIS 循环协调（`cegis_loop.py`）

**位置：** `cegis/cegis_loop.py` 第 53-104 行

**作用：** 循环执行"提出候选 → 验证 → 反馈反例 → 更新约束"

```python
for iteration in range(self.max_iterations):
    # 1. Synthesizer 提出候选参数
    candidate = self.synthesizer.propose_candidate()
    
    # 2. Verifier 验证这个候选协议
    counterexample = self.verifier.verify_specification(self.template, candidate)
    
    # 3. 如果找到反例，反馈给 Synthesizer
    if counterexample:
        self.synthesizer.accumulate_counterexample(counterexample, candidate)
        # Synthesizer 会添加约束，排除这个参数组合
    
    # 4. 如果没找到反例，协议生成成功！
    else:
        return candidate  # 这就是生成的协议参数
```

---

### 第五步：协议生成器转换参数为可读形式（`protocol_generator.py`）

**位置：** `cegis/protocol_generator.py`

**作用：** 将找到的参数组合转换为：
1. 协议名称（如 "FloodSet"）
2. 数学公式（如 `S[i][t] = S[i][t-1] ∨ ...`）
3. 可读描述
4. Python 代码

**关键函数：**

```python
# 第 29-52 行：生成状态更新公式
def get_state_update_formula(self):
    terms = []
    if self.keep_old:
        terms.append("S[i][t-1]")
    if self.use_incoming:
        terms.append("∃j≠i: M(j→i, t) ∧ S[j][t-1]")
    # ...
    return "S[i][t] = " + " ∨ ".join(terms)

# 第 84-219 行：生成 Python 代码
def generate_python_code(self):
    # 生成完整的可执行协议代码
    # 包含 Z3 变量定义、约束、状态更新规则等
```

---

## 协议生成的具体位置总结

### 1. **协议逻辑生成位置**

**文件：** `cegis/verifier.py`  
**函数：** `build_environment()` 第 104-114 行  
**代码：**
```python
s.add(S[i][t] == protocol_template.build_state_update(S[i][t - 1], incoming_any))
```

**这里发生了什么：**
- `protocol_template.build_state_update()` 根据参数生成 Z3 公式
- 这个公式被添加到 solver 中，成为协议的状态更新规则
- **这就是协议的核心！**

### 2. **参数搜索位置**

**文件：** `cegis/synthesizer.py`  
**函数：** `propose_candidate()` 第 35-61 行  
**代码：**
```python
model = self.solver.model()
candidate = {
    'keep_old': model.evaluate(self.keep_old),
    # ...
}
```

**这里发生了什么：**
- Z3 solver 搜索满足所有约束的参数组合
- 返回一个候选参数赋值

### 3. **协议代码生成位置**

**文件：** `cegis/protocol_generator.py`  
**函数：** `generate_python_code()` 第 84-219 行  
**代码：**
```python
if self.keep_old:
    code += "            terms.append(S[i][t - 1])\n"
if self.use_incoming:
    code += "            terms.append(incoming_any)\n"
```

**这里发生了什么：**
- 根据参数值，生成对应的 Python 代码字符串
- 代码包含完整的状态更新逻辑

---

## 完整流程图

```
1. ProtocolTemplate (protocol_template.py)
   ↓ 定义参数化的协议模板
   keep_old, use_incoming, use_const_one (Z3 变量)

2. Synthesizer (synthesizer.py)
   ↓ 用 Z3 搜索参数组合
   propose_candidate() → {keep_old: True, use_incoming: True, ...}

3. Verifier (verifier.py)
   ↓ 将参数实例化到模板，生成协议逻辑
   build_environment() → S[i][t] = S[i][t-1] ∨ incoming_any
   ↓ 验证协议是否满足规范
   verify_specification() → Counterexample or None

4. CEGISLoop (cegis_loop.py)
   ↓ 协调循环
   如果找到反例 → 反馈给 Synthesizer → 更新约束 → 回到步骤2
   如果没反例 → 协议生成成功！

5. ProtocolGenerator (protocol_generator.py)
   ↓ 将参数转换为可读形式
   generate_python_code() → 完整的 Python 代码文件
   get_state_update_formula() → 数学公式
   get_protocol_name() → "FloodSet"
```

---

## 关键理解

**协议不是在某个地方"写出来"的，而是：**

1. **模板定义了协议空间**：所有可能的协议形式
2. **Z3 搜索参数空间**：找到满足约束的参数组合
3. **参数实例化模板**：参数 + 模板 = 具体协议逻辑
4. **验证确保正确性**：确保协议满足规范
5. **生成器输出结果**：转换为可读/可用的形式

**所以协议是在 `verifier.py` 的 `build_environment()` 中"生成"的，**
**但它的"搜索"是在 `synthesizer.py` 中完成的，**
**它的"形式化"是在 `protocol_template.py` 中定义的。**

