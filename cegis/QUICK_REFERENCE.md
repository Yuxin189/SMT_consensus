# 协议生成快速参考

## 🎯 协议生成的关键位置

### 1. **协议模板定义**
**文件：** `protocol_template.py`  
**函数：** `build_state_update()` (第 29-52 行)  
**作用：** 定义参数化的协议逻辑模板

```python
# 这里定义了：S[i][t] = f(参数, S[i][t-1], incoming)
return Or(terms)  # 根据参数组合各项
```

---

### 2. **参数搜索**
**文件：** `synthesizer.py`  
**函数：** `propose_candidate()` (第 35-61 行)  
**作用：** Z3 自动搜索满足约束的参数组合

```python
# 这里：Z3 找到一个参数组合，如 {keep_old: True, use_incoming: True, ...}
model = self.solver.model()
candidate = {...}
```

---

### 3. **协议逻辑生成（核心！）**
**文件：** `verifier.py`  
**函数：** `build_environment()` (第 104-114 行)  
**作用：** 将参数实例化到模板，生成具体的协议逻辑

```python
# ⭐ 这里！协议在这里生成！
s.add(S[i][t] == protocol_template.build_state_update(S[i][t - 1], incoming_any))
# 当参数固定时，这行代码会生成：
# S[i][t] = S[i][t-1] ∨ incoming_any  (如果 keep_old=True, use_incoming=True)
```

---

### 4. **协议代码生成**
**文件：** `protocol_generator.py`  
**函数：** `generate_python_code()` (第 84-219 行)  
**作用：** 将参数转换为可执行的 Python 代码

```python
# 根据参数值生成代码字符串
if self.keep_old:
    code += "            terms.append(S[i][t - 1])\n"
```

---

## 📍 执行流程

```
1. CEGISLoop.run() 启动
   ↓
2. Synthesizer.propose_candidate() 
   → 搜索参数组合
   ↓
3. Verifier.verify_specification()
   → Verifier.build_environment()
   → protocol_template.build_state_update()
   → ⭐ 这里生成协议逻辑！
   ↓
4. 如果验证通过：
   → ProtocolGenerator.generate_python_code()
   → ⭐ 这里生成 Python 代码！
```

---

## 🔍 如何查看生成的协议？

### 方法1：看终端输出
运行 `python cegis/run_cegis.py`，会显示：
- 协议名称
- 状态更新公式
- 规则描述

### 方法2：看生成的 Python 文件
运行 `python cegis/run_cegis.py 4 3 10 my_protocol.py`，查看 `my_protocol.py`

### 方法3：看代码中的关键位置
- **协议逻辑生成：** `verifier.py` 第 114 行
- **参数搜索：** `synthesizer.py` 第 45 行
- **代码生成：** `protocol_generator.py` 第 84-219 行

---

## 💡 关键理解

**协议不是在某个地方"写"出来的，而是：**
1. **模板定义**了所有可能的协议形式
2. **Z3 搜索**找到正确的参数组合
3. **参数实例化模板**生成具体协议逻辑
4. **生成器输出**转换为可读/可用形式

**核心生成位置：** `verifier.py` 第 114 行
```python
s.add(S[i][t] == protocol_template.build_state_update(...))
```

