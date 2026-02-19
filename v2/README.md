# CEGIS v2 — 代码分块说明

代码按「块」划分，以后要**验证别的情况、别的 protocol** 时，改对应一块即可，其余不变。

| 部分 | 文件 | 作用 | 要改什么时动这里 |
|------|------|------|------------------|
| **Part 1** | `config.py` | 全局参数（节点数、轮数、输入 pattern） | 换 3/4/5 节点、轮数、或消息取值 |
| **Part 2** | `system_model.py` | 协议执行语义（状态迹 S、SM 查表、crash-stop） | 换一种 protocol 执行方式 / 消息模型 |
| **Part 3** | `synthesizer.py` | 合成：SM 变量 + 对每个反例的约束 | 换「正确性」定义时改 **3.2 正确性约束**（Agreement + Validity） |
| **Part 4** | `verifier.py` | 验证：环境变量 + 执行迹 + 违反条件 | 换要查的违反条件时改 **4.4 违反条件** |
| **Part 5** | `main.py` | CEGIS 主循环、初始反例、成功时输出与保存 | 换初始反例或输出/保存格式 |

- **只改「正确性」条件**（例如别的 consensus 定义）：改 `synthesizer.py` 里 3.2 的约束，和 `verifier.py` 里 4.4 的违反条件，两处保持一致即可。
- **只改执行语义**（例如不同轮次含义）：改 `system_model.py`（Part 2）。
- **只改规模**：改 `config.py`（Part 1）。

运行：`python main.py`（需安装 z3）。
