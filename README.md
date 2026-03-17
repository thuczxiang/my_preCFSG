# preCFSG

本项目是 **清华大学求真书院 AI4Formalism 第二期迷你课程 (Season 2)** 的学习与练习仓库。

This repository is for the **AI4Formalism Minicourse (Season 2)** at **Qiuzhen College, Tsinghua University**. It follows the curriculum of the minicourse on mathematical formalization using Lean 4.

## 项目背景 | Context
课程仓库是 [adomani/PreCFSG](https://github.com/adomani/PreCFSG)。主要目标是通过 Lean 4 学习如何将现代数学语言形式化。

- **课程主页**: [adomani/PreCFSG](https://github.com/adomani/PreCFSG)
- **组织方**: 清华大学求真书院 (Qiuzhen College, Tsinghua University)
- **技术栈**: Lean 4, Mathlib4

## 安装与运行 | Setup

由于本项目依赖于 `Mathlib`，请确保你已经安装了 [Elan](https://github.com/leanprover/elan)。

1. **克隆项目**:
   ```bash
   git clone git@github.com:MouAoZ/my_preCFSG.git
   cd my_preCFSG
    ```

2. **获取 Mathlib 缓存**
    ```bash
    lake exe cache get
    ```

3. **构建项目**
    ```bash
    lake build
    ```