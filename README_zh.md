# Stern 多项式的严格正性与单调性反例

本说明从标准 Stern 递推定义出发，证明

\[
B_{h_n}(t)>0\quad(n\geq0,\ t\in\mathbb R),\qquad
h_n=\frac23(2^{2n}-1)(2^{2n+1}+1)+1.
\]

同时精确计算 `B_183(t) = t^5 + 3t^4 + 7t^3 + 9t^2 + 5t + 1`，其在 `t = -2/3` 处的导数为 `-19/81`。位于 `(-1,0)` 内的两个有理点也直接给出函数值下降证书。这证明了 Ulas [arXiv:1909.10844v1](https://arxiv.org/abs/1909.10844v1) 中猜想 4.4 的断言，并否定猜想 4.3 最后的单调性子项。

证明使用的核心二次型已经见于 Ulas 原文，文中明确保留归属。猜想 4.3 的一般唯一实根子项**尚未解决**；`B_183` 本身恰好只有实根 `-1`。

Lean 项目已经验证全参数严格正性与反例，并将负导数直接连接到 `(-1,0)` 上单调性不成立的结论。形式化证明的是实数取值恒等式及整数多项式可表示性；未另行构造规范的整数多项式对象序列，也未形式化根的重数。

- 完整英文证明：[note.tex](note.tex)，编译后为 `note.pdf`。
- Lean 的精确证明范围、定理名称、构建结果及公理依赖见 `STATUS.md`。
- 来源归属、访问限制与第三方材料边界见 [SOURCES.md](SOURCES.md)。

使用 Lean 和 mathlib **v4.19.0** 构建形式化项目：

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
cd ..
```

记录中的本地验证使用已安装的 Lean 工具链和现有 mathlib 依赖，未另行测试从网络全新下载依赖后构建。实际命令和验证范围见 `STATUS.md`。

辅助的精确算术检查器需要 Python **3.8 或更新版本**，无第三方依赖，已在 Python 3.8.3 上运行通过：

```sh
python check.py
```

有限检查包含 `n = 0,...,20`，结果保存在 `check_results.json`。这些检查不替代全参数证明。

使用标准 LaTeX 环境编译：

```sh
pdflatex -interaction=nonstopmode -halt-on-error note.tex
pdflatex -interaction=nonstopmode -halt-on-error note.tex
```

正文给出覆盖所有参数的数学证明；有限计算仅作辅助验证。首次性未定：期刊全文和相关的 2025 年博士论文未能访问，文献检查也未穷尽。

本工作在 AI 辅助下完成，不声称已通过人工专家同行评审。
