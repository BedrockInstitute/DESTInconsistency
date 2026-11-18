# 弱双面外延集合论不一致

[English](README.md) · **中文**

我们证明了 Kisielewicz 的弱双面外延集合论 DEST 不一致：仅混合外延性与概括这两条公理就已互相矛盾，其中概括只允许均质（regular）参数．DEST 有 $\in$、$\varepsilon$ 两种成员关系，能解释 ZF，其一致性此前一直是开放问题．

核心是一条对角定理：单凭概括就能驳倒一切在两种成员关系之间「不对称」的公式，而且这一定理的证明既不需要混合外延性，也不需要经典逻辑．混合外延性与经典逻辑只用来证明序数不对称．

| 路径 | 内容 |
|---|---|
| `pdf/` | 论文：中文 `dest-inconsistency.zh.pdf`，英文 `dest-inconsistency.en.pdf` |
| `tex/` | 两版论文的 LaTeX 源文件与构建脚本 `build.sh` |
| `blind-test/diagonal-summary.zh.png` | 对角论证的一页摘要，即第二次盲测形式化的输入 |
| `agda/DESTInconsistency.agda` | Agda 形式化：单文件，不导入任何模块 |
| `lean/` | Lean 4 形式化：不依赖任何库；`Probes.lean` 做了几项辅助核对，详见论文第 6 节 |

## 核对证明

**Agda**：已在 2.8.0.2 版下测试．在 `agda` 目录下运行：

```
agda --safe --no-libraries DESTInconsistency.agda
```

信任部分有两块：一是文件的第 0–1 节，给出逻辑、语法、两种读法、公理和不对称的定义；二是第 4 节中的定理陈述．定理如下：
- `diagonal : (M : Set) (E : Rel M) → Comp M E → … → Opp b c → ¬ Asymmetric E P ρ b c`
- `inconsistent : (M : Set) (E : Rel M) → DEST⁻ M E → DNE → ⊥`
- `DEST-inconsistent : (M : Set) (E : Rel M) → DEST M E → DNE → ⊥`

其中 `DEST⁻` 指 ME 加 COMP；`DNE` 指双重否定消去，即经典逻辑．`diagonal` 既不使用 ME，也不使用 `DNE`．

**Lean 4**：在 `lean` 目录下运行下面的命令．工具链版本 `v4.36.0` 已在 `lean-toolchain` 中固定，不需要其他依赖．

```
lake build
```

信任部分即 `DESTInconsistency.lean` 的第 I 部分和第 III 部分的定理陈述，论文附录 A 原样列出了它们．构建主文件时输出：

```
'DEST.diagonal' does not depend on any axioms
'DEST.inconsistent' does not depend on any axioms
'DEST.DEST_inconsistent' does not depend on any axioms
'DEST.inconsistent'' depends on axioms: [propext, Classical.choice, Quot.sound]
'DEST.DEST_inconsistent'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`inconsistent` 把经典逻辑作为显式假设 `∀ P : Prop, ¬¬P → P`；带撇号的版本改用 Lean 内置的经典逻辑．运行 `lake env leanchecker DESTInconsistency` 可以重新核对编译结果．

## 构建论文

在 `tex` 目录下运行：

```
./build.sh          # 生成两份 PDF，输出到 ../pdf
```

脚本先运行 `gen_codelinks.py`，从 `agda/` 与 `lean/` 重新生成代码链接和代码摘录，再用 [Tectonic](https://tectonic-typesetting.github.io/) 编译 PDF．也可以改用 TeX Live 的 `latexmk -xelatex`，需要 `ctex` 宏包和 DejaVu Sans Mono 字体．中文 PDF 优先使用 macOS 自带的宋体、黑体、楷体，没有时自动换成思源或 TeX 自带的 Fandol 字体．

## 作者与 AI 使用

通讯作者：Peter Zhang（peterzhangsg@gmail.com）．研究由他主导，借助 ChatGPT（Astra 6.2，OpenAI）与 Claude（Anthropic）完成，分工见论文的「工具与计算资源说明」（附录 B）．

## 引用

见 [`CITATION.bib`](CITATION.bib)．

## 许可

全部文件以 [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) 许可发布，全文见 [`LICENSE`](LICENSE)．

© 2026 Bedrock Institute．
