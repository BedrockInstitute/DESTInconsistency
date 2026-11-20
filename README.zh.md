# 弱双面外延集合论不一致

[English](README.md) · **中文**

我们证明了 Kisielewicz 的弱双面外延集合论 DEST 不一致：仅混合外延性与概括这两条公理就已互相矛盾，其中概括只允许均质（regular）参数．DEST 有 $\in$ 与 $\varepsilon$ 两种成员关系，能解释 ZF，其一致性此前一直是开放问题．

核心是一条对角定理：单凭概括就能驳倒一切在两种成员关系之间「不对称」的公式，而且这一定理的证明既不需要混合外延性，也不需要经典逻辑．在主证明中，混合外延性与经典逻辑只用来证明序数不对称．另有一个证明变体，换用另一个序数公式，完全不用经典逻辑，所以这两条公理在直觉主义逻辑中也互相矛盾；它作为附加代码形式化，见 `agda/Intuitionistic.agda` 与 `lean/Intuitionistic.lean`．

## 论文

1. **弱双面外延集合论不一致**（2026 年 11 月）．[中文 PDF](pdf/dest-inconsistency.zh.pdf) · [英文 PDF](pdf/dest-inconsistency.en.pdf) · [BibTeX](CITATION.bib)

## 核对证明

Agda 2.8.0.2，在 `agda` 目录下运行：

```
agda --safe --no-libraries DESTInconsistency.agda
agda --safe --no-libraries Intuitionistic.agda
agda --safe --no-libraries Supplement.agda
```

Lean 4，在 `lean` 目录下运行．工具链 v4.36.0 已固定，不需要其他依赖．

```
lake build
lake env leanchecker DESTInconsistency
lake env leanchecker Intuitionistic
```

各文件的信任部分、所证的定理与其他核对，见论文第 6 节．那里提到的盲测形式化，其输入与输出在 `blind-test/` 中；其中的 Lean 文件用 `lean intuitionistic.lean` 核对．

## 构建论文

在 `tex` 目录下运行 `./build.sh`：它先从 `agda/` 与 `lean/` 重新生成代码链接和代码摘录，再用 [Tectonic](https://tectonic-typesetting.github.io/) 生成两份 PDF，输出到 `pdf/`．也可以改用 TeX Live 的 `latexmk -xelatex`，需要 `ctex` 宏包和 DejaVu Sans Mono 字体．

## 许可

全部文件以 [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) 许可发布，全文见 [`LICENSE`](LICENSE)．© 2026 Bedrock Institute．
