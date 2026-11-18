# Weak double extension set theory is inconsistent

We prove that Kisielewicz's weak double extension set theory DEST is inconsistent: already two of its axioms, mixed extensionality (ME) and comprehension with regular parameters (COMP), contradict each other. DEST has two membership relations, $\in$ and $\varepsilon$; it interprets ZF, and its consistency was an open problem.

The core is a diagonal theorem: comprehension alone refutes every formula that is *asymmetric* between the two membership relations, and this needs neither mixed extensionality nor classical logic. Mixed extensionality and classical logic are used only to show that the ordinals are asymmetric.

| Path | Content |
|---|---|
| `pdf/` | The paper, English (`dest-inconsistency.en.pdf`) and Chinese (`dest-inconsistency.zh.pdf`) |
| `tex/` | LaTeX sources of both versions and the build script `build.sh` |
| `blind-test/diagonal-summary.zh.png` | One-page summary of the diagonal, the input of the second blind formalization |
| `agda/DESTInconsistency.agda` | Agda formalization: one file, no imports |
| `lean/` | Lean 4 formalization: no libraries; `Probes.lean` holds sanity checks |

## Checking the proofs

**Agda** (tested with 2.8.0.2), in the `agda` directory:

```
agda --safe --no-libraries DESTInconsistency.agda
```

Sections 0–1 of the file (logic, syntax, the two readings, the axioms, asymmetry) and the statements in Section 4 are the trusted part. The theorems are:
- `diagonal : (M : Set) (E : Rel M) → Comp M E → … → Opp b c → ¬ Asymmetric E P ρ b c` (no ME, no DNE)
- `inconsistent : (M : Set) (E : Rel M) → DEST⁻ M E → DNE → ⊥`
- `DEST-inconsistent : (M : Set) (E : Rel M) → DEST M E → DNE → ⊥`

`DEST⁻` is ME + COMP; `DNE` is double-negation elimination, i.e. classical logic.

**Lean 4**, in the `lean` directory (the toolchain `v4.36.0` is pinned in `lean-toolchain`; there are no dependencies):

```
lake build
```

Part I and the statements in Part III of `DESTInconsistency.lean` are the trusted part; they are reproduced in Appendix A of the paper. For the main file, the build prints:

```
'DEST.diagonal' does not depend on any axioms
'DEST.inconsistent' does not depend on any axioms
'DEST.DEST_inconsistent' does not depend on any axioms
'DEST.inconsistent'' depends on axioms: [propext, Classical.choice, Quot.sound]
'DEST.DEST_inconsistent'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`inconsistent` takes classical logic as the explicit hypothesis `∀ P : Prop, ¬¬P → P`; the primed versions use Lean's built-in classical logic instead. `lake env leanchecker DESTInconsistency` re-checks the compiled development.

## Building the paper

In the `tex` directory:

```
./build.sh          # both PDFs, to ../pdf
```

The script first runs `gen_codelinks.py`, which regenerates the code links and the code excerpts from `agda/` and `lean/`, then builds the PDFs with [Tectonic](https://tectonic-typesetting.github.io/); `latexmk -xelatex` with TeX Live (`ctex`, DejaVu Sans Mono) works as well. The Chinese PDF uses the macOS fonts Songti SC, Heiti SC, and Kaiti SC when present, and otherwise Noto CJK or the Fandol fonts that come with TeX.

## Authorship and AI use

Corresponding author: Peter Zhang (peterzhangsg@gmail.com). The research was led by him and carried out with AI systems: ChatGPT (Astra 6.2, OpenAI) and Claude (Anthropic). Their roles are described in the paper's tool and computational resource disclosure.

## Citation

See [`CITATION.bib`](CITATION.bib).

## License

All files are licensed under [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/). The full text is in [`LICENSE`](LICENSE).

© 2026 Bedrock Institute.

---

# 弱双面外延集合论不一致

我们证明了 Kisielewicz 的弱双面外延集合论 DEST 不一致：仅混合外延性与概括这两条公理就已互相矛盾，其中概括只允许均质（regular）参数。DEST 有 $\in$、$\varepsilon$ 两种成员关系，能解释 ZF，其一致性此前一直是开放问题。

核心是一条对角定理：单凭概括就能驳倒一切在两种成员关系之间「不对称」的公式，而且这一定理的证明既不需要混合外延性，也不需要经典逻辑。混合外延性与经典逻辑只用来证明序数不对称。

| 路径 | 内容 |
|---|---|
| `pdf/` | 论文：中文 `dest-inconsistency.zh.pdf`，英文 `dest-inconsistency.en.pdf` |
| `tex/` | 两版论文的 LaTeX 源文件与构建脚本 `build.sh` |
| `blind-test/diagonal-summary.zh.png` | 对角论证的一页摘要，即第二次盲测形式化的输入 |
| `agda/DESTInconsistency.agda` | Agda 形式化：单文件，不导入任何模块 |
| `lean/` | Lean 4 形式化：不依赖任何库；`Probes.lean` 做了几项辅助核对，详见论文第 6 节 |

核对证明与构建论文的命令及说明见上文英文部分：在 `tex/` 下运行 `./build.sh`，即可生成两份 PDF。中文 PDF 优先使用 macOS 自带的宋体、黑体、楷体，没有时自动换成思源或 TeX 自带的 Fandol 字体。

**作者与 AI 使用。** 通讯作者：Peter Zhang（peterzhangsg@gmail.com）。研究由他主导，借助 ChatGPT（Astra 6.2，OpenAI）与 Claude（Anthropic）完成，分工见论文的「工具与计算资源说明」（附录 B）。

**引用。** 见 [`CITATION.bib`](CITATION.bib)。

**许可。** 全部文件以 [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) 许可发布，全文见 [`LICENSE`](LICENSE)。

© 2026 Bedrock Institute。
