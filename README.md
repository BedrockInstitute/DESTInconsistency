# Weak double extension set theory is inconsistent

**English** · [中文](README.zh.md)

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

Corresponding author: Peter Zhang (peterzhangsg@gmail.com). The research was led by him and carried out with AI systems: ChatGPT (Astra 6.2, OpenAI) and Claude (Anthropic). Their roles are described in the paper's statement on the use of AI.

## Citation

See [`CITATION.bib`](CITATION.bib).

## License

All files are licensed under [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/). The full text is in [`LICENSE`](LICENSE).

© 2026 Bedrock Institute.
