# Weak double extension set theory is inconsistent

**English** · [中文](README.zh.md)

We prove that Kisielewicz's weak double extension set theory DEST is inconsistent: already two of its axioms, mixed extensionality (ME) and comprehension with regular parameters (COMP), contradict each other. DEST has two membership relations, $\in$ and $\varepsilon$; it interprets ZF, and its consistency was an open problem.

The core is a diagonal theorem: comprehension alone refutes every formula that is *asymmetric* between the two membership relations, and this needs neither mixed extensionality nor classical logic. Mixed extensionality and classical logic are used only to show that the ordinals are asymmetric.

| Path | Content |
|---|---|
| `pdf/` | The paper, English (`dest-inconsistency.en.pdf`) and Chinese (`dest-inconsistency.zh.pdf`) |
| `tex/` | LaTeX sources of both versions and the build script `build.sh` |
| `blind-test/diagonal-summary.zh.png` | One-page summary of the diagonal, the input of the second blind formalization |
| `blind-test/intuitionistic-input.md` | Input of the third blind formalization: Sections 1–5 of the first version of the paper as plain text, and a draft of the intuitionistic proof in Chinese. The lines mentioning the code were filtered out, which also removed the first line of each definition, theorem, lemma and proposition, and two lines of the draft |
| `blind-test/intuitionistic.lean` | Output of the third blind formalization: a Lean 4 formalization of the intuitionistic proof; check with `lean intuitionistic.lean` (Lean v4.36.0) |
| `agda/DESTInconsistency.agda` | Agda formalization: one file, no imports |
| `lean/` | Lean 4 formalization: no libraries; `Probes.lean` holds sanity checks |
| `agda/Intuitionistic.agda`, `lean/Intuitionistic.lean` | Additional code: a variant of the proof that uses no classical logic, with a different ordinal formula (paper, Sections 2 and 6) |
| `agda/Supplement.agda` | Additional code: `kisielewicz-strict`, `me-localized`, `irregular-ordinals`, cited in Sections 1, 5 and 8 of the paper |

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

The additional Agda files are checked in the same way:

```
agda --safe --no-libraries Intuitionistic.agda
agda --safe --no-libraries Supplement.agda
```

`Intuitionistic.agda` has the trusted part of the main file without `DNE`; its theorems `inconsistent` and `DEST-inconsistent` take no `DNE` hypothesis. `Supplement.agda` imports nothing either; its trusted part is Sections 0–2 (Sections 0–1 and the ordinal formula of the main file, verbatim, and five definitions used in the statements) and the statements in Section 4 of `kisielewicz-strict`, `irregular-ordinals` and `me-localized`.

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

`lake build` also builds the additional file `Intuitionistic.lean`, whose trusted part is that of the main file without the classical hypothesis. For it, the build prints:

```
'DEST.diagonal' does not depend on any axioms
'DEST.inconsistent' does not depend on any axioms
'DEST.DEST_inconsistent' does not depend on any axioms
```

`lake env leanchecker Intuitionistic` re-checks it.

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
