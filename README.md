# Weak double extension set theory is inconsistent

**English** · [中文](README.zh.md)

We prove that Kisielewicz's weak double extension set theory DEST is inconsistent: already two of its axioms, mixed extensionality (ME) and comprehension with regular parameters (COMP), contradict each other. DEST has two membership relations, $\in$ and $\varepsilon$; it interprets ZF, and its consistency was an open problem.

The core is a diagonal theorem: comprehension alone refutes every formula that is *asymmetric* between the two membership relations, and this needs neither mixed extensionality nor classical logic. In the main proof, mixed extensionality and classical logic are used only to show that the ordinals are asymmetric. A variant of the proof with a different ordinal formula uses no classical logic at all, so the two axioms contradict each other even in intuitionistic logic; it is formalized as additional code in `agda/Intuitionistic.agda` and `lean/Intuitionistic.lean`.

## Papers

1. **Weak double extension set theory is inconsistent** (November 2026). [English PDF](pdf/dest-inconsistency.en.pdf) · [Chinese PDF](pdf/dest-inconsistency.zh.pdf) · [BibTeX](CITATION.bib)

## Checking the proofs

Agda 2.8.0.2, in the `agda` directory:

```
agda --safe --no-libraries DESTInconsistency.agda
agda --safe --no-libraries Intuitionistic.agda
agda --safe --no-libraries Supplement.agda
```

Lean 4, in the `lean` directory; the toolchain v4.36.0 is pinned and there are no dependencies:

```
lake build
lake env leanchecker DESTInconsistency
lake env leanchecker Intuitionistic
```

Section 6 of the paper says which parts of the files are trusted, which theorems they prove, and what else was checked. The inputs and outputs of the blind formalizations described there are in `blind-test/`; the Lean one is checked with `lean intuitionistic.lean`.

## Building the paper

In the `tex` directory, `./build.sh` regenerates the code links and excerpts from `agda/` and `lean/`, then builds both PDFs into `pdf/` with [Tectonic](https://tectonic-typesetting.github.io/). `latexmk -xelatex` with TeX Live, `ctex` and DejaVu Sans Mono works as well.

## License

All files are licensed under [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/); the full text is in [`LICENSE`](LICENSE). © 2026 Bedrock Institute.
