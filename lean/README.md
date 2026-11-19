# Lean 4 formalization

Comprehension alone refutes every asymmetric formula (`diagonal`, with no mixed extensionality and no classical logic); classical ME + regular-parameter COMP has no model (`inconsistent`), and hence neither has full DEST. See `../pdf/dest-inconsistency.en.pdf`.

- `DESTInconsistency.lean`. Part I (syntax, the two readings, the axioms, asymmetry) and the statements in Part III are the trusted part. Part II is the proof; the file ends with `#print axioms`.
- `Intuitionistic.lean`. Additional code: ME + regular-parameter COMP has no model, without classical logic, with another variant of the ordinal formula (paper, Sections 2 and 6). Its trusted part is that of the main file without the classical hypothesis.
- `Probes.lean`. Sanity probes, not imported by the main file. They show three things:
  - ME together with the Russell instance has a one-point model;
  - ME plus comprehension without the regular-parameter condition is inconsistent;
  - comprehension with same-sided (non-crossed) faces is inconsistent by itself.
- Toolchain: `leanprover/lean4:v4.36.0`, pinned in `lean-toolchain`. No Mathlib and no other dependency, so `lake-manifest.json` lists no packages.

## Check

```
rm -rf .lake
lake build                                 # builds all three files and prints the #print axioms output
lake env leanchecker DESTInconsistency     # re-checks the compiled development
lake env leanchecker Intuitionistic        # the same for the additional file
```

Expected `#print axioms` output for the main file:

```
'DEST.diagonal' does not depend on any axioms
'DEST.inconsistent' does not depend on any axioms
'DEST.DEST_inconsistent' does not depend on any axioms
'DEST.inconsistent'' depends on axioms: [propext, Classical.choice, Quot.sound]
'DEST.DEST_inconsistent'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`inconsistent` takes classical logic as the explicit hypothesis `∀ P : Prop, ¬¬P → P`. The primed theorems use Lean's built-in `Classical.byContradiction` instead.

Expected `#print axioms` output for `Intuitionistic.lean`:

```
'DEST.diagonal' does not depend on any axioms
'DEST.inconsistent' does not depend on any axioms
'DEST.DEST_inconsistent' does not depend on any axioms
```

The three main theorems were also re-checked with the independent kernel nanoda 0.4.17 (shipped with the toolchain as `nanoda_bin`), on an export made with `leanexport`, with no axioms permitted; so were the three theorems of `Intuitionistic.lean`.
