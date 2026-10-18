# Status of this review folder — updated 18 Oct 2026

This folder is the reviewer's snapshot; nothing in it was rewritten.  Two notes for anyone
re-checking it against the current tree.

## 1. `LL1Specification.lean` no longer elaborates *alongside* the library

The library adopted the artifact's definitions and forward theorems under the same names
(`VerifiedLL1.Grammar.ClassicalLL1`, `classicalLL1_of_ll1`, `classicalLL1_of_ll1Check` in
`VerifiedLL1/Classical.lean`), so re-checking the artifact now reports duplicate
declarations:

```
lake env lean review-2026-10-18/LL1Specification.lean
error: `VerifiedLL1.Grammar.ClassicalLL1` has already been declared
```

That is adoption, not breakage: the artifact's `ClassicalLL1` is *the* definition the
characterization theorem uses.  The other four Lean artifacts in this folder still check
clean against the current build (`AnalysisConventions`, `UnreachableSelectedCycle`,
`UncheckedGenerator`, `ProgressLimitation`).

## 2. Both recorded targets are now theorems

| artifact name | now proved as | module |
|---|---|---|
| `Grammar.ClassicalLL1CharacterizationTarget` | `Grammar.ll1Check_iff_classicalLL1` | `VerifiedLL1/Classical.lean` |
| `Grammar.FuelBoundTarget` | `Grammar.fuelFor_bound`, with the executable `Grammar.fuelFor` | `VerifiedLL1/Fuel.lean` |
| the proposed `SelectedLCPath` acyclicity | `Grammar.noSelectedLCCycle`, `Grammar.reachableSelectedLCAcyclic` | `VerifiedLL1/SelectedLC.lean` |
| the proposed checked generator | `Grammar.generate`, `Grammar.generate_iff_Ll1`, `Grammar.generate_conflict` | `VerifiedLL1/Generate.lean` |
| the `SelectedLeftCorner` / `SelectedLCPath` definitions of `UnreachableSelectedCycle.lean` | the same, moved into the library | `VerifiedLL1/SelectedLC.lean` |

The start-parser guarantee does *not* assume `Reduced` or `wellFormed`, and its success half
is the exact-tree statement, as the artifact required.  `axioms.log` in this folder is the
audit as of the review; the current audit is `ll1/axioms.log`.

## Reproduce

```
cd ll1
lake build                                    # library + demo + axioms exe, 69 jobs
lake exe verifiedLL1Demo                      # the Phase 5.7 block prints fuel and parses
lake env lean Axioms.lean                     # every declaration, standard axioms only
lake env lean review-2026-10-18/AnalysisConventions.lean
```
