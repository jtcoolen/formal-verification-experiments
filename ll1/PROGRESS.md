# Progress log — closing the review's six stages

Reference for the work items: `review-2026-10-18/REVIEW.md` and
`review-2026-10-18/LL1Specification.lean`.

## Status: all six stages are closed

| # | item | state | where |
|---|------|-------|-------|
| 1 | classical characterization `Reduced → (ll1Check = true ↔ ClassicalLL1)` | **done** | `VerifiedLL1/Classical.lean` (`Grammar.ll1Check_iff_classicalLL1`) |
| 2 | `G.Ll1 → G.Occurs A → ¬ G.SelectedLCPath x A A` | **done** | `VerifiedLL1/SelectedLC.lean` (`Grammar.noSelectedLCCycle`, `reachableSelectedLCAcyclic`) |
| 3 | execution invariants + a numeric recursion bound covering invalid inputs | **done** | invariants `VerifiedLL1/Exec.lean`; bound `VerifiedLL1/Fuel.lean` (`fuel_not_outOfFuel`) |
| 4 | executable `fuelFor`, `FuelBound`, `parseGenerated` | **done** | `VerifiedLL1/Fuel.lean` (`Grammar.fuelFor_bound`, `decideMembership_iff`) |
| 5 | checked generation returning a table or a named conflict | **done** | `VerifiedLL1/Generate.lean` (`generate`, `generate_iff_Ll1`, `generate_conflict`) |
| 6 | integrate + audit | **done** | `VerifiedLL1.lean` imports, `Examples/FuelChecks.lean`, `Axioms.lean`, `axioms.log`, README Phase 5.7 |

Fuel monotonicity for *every* outcome but `outOfFuel` (stage 4's second requirement) was
already proved in `Completeness.lean`: `fuel_stable`, `parseForest_stable`, `parseSym_stable`,
`parseForest_error_stable`, `parseSym_error_stable`, `parse_stable`,
`parseForest_eq_of_not_outOfFuel`. The new bound composes with the existing soundness
(`Parser.parse_sound`) and exact-tree completeness (`Grammar.generated_parse_tree`) through
`parse_eq_of_not_outOfFuel` — nothing had to be rebuilt.

`review-2026-10-18/UnreachableSelectedCycle.lean` keeps the reachability requirement honest:
with `S → a; U → U b | ε` the checker passes and the subparser for `U` on `b` exhausts every
fuel, so any global (unrestricted) version of stage 2 or 3 is false.
`Examples/FuelChecks.lean` proves that the same grammar's *start* parser terminates on `[a]`,
`[b]` and `[]` — exactly the scope of the proved bound.

## The counting argument (stage 3/4, as implemented)

Fuel is the length of a call path, and every call on a path except the last one succeeded.
With `n = G.numVars` and `W = G.maxRhsLen`:

```
muS l k    = (l * (n + 2) + k) * (W + 1) + 1      -- symbol call
muF l kb m = (l * (n + 2) + kb) * (W + 1) + m + 1 -- forest call
```

* `ChainBdd x A kb`: every selected chain at lookahead `x` from `A` has at most `kb` nodes.
  Under `Ll1` a chain from an occurring `A` is duplicate-free (stage 2), and the pigeonhole
  makes `n + 1` a universal budget (`chainBdd_universal`).
* `Budget x kb syms`: every variable of `syms` whose prefix *inside* `syms` erases has that
  budget. Variables behind a non-erasable prefix are only reachable after a token has been
  consumed, so they get the universal budget plus a strictly shorter input.
* Expansion: `muF l (kb-1) |rhs| ≤ muS l kb - 1` because `|rhs| + 1 ≤ W + 1` — this is where
  production width enters. A sibling that consumed nothing keeps the budget and drops `m`.
  A sibling that consumed a token resets the budget to `n + 1`, paid for by one whole input
  block `(n+2)*(W+1)`.
* `AllOccurs rhs` after an expansion follows from `Occurs A` plus `(A, rhs) ∈ productions`,
  so no `Reachable` hypothesis is needed and the argument covers failing runs.

## API added by stage 4

```lean
Grammar.fuelFor        G ws = G.muF (ws.length + 1) (G.numVars + 1) 1
Grammar.parseGenerated G ws = Parser.parse G G.genTable (G.fuelFor ws) (ltoks ws ++ [LTok.eof])
Grammar.FuelBound      G fuelFor   -- the review's FuelBoundTarget, as a property
Grammar.fuelFor_bound  : G.ll1Check = true → G.FuelBound G.fuelFor
Grammar.decideMembership / Grammar.decideMembership_iff
```

No `Reduced`, no `wellFormed`, and the success side is the exact-tree statement, not an
existential.

## Verification

```
cd ll1 && lake build                 # clean
lake exe verifiedLL1Demo             # prints the Phase 5.7 fuel and parse results
lake env lean Axioms.lean            # 247 declarations, only propext / Classical.choice / Quot.sound
```

The audit output is stored in `ll1/axioms.log`. `Examples/FuelChecks.lean` checks four
grammars by `rfl`/`decide` — EOF selection, repeated nullable siblings, right recursion, the
unreachable selected cycle, trailing input and invalid input — with the kernel itself running
the parser at the fuel `fuelFor` chooses.

## Still open (recorded in README "Remaining work")

* Tighter constants: the bound is deliberately conservative (a whole `(n+2)*(W+1)` block per
  token); a per-lookahead rank on the selected relation would shrink it.
* `ClassicalLL1` is characterized only under `Reduced`; the exact boundary is unknown.
* Representation speed-ups (indexed productions, a smaller FIRST carrier).
