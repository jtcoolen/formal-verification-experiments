# Follow-up verification, 18 October 2026

Reviewed commit `b4786a9fdc86644e6b5743992a4c9afb1dad28cd`. The substantive proof and implementation gaps in the original review have been addressed. No correctness blocker was found in this follow-up.

The project now supports the description **a formally verified LL(1) table generator and total generated start-symbol parser for finite alphabets**. Its exact-tree correctness and automatic-fuel guarantees apply whenever its conflict check passes. The classical checker characterization assumes a reduced grammar; the start-parser guarantee does not require reduction, well-formedness or language membership.

| Original requirement | Current result |
|---|---|
| Independent classical LL(1) characterization | `Classical.lean:290`, `Grammar.ll1Check_iff_classicalLL1` |
| Reachable selected-cycle acyclicity | `SelectedLC.lean:474`, `Grammar.noSelectedLCCycle` |
| Checked generation and real conflict reporting | `Generate.lean:105`, `generate_iff_Ll1`, `generate_conflict` |
| Executable fuel chooser | `Fuel.lean:695`, `Grammar.fuelFor` |
| No fuel exhaustion on valid or invalid input | `Fuel.lean:735`, `Grammar.parseGenerated_ne_outOfFuel` |
| Exact-tree soundness and completeness at chosen fuel | `Fuel.lean:795`, `Grammar.parseGenerated_iff` |
| Correct language decision procedure | `Fuel.lean:836`, `Grammar.decideMembership_iff` |

The original `Table.lean` and `Generator.lean` specifications were not weakened. The new classical predicate retains the independent successful-leftmost-derivation definition. The fuel-bound proof handles failed executions through successful-prefix and input-suffix invariants; it does not assume a finite matching forest for the entire residual input.

## Independent checks

- `lake build` succeeded, 69 jobs including replayed outputs.
- Fresh Lean checks succeeded for `Classical.lean`, `Generate.lean`, `SelectedLC.lean`, `Exec.lean`, `Fuel.lean` and `Examples/FuelChecks.lean`. Some unused-variable/simp linter warnings remain.
- A fresh `Axioms.lean` audit printed 248 dependency lists. Their axiom names were only `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, custom axiom or audit error appeared. Output is `followup-axioms.log`.
- `FollowupFuel.lean` independently restates the original fuel target and proves it for `G.fuelFor`. It additionally proves that a returned error under the LL(1) check is not fuel exhaustion and implies nonmembership.
- `FollowupContracts.lean` proves successful checked generation returns a `Correct` table, and that both actual reported RHSs belong to the grammar and SELECT the reported lookahead. These are stronger convenience corollaries than the currently exported result statements and require no implementation changes.

Recheck the independent probes from `ll1/`:

```
lake env lean review-2026-10-18/FollowupFuel.lean
lake env lean review-2026-10-18/FollowupContracts.lean
```

## Remaining qualifications and cleanup

- The totality guarantee concerns parsing from the start symbol. Arbitrary unreachable subparser roots can still loop until their fuel expires; this is an intentional scope qualification with a formal counterexample.
- `parseGenerated` and raw `genTable` are callable on unchecked grammars; their completeness and no-exhaustion guarantees require `ll1Check = true`. The new `generate` API enforces conflict rejection.
- Duplicate identical RHS productions are identified, matching the repository's grammar/tree semantics rather than the pasted specification's distinct rule IDs.
- The computed fuel is a conservative recursion-depth bound, not a proved runtime-complexity theorem.
- Documentation still overstates a converse at `SelectedLC.lean:16` and `README.md:845`: a selected graph cycle need not cause an actual loop if a nullable prefix rejects first. The proved descent-to-edge direction and acyclicity argument are sound. Old claims that productivity is needed for the stopping-form FIRST lemma, and that stopping lengths agree in any grammar, should also be updated to match the strengthened theorems.
- Exporting the stronger exact conflict and table-correctness corollaries from `FollowupContracts.lean` would make the public contracts clearer.

These remaining items do not reopen the original correctness or termination gap. The earlier review documents are historical snapshots; their open-target descriptions have been superseded by the results above.
