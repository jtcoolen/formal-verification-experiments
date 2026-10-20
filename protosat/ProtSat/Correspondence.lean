/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Query
import ProtSat.BoundedExec
import ProtSat.Represent
import ProtSat.Resolution
import ProtSat.BoundedCert
import ProtSat.EndToEnd

/-!
# ProtSat: the correspondence, stated once and generally (roadmap stages 5 and 6)

`Differential.lean` verified the correspondence on two protocols. This module states it for *every*
gap-free query, and then feeds it the evidence format from `Resolution.lean`, so the CNF route's
safety verdict rests on a checked refutation rather than on a solver answer:

```lean
encoding_complete_gapFree :
  domainGap P B = false -> boundedAttackGoals q -> Satisfiable (encode P B)

boundedSafe_of_unsat_gapFree :
  domainGap P B = false -> Unsat (encode P B) -> boundedSafeGoals q

boundedSafe_of_refutation :
  domainGap P B = false -> checkProof (encode P B) p = true -> boundedSafeGoals q
```

The second is the objective's implication - no satisfying assignment, therefore no permitted
execution violating the selected goal - with the representability condition discharged by a
decidable property of the query instead of an assumption about the runs. The third replaces the
solver answer by evidence: nothing in its proof re-runs the search.

The other side of "the verdict means what it says" - an `attack` answer really is an attack - is
not established here and does not need the encoding: `BoundedCert.checkBounded_sound` re-derives
every transition and the bounds from the certificate alone, independently of the CNF and the
solver. So false positives are excluded by the certificate checker and false negatives by the
theorems below.

The other direction is closed in `ProtSat/Sound.lean`: `decoding_runsInUniverse` proves the
decoded run stays inside the universe, so `encoding_sound` now yields the *complete* bounded
predicate and `Sound.encoding_correct` states the equivalence both ways for a gap-free query.
What still bounds it is the goal, not the direction: `Encode.violationLits` names leak literals
only, so the CNF route speaks about secrecy, and a query selecting agreement is refused rather
than answered.
-/

namespace ProtSat.Correspondence

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  Resolution

/-- **Completeness, no hypotheses about the execution.** For a gap-free query, every permitted
execution that violates the selected goal yields a satisfying assignment of the generated
formula. `WithinBounds` is not assumed: `BoundedExec.withinBounds_of_bounded` derives it from the
public bound and the query's gap check. -/
theorem encoding_complete_gapFree {P : Protocol} {B : Bounded.Bounds}
    (hgap : domainGap P B = false) (hU : univClosed (shapeOf P B) P)
    (hsec : SecretsOK (shapeOf P B) P)
    (h : boundedAttackGoals (Query.mk P B [Goal.secrecy])) :
    Satisfiable (encode P B) := by
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := h
  have hgeq : g = Goal.secrecy := by simpa using hg
  subst hgeq
  rw [violation_secrecy] at hv
  exact encoding_complete (P := P) (B := B) (tr := tr) (Cs := Cs) hU hsec
    hbt.1 hbt.2.1 hv (withinBounds_of_bounded hbt hgap)

/-- **The implication the objective asks for.** No satisfying assignment, therefore no permitted
execution violating the selected goal - for every gap-free query. This is
`boundedSafe_of_encodingUnsat_of_gapFree` with the analyser's verdict replaced by the semantic
property of the formula, so it no longer depends on how the answer was produced. -/
theorem boundedSafe_of_unsat_gapFree {P : Protocol} {B : Bounded.Bounds}
    (hgap : domainGap P B = false) (hU : univClosed (shapeOf P B) P)
    (hsec : SecretsOK (shapeOf P B) P)
    (h : ProtSat.Unsat (encode P B)) :
    boundedSafeGoals (Query.mk P B [Goal.secrecy]) :=
  fun hat => h (encoding_complete_gapFree hgap hU hsec hat)

/-- **Evidence, not search.** A checked resolution refutation of the generated formula is enough
to conclude bounded safety. Nothing here runs, or re-runs, a solver: the only fact about the
formula is that `checkProof` accepted a proof of it. This is roadmap stage 6's architecture
realized - search (ours or an external prover's) emits evidence, a linear check decides whether
the evidence refutes *this* formula, and the verdict follows from the check. -/
theorem boundedSafe_of_refutation {P : Protocol} {B : Bounded.Bounds}
    (hgap : domainGap P B = false) (hU : univClosed (shapeOf P B) P)
    (hsec : SecretsOK (shapeOf P B) P)
    (p : List Line) (hp : checkProof (encode P B) p = true) :
    boundedSafeGoals (Query.mk P B [Goal.secrecy]) :=
  boundedSafe_of_unsat_gapFree hgap hU hsec (checkProof_sound hp)

/-- The general theorem, instantiated on the guarded protocol from `EndToEnd`: bounded safety
derived from the formula's unsatisfiability alone, without the analyser's verdict equation. -/
theorem guard_safe_from_unsat : boundedSafeGoals EndToEnd.qg :=
  boundedSafe_of_unsat_gapFree EndToEnd.qg_gap EndToEnd.qg_hU
    EndToEnd.qg_hsec (DPLL.dpll_complete EndToEnd.qg_unsat)

/-- And the same conclusion the old bridge gives, for comparison: it needs the verdict equation,
this one needs only the semantic property of the formula. -/
theorem guard_safe_via_verdict : boundedSafeGoals EndToEnd.qg := EndToEnd.qg_safe

/-- The false-positive side, for completeness of the story: an accepted *bounded* certificate is
a permitted execution, re-derived from the certificate alone with no reference to the CNF. -/
theorem boundedAttack_of_checkBounded {P : Protocol} {B : Bounded.Bounds} {c : Certificate}
    (h : BoundedCert.checkBounded P B c = true) : BoundedAttack P B :=
  BoundedCert.checkBounded_sound h

end ProtSat.Correspondence