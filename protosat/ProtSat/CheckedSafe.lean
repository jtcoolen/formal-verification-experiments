/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Correspondence
import ProtSat.Serialize

/-!
# ProtSat: a safety verdict that comes from evidence, not from a solver run

## Why this module exists

The objective is that SAFE mean: no execution permitted by the stated model, assumptions and
bounds violates any selected goal. `Correspondence.lean` reaches that conclusion from
`Unsat (encode P B)` - a semantic property of the formula - and `Resolution.lean` plus
`Serialize.lean` decide whether a certificate refutes a formula without running any search.
This module joins the two ends at the level of a `Query`, so the whole chain is one theorem:

    bytes -> proofOfCode -> checkProof -> Unsat -> boundedSafeGoals q

    boundedSafe_of_checkedProof :
      checkProof (encode q.protocol q.bounds) p = true -> boundedSafeGoals q
    boundedSafe_of_checkedCode :
      checkCode (encode q.protocol q.bounds) k c = true -> boundedSafeGoals q

It also does something the analyser cannot: it constructs a `SafeEvidence`. `Query.lean` records
that nothing builds one yet, because `analyzeQuery` answers through a solver. Checked evidence is
a different input, and it yields the verdict directly.

## The goal-selection condition

The CNF encodes secrecy only: `Query.goalEncoded` is true of `Goal.secrecy` and of nothing else,
and a query selecting agreement is refused with `unsupportedGoals` rather than answered. The
theorems here therefore take `hq : ∀ g ∈ q.goals, goalEncoded g` and `hne : q.goals ≠ []`, and
`boundedSafeGoals_of_secrecy` is the transfer that makes them mean what they say: under those two
conditions, safety for the secrecy-only query IS safety for q, because every goal q selected is
secrecy. Without `hq` the transfer is false, and the module says so rather than hiding it.

## What this does not do

It does not produce the evidence. Producing a refutation of a real protocol formula is the prover,
which does not exist yet; the theorems below are the socket it plugs into. Nor does it remove the
representability condition: `domainGap q.protocol q.bounds = false` is still a hypothesis, now a
decidable property of the query rather than an assumption about its executions.
-/

namespace ProtSat.CheckedSafe

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  Resolution Serialize

/-- **Transferring across the goal set.** If every goal `q` selected is one the encoding represents
- in practice, secrecy - then a proof that the secrecy-only query is safe is a proof that `q` is
safe. The hypothesis is doing real work: a query that selects agreement can be safe for secrecy
and attacked for agreement, so the statement is false without it. -/
theorem boundedSafeGoals_of_secrecy {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (_hne : q.goals ≠ [])
    (h : boundedSafeGoals (Query.mk q.protocol q.bounds [Goal.secrecy])) :
    boundedSafeGoals q := by
  intro hat
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := hat
  have he : goalEncoded g = true := hq g hg
  rw [goalEncoded_iff] at he
  subst he
  exact h ⟨Goal.secrecy, by simp, tr, Cs, hbt, hv⟩

/-- **The implication the objective asks for, at the level of a query.** No satisfying assignment
of the formula generated for `q`, therefore no permitted execution of `q` violating a goal `q`
selected. The representability condition is the decidable `domainGap`, not a hypothesis about the
runs. -/
theorem boundedSafeGoals_of_unsat {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    (h : ProtSat.Unsat (encode q.protocol q.bounds)) : boundedSafeGoals q :=
  boundedSafeGoals_of_secrecy hq hne
    (Correspondence.boundedSafe_of_unsat_gapFree hgap hU hsecStore h)

/-- **From a checked refutation to the verdict.** The formula fact is supplied by the independent
checker: `checkProof` walked a list of resolution steps and accepted. No solver appears anywhere
in the chain. -/
theorem boundedSafe_of_checkedProof {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) {p : List Line}
    (hp : checkProof (encode q.protocol q.bounds) p = true) : boundedSafeGoals q :=
  boundedSafeGoals_of_unsat hq hne hU hsecStore hgap (checkProof_sound hp)

/-- **From serialized evidence to the verdict.** The input is a flat list of integers - what a
prover would write to disk - and the conclusion is the security statement for the query. This is
the architecture the roadmap asks for, closed end to end except for the producer. -/
theorem boundedSafe_of_checkedCode {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) {k : Nat} {c : List Int}
    (hc : checkCode (encode q.protocol q.bounds) k c = true) : boundedSafeGoals q :=
  boundedSafeGoals_of_unsat hq hne hU hsecStore hgap (checkCode_sound hc)

/-- **A safety verdict with its evidence.** `SafeEvidence` pairs the statement with the query it is
about, so a verdict cannot be detached from the question it answers. `Query.lean` notes that
nothing constructs one; this does, from a checked refutation. -/
def safeEvidenceOfProof {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) (p : List Line)
    (hp : checkProof (encode q.protocol q.bounds) p = true) : SafeEvidence where
  query := q
  safe := boundedSafe_of_checkedProof hq hne hU hsecStore hgap hp

/-- The evidence is about the query it names - the field that makes a verdict inseparable from its
question. -/
theorem safeEvidenceOfProof_query {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) (p : List Line)
    (hp : checkProof (encode q.protocol q.bounds) p = true) :
    (safeEvidenceOfProof hq hne hU hsecStore hgap p hp).query = q := rfl

/-- And an answer built from that evidence is a security answer, by the definition the contract
uses to tell security verdicts apart from formula facts. -/
theorem boundedSafe_is_security {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) (p : List Line)
    (hp : checkProof (encode q.protocol q.bounds) p = true) :
    securityResult (Result.boundedSafe
      (safeEvidenceOfProof hq hne hU hsecStore hgap p hp)) = true :=
  rfl

/-- **The shape of the end-to-end claim on a real protocol.** For the guarded example of
`EndToEnd.lean` - well-formed, gap-free, secrecy selected - any code the checker accepts for its
formula yields a bounded-security theorem about that protocol. The only thing missing is a prover
that emits such a code; the conclusion no longer mentions a solver. -/
theorem qg_safe_of_code (k : Nat) (c : List Int)
    (h : checkCode (encode EndToEnd.qg.protocol EndToEnd.qg.bounds) k c = true) :
    boundedSafeGoals EndToEnd.qg :=
  boundedSafe_of_checkedCode (by decide) (by decide) EndToEnd.qg_hU
    EndToEnd.qg_hsec EndToEnd.qg_gap h

end ProtSat.CheckedSafe
