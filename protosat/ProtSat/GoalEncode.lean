/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.AuthClauses
import ProtSat.DecodeIndex
import ProtSat.Sound

/-!
# ProtSat/GoalEncode.lean - the goal-indexed formula

## What this file is

`ProtSat.Encode.violationLits` (ProtSat/Clauses.lean:679) names leak literals and nothing else, so
the generated CNF can only ever ask "does a declared secret reach the attacker?".
`ProtSat/AuthClauses.lean` proved that you cannot repair that by CONJUNCTION: on the AuthGap model
the secrecy violation clause is the empty clause (`authEncode_not_sat`), so anything conjoined with
it is unsatisfiable however good the new clauses are. The violation GROUP has to be chosen by the
goals the query selected.

This file is that step, done additively: `encodeGoalsOf P B gs` is the ten semantic groups of
`Encode.encodeGroups` plus the violation group `gs` asks for. Nothing existing changes - `encode
P B` still means what it means today, and every theorem of `Complete.lean` / `Sound.lean` keeps its
statement.

* `encodeGoalsOf_secrecy` : `encodeGoalsOf P B [Goal.secrecy] = encode P B`, **by `rfl`** - the
  byte-identical regression gate.
* `encodeGoalsOf_nil` : `encodeGoalsOf P B [] = baseEncode P B`, also by `rfl`, with
  `empty_goals_are_strictly_weaker` saying what that case means and proving it is a different
  question, not a security answer.
* `encodeGoalsOf_agreement` : `encodeGoalsOf P B [Goal.agreement] = agreementEncode P B`, so the
  `AuthClauses.Diff` gates become gates about the goal-indexed formula (`Diff.*_goals`).
* `encoding_correct_goals` : the correspondence for the secrecy goal, obtained by REWRITING
  `Sound.encoding_correct` with the first gate - nothing is reproved.

## The design decision the task left open

`Goal` has three constructors and nowhere to record *which agreement monitor* is meant, but
`AuthClauses` has two: `Matching.orderAware` (a commit is excused only by a strictly earlier claim,
mirroring `ProtSat.Reference.claimMatches`) and `Matching.tripleOnly` (a commit is excused by any
claim of the same tag, peer and value, mirroring `ProtSat.AuthBreak`). The selector therefore
**cannot be expressed as a `Goal`** and it stays a parameter: `encodeGoalsOf` fixes the repository
default `orderAware` - so that the equation with `agreementEncode P B orderAware` holds exactly -
and `encodeGoalsOfM` exposes it.

Which selector pairs with `Goal.agreement` depends on the semantics, and the two disagree:

* `Query.Violation P Goal.agreement Cs tr` is `ProtSat.AuthBreak P Cs tr` - **unordered**,
  triple-only. That is what `boundedAttackGoals` is built from, so it is the target of any
  correspondence stated in `Query`'s vocabulary, and it pairs with `Matching.tripleOnly`.
* `ProtSat.Reference.authBreak`, the monitor `Contract.goalViolationBool` computes, is **ordered**
  and pairs with `Matching.orderAware`.

So `Satisfiable (encodeGoalsOf P B [Goal.agreement]) -> boundedAttackGoals (Query.mk P B
[Goal.agreement])` is the wrong pairing: a commit excused by nothing but a *later* claim satisfies
the ordered clauses and refutes the unordered predicate. The sound direction proved below is stated
for `encodeGoalsOfM ... [Goal.agreement] Matching.tripleOnly`, which is the pairing `Query`
supports. Retargeting `Query.Violation` (or adding a fourth `Goal`) is a change to
`ProtSat/Query.lean` and is outside this file's scope.

## What IS proved here, theorem by theorem

| theorem | content |
|---|---|
| `encodeGoalsOf_secrecy` | `encodeGoalsOf P B [secrecy] = encode P B` **by `rfl`** - the regression gate |
| `encodeGoalsOf_nil` | `encodeGoalsOf P B [] = baseEncode P B` **by `rfl`** - no violation demand at all |
| `encodeGoalsOf_agreement`, `encodeGoalsOfM_agreement` | the agreement goal is `AuthClauses.agreementEncode` |
| `encodeGoalsOf_both` | both goals is `AuthClauses.authEncode` |
| `sat_encode_of_sat` | the transport: a model of a secrecy-selecting goal-indexed formula is a model of `encode P B` |
| `encoding_correct_goals` | the correspondence for the secrecy goal, by rewriting `Sound.encoding_correct` |
| `boundedAttackGoals_of_sat_goals`, `boundedAttackGoals_implies_sat_goals` | both directions for an arbitrary goal list, secrecy-only respectively |
| `boundedAttackGoals_of_sat_both` | SOUND for the two-goal query, unconditionally (the secrecy half feeds the old chain) |
| `no_attack_without_goals`, `empty_goals_are_strictly_weaker` | what the empty goal list means, and that it is not a security answer |
| `Diff.diff_*_goals` | the three `AuthClauses.Diff` differential gates, restated about `encodeGoalsOf` |
| `exists_commit_candidate`, `authOccLits_true`, `authNoExcuse` | the agreement clauses do their job: demand satisfied, selector implications correct, no excusing claim complete - all with no `Sat a (encode P B)` |
| `boundedAttackGoals_of_sat_agreement` | **SOUND for the agreement goal**, modulo `DecodedRun` - which `ProtSat/AgreesBase.lean` now discharges (`decodedRun_of_sat_agreement`), making the soundness direction unconditional apart from two shape hypotheses |
| `no_transport_from_base` | the obstruction: the bridge cannot be a one-line transport, because that transport is FALSE |
| `decodedTrace_of_sat_encode`, `decodedTrace_of_sat_goals` | the trace half of `DecodedRun` for the old formula, and for any secrecy-selecting goal list |
| `decodedTrace_is_realised` | that trace half is inhabited by a concrete solver-produced assignment, so the bridge is not a hypothesis about an empty class |
| `agreement_group_is_a_real_demand` | the agreement group is a real demand: on the ordered model it makes the goal-indexed formula unsatisfiable |

Kernel-decided gates in this file: `empty_clause_in_encode_Authentication` (`decide`, ~0.35 s of
kernel replay on a 10-core developer machine; the two `elem` decisions in `encodeGoalsOf_both` are
negligible). No gate here exceeds a second, and none bypasses the kernel.

## What is NOT proved here, and exactly why

**Update (2026-10-20): the bridge below has been discharged.** `ProtSat/AgreesBase.lean` proves
`decodedRun_of_sat_agreement` from `Sat a (encodeGoalsOfM P B [Goal.agreement] tripleOnly)` plus two
shape hypotheses (`univClosed`, `authNameable`), by re-stating the decoding cone over the ten semantic
groups - the dependency cone of `decRun_trace` is 78 lemmas and not one of them reads the violation
clause, which is why the re-statement works. So `boundedAttackGoals_of_sat_agreement` below is no
longer conditional in substance; what remains unproved in this area is the COMPLETENESS direction for
agreement, and the ordered notion of agreement, which is inexpressible over `Operational` (see
`ProtSat/AgreementPredicates.lean`). The rest of this section is kept as the record of what the
obstacle was and why the one-line transport is false.

The sound direction for agreement needs two things no lemma in the repository provides for a
goal-indexed formula. They are isolated as `DecodedRun P B a`; `decodedTrace_of_sat_encode` proves
the first component of it from `Sat a (encode P B)`, so the hypothesis has the shape the existing
machinery delivers and is not a wish.

1. **`BoundedTrace` for the decoded run.** `Encoding.decRun_trace` and `Sound.decoding_runsInUniverse`
   take `Sat a (encode P B)` - the whole formula, secrecy violation clause included. A model of the
   agreement-only formula does not supply it, and it *cannot* be supplied by any general argument:
   `no_transport_from_base` exhibits an assignment that satisfies `baseEncode P B` and does **not**
   satisfy `encode P B` (on `Regressions.Authentication.P` the secrecy violation clause is the empty
   clause, so nothing satisfies `encode P B` there at all). That is the precise reason the agreement
   soundness direction cannot reuse `Encoding`'s decoding lemmas as they stand: the missing step is
   not a gap in a proof, it is a false lemma. The only route is to re-state the decoding chain over
   the ten semantic groups. `ProtSat/DecodeIndex` already moved every lemma that did not genuinely
   need the clauses (`evAt_decEvsFrom_steps`, `cfgAt_decCfgsFrom_steps`, `decEv_act_of_decCode`,
   `decCode_of_decEv_act`); what is left is the `Agrees` induction - `agrees_zero`, `rel_agrees`
   (ProtSat/Encoding.lean:2775, the ~600 lines that discharge the introduction rules of
   `ProtSat.Rel` one by one), `agrees_decRun`, `decRunFrom_runs` - plus `decXe_eq`,
   `decodePc_of_true`/`decodePc_true`, `decCode_of_evAct` and `kn_sound`, each stated over
   `Sat a (encode P B)`. Every clause those use is a member of `baseGroups` - so nothing is lost by
   re-stating them - but it is a re-proof of the soundness direction, not a rewrite of it. That is
   the single remaining obstacle, and it is bounded work: about fifteen lemma statements, of which
   one (`rel_agrees`) is long.
2. **`CommitsReflect` and `ClaimsReflect`, the authentication half of the bridge**: that the four
   literals naming an authentication occurrence are true exactly when the decoded run performs that
   event. The clauses are proved to behave here (`exists_commit_candidate`, `authOccLits_true`,
   `authNoExcuse`); what is missing is the same `Agrees` induction again, because "the decoded run
   performs the claim at step i" needs `pcOf (decRun P B a i) q` (that is `agrees_decRun`'s first
   component) and `Expr.eval` on the decoded store (`decXe_eq`, or `Encoding.xe_konst` under
   `authNameable`, which pins a nameable annotation to a closed constant). The pieces that do *not*
   need `Agrees` are already available: `decEv_act_of_decCode` and `decCode_of_decEv_act` from
   `DecodeIndex` give the event, and `Complete.eval_eq_constVal` makes a nameable annotation's value
   independent of the store.

With those two discharged, `boundedAttackGoals_of_sat_agreement` IS the sound direction, and it is
proved below: the goal-indexed formula, the demand clause, the excuse clauses and the triple-only
excuse relation all do real work in it. What is assumed is exactly the decoded-run bridge, named.

## A correction to the pairing the task proposed

`Query.Violation P Goal.agreement` is `ProtSat.AuthBreak` - unordered, triple-only. So the sound
direction for `Goal.agreement` pairs with `Matching.tripleOnly`, not with the repository default
`Matching.orderAware`: a commit excused by nothing but a *later* claim satisfies the ordered clauses
and refutes `AuthBreak`. `boundedAttackGoals_of_sat_agreement` is therefore stated for
`encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly`. Making `Goal.agreement` denote the
ordered monitor (or adding a fourth `Goal`) is a change to `ProtSat/Query.lean`, which is outside
this file's scope.
-/

namespace ProtSat.GoalEncode

open ProtSat Term Protocol OneHot Bounded Attacker Encode Encoding Complete Query DPLL Sound
  Represent BoundedExec
open ProtSat.AuthClauses
open Protocol

/-! ### 1. The goal-indexed formula -/

/-- **The goal-indexed encoding**: the ten semantic clause groups of `Encode.encodeGroups` - the
ones that say what a run of the protocol looks like - conjoined with the violation group the
selected goals `gs` ask for. `Goal.secrecy` selects the old leak clause, `Goal.agreement` selects
the claim/commit clauses of `AuthClauses`, and a goal that is not selected contributes no clause at
all. The agreement monitor is the repository default, `Matching.orderAware`; `encodeGoalsOfM` is
the same formula with the monitor as an argument. -/
def encodeGoalsOf (P : Protocol) (B : Bounds) (gs : List Goal) : CNF :=
  encodeGoals P B gs Matching.orderAware

/-- **The goal-indexed encoding with the agreement monitor explicit.** The monitor cannot be
expressed as a `Goal`: `Goal.agreement` denotes `ProtSat.AuthBreak`, the unordered triple-only
relation, while `ProtSat.Reference.authBreak` is the ordered one. -/
def encodeGoalsOfM (P : Protocol) (B : Bounds) (gs : List Goal) (m : Matching) : CNF :=
  encodeGoals P B gs m

/-- The default is the explicit one: `encodeGoalsOf` is `encodeGoalsOfM` at `orderAware`. -/
theorem encodeGoalsOf_eq_default (P : Protocol) (B : Bounds) (gs : List Goal) :
    encodeGoalsOf P B gs = encodeGoalsOfM P B gs Matching.orderAware := rfl

/-- **THE REGRESSION GATE.** A query that selects only secrecy gets *definitionally* the formula the
whole development is stated about: `encodeGoalsOf P B [Goal.secrecy]` and `encode P B` are the same
term, not merely equivalent ones. Nothing that today type-checks about `encode P B` can be affected
by the goal index, and `rfl` is the proof of that. -/
theorem encodeGoalsOf_secrecy (P : Protocol) (B : Bounds) :
    encodeGoalsOf P B [Goal.secrecy] = encode P B := rfl

/-- **The empty-goal gate.** A query that selects nothing gets the semantic groups alone: no
violation demand of any kind, not even an empty clause. Also definitional. -/
theorem encodeGoalsOf_nil (P : Protocol) (B : Bounds) :
    encodeGoalsOf P B [] = baseEncode P B := rfl

/-- An agreement-only query is the agreement encoding of `AuthClauses`, with the default monitor. -/
theorem encodeGoalsOf_agreement (P : Protocol) (B : Bounds) :
    encodeGoalsOf P B [Goal.agreement] = agreementEncode P B Matching.orderAware :=
  encodeGoals_agreement P B Matching.orderAware

/-- An agreement-only query with an explicit monitor. -/
theorem encodeGoalsOfM_agreement (P : Protocol) (B : Bounds) (m : Matching) :
    encodeGoalsOfM P B [Goal.agreement] m = agreementEncode P B m :=
  encodeGoals_agreement P B m

/-- A query that selects both goals is `AuthClauses.authEncode` - the conjunction the earlier
prototype used, and the one that cannot work on the AuthGap model. -/
theorem encodeGoalsOf_both (P : Protocol) (B : Bounds) :
    encodeGoalsOf P B [Goal.secrecy, Goal.agreement] = authEncode P B Matching.orderAware := by
  have h1 : ([Goal.secrecy, Goal.agreement] : List Goal).elem Goal.secrecy = true := by decide
  have h2 : ([Goal.secrecy, Goal.agreement] : List Goal).elem Goal.agreement = true := by decide
  have hvg : violationGroups (shapeOf P B) P [Goal.secrecy, Goal.agreement]
        Matching.orderAware
      = [violationClauses (shapeOf P B) P]
          ++ [authViolationClauses Matching.orderAware (shapeOf P B) P] := by
    rw [violationGroups, h1, h2]
    rfl
  have key : (baseGroups (shapeOf P B) P
        ++ ([violationClauses (shapeOf P B) P]
            ++ [authViolationClauses Matching.orderAware (shapeOf P B) P])).flatMap (·.clauses) =
      (encodeGroups (shapeOf P B) P).flatMap (·.clauses)
        ++ (authViolationClauses Matching.orderAware (shapeOf P B) P).clauses := by
    rw [← List.append_assoc, List.flatMap_append, List.flatMap_append, encodeGroups_eq,
      List.flatMap_append]
    simp [List.append_nil]
  unfold encodeGoalsOf encodeGoals authEncode
  rw [hvg, key]
  rfl

/-- Every clause of the semantic groups is a clause of the goal-indexed formula, whatever the goals
are: selecting a violation never removes a fact about what a run is. -/
theorem sat_baseEncode_of_sat {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {a : Assignment} (h : Sat a (encodeGoalsOfM P B gs m)) : Sat a (baseEncode P B) := by
  intro c hc
  obtain ⟨g, hg, hgc⟩ := List.mem_flatMap.mp hc
  exact h c (List.mem_flatMap.mpr ⟨g, List.mem_append_left _ hg, hgc⟩)

/-- Any group of the goal-indexed formula - a semantic group or a selected violation group - is
satisfied by every model of it. -/
theorem sat_group_of_sat {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {g : CNF} (hg : g ∈ baseGroups (shapeOf P B) P ++ violationGroups (shapeOf P B) P gs m)
    {a : Assignment} (h : Sat a (encodeGoalsOfM P B gs m)) : Sat a g := by
  intro c hc
  exact h c (List.mem_flatMap.mpr ⟨g, hg, hc⟩)

/-- A group of the semantic groups is satisfied by any model of the goal-indexed formula. -/
theorem sat_baseGroup_of_sat {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {g : CNF} (hg : g ∈ baseGroups (shapeOf P B) P)
    {a : Assignment} (h : Sat a (encodeGoalsOfM P B gs m)) : Sat a g :=
  sat_group_of_sat (List.mem_append_left _ hg) h

/-- A secrecy goal in the list means the secrecy violation clause is one of the selected groups. -/
theorem violationClauses_mem {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    (hsec : Goal.secrecy ∈ gs) :
    violationClauses (shapeOf P B) P ∈ violationGroups (shapeOf P B) P gs m := by
  rw [violationGroups]
  have he : gs.elem Goal.secrecy = true := by simpa [List.elem, List.any_eq_true] using hsec
  rw [if_pos he]
  exact List.mem_append_left _ (List.Mem.head _)

/-- An agreement goal in the list means the agreement violation group is one of the selected
groups. -/
theorem authViolationClauses_mem {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    (hag : Goal.agreement ∈ gs) :
    authViolationClauses m (shapeOf P B) P ∈ violationGroups (shapeOf P B) P gs m := by
  rw [violationGroups]
  have he : gs.elem Goal.agreement = true := by simpa [List.elem, List.any_eq_true] using hag
  rw [if_pos he]
  exact List.mem_append_right _ (List.Mem.head _)

/-- The secrecy clause of a goal-indexed formula is satisfied by any of its models. -/
theorem sat_violationClauses_of_sat {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {a : Assignment} (hsec : Goal.secrecy ∈ gs) (h : Sat a (encodeGoalsOfM P B gs m)) :
    Sat a (violationClauses (shapeOf P B) P) :=
  sat_group_of_sat (List.mem_append_right _ (violationClauses_mem (m := m) hsec)) h

/-- The agreement group of a goal-indexed formula is satisfied by any of its models. -/
theorem sat_authViolationClauses_of_sat {P : Protocol} {B : Bounds} {gs : List Goal}
    {m : Matching} {a : Assignment} (hag : Goal.agreement ∈ gs)
    (h : Sat a (encodeGoalsOfM P B gs m)) :
    Sat a (authViolationClauses m (shapeOf P B) P) :=
  sat_group_of_sat (List.mem_append_right _ (authViolationClauses_mem (m := m) hag)) h

/-- **The transport that makes the old theorems reusable.** A model of any goal-indexed formula that
selects secrecy is a model of `encode P B`: the semantic groups are shared and the secrecy
violation clause is one of the selected groups. This is the single lemma through which all of
`Complete.lean` and `Sound.lean` applies to the new index without being reproved. -/
theorem sat_encode_of_sat {P : Protocol} {B : Bounds} {gs : List Goal} {a : Assignment}
    (hsec : Goal.secrecy ∈ gs) (h : Sat a (encodeGoalsOf P B gs)) : Sat a (encode P B) := by
  rw [encode_eq_base_append]
  exact sat_append.mpr ⟨sat_baseEncode_of_sat h, sat_violationClauses_of_sat hsec h⟩

/-- In the other direction, dropping the secrecy demand only removes clauses: a model of the old
formula is a model of the empty-goal formula. -/
theorem sat_encodeGoalsOf_nil_of_sat {P : Protocol} {B : Bounds} {a : Assignment}
    (h : Sat a (encode P B)) : Sat a (encodeGoalsOf P B []) := by
  rw [encodeGoalsOf_nil]
  have h2 : Sat a (baseEncode P B ++ violationClauses (shapeOf P B) P) := by
    rw [← encode_eq_base_append]
    exact h
  exact sat_append_left h2

/-- A model of the agreement encoding is a model of the semantic groups: the goal index only ever
adds clauses to `baseEncode`, and `agreementEncode` is one of the goal-indexed formulas. -/
theorem sat_baseEncode_of_sat_agreement {P : Protocol} {B : Bounds} {m : Matching}
    {a : Assignment} (h : Sat a (agreementEncode P B m)) : Sat a (baseEncode P B) := by
  have h2 : Sat a (encodeGoals P B [Goal.agreement] m) := by
    rw [encodeGoals_agreement]
    exact h
  exact sat_baseEncode_of_sat h2

/-! ### 2. The correspondence, goal-indexed, by rewriting -/

/-- **Completeness, goal-indexed.** A permitted bounded attack on the secrecy goal yields a model
of the goal-indexed formula: `Complete.encoding_complete` read through the regression gate. -/
theorem encoding_complete_goals_secrecy {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) (hsecStore : SecretsOKStore (shapeOf P B) P)
    {tr : List Ev} {Cs : List Cfg} (hbt : BoundedTrace P B tr Cs)
    (hleak : runsLeaks P Cs) (hbnd : WithinBounds P B (cfgAt Cs) (evAt tr)) :
    Satisfiable (encodeGoalsOf P B [Goal.secrecy]) := by
  rw [encodeGoalsOf_secrecy]
  exact encoding_complete (P := P) (B := B) (tr := tr) (Cs := Cs) hU hsecStore hbt.1 hbt.2.1
    hleak hbnd

/-- **Soundness, goal-indexed.** A model of the goal-indexed formula that selects secrecy is a
bounded attack on the secrecy goal: `Sound.encoding_correct_sound` through the same gate. -/
theorem encoding_sound_goals_secrecy {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) :
    Satisfiable (encodeGoalsOf P B [Goal.secrecy]) →
      boundedAttackGoals (Query.mk P B [Goal.secrecy]) := by
  rw [encodeGoalsOf_secrecy]
  exact encoding_correct_sound hU

/-- **The correspondence on the goal-indexed formula, both ways.** For a secrecy query with a
gap-free value domain and a universe the protocol stays inside, the goal-indexed CNF is satisfiable
exactly when the query has a bounded attack. The proof is `Sound.encoding_correct` with the
regression gate rewritten into it, which is the point: the new index is *compatible* with the old
correspondence rather than a second copy of it. -/
theorem encoding_correct_goals {P : Protocol} {B : Bounds}
    (hgap : domainGap P B = false) (hU : univClosed (shapeOf P B) P)
    (hsecStore : SecretsOKStore (shapeOf P B) P) :
    Satisfiable (encodeGoalsOf P B [Goal.secrecy]) ↔
      boundedAttackGoals (Query.mk P B [Goal.secrecy]) := by
  rw [encodeGoalsOf_secrecy]
  exact encoding_correct hgap hU hsecStore

/-- **Soundness for an arbitrary goal list that selects secrecy.** Adding goals only adds clauses,
and an attack on secrecy is an attack on any list that contains secrecy, so the direction holds
uniformly. This is the shape an `analyzeQuery` needs: the answer is about the goals that were
asked. -/
theorem boundedAttackGoals_of_sat_goals {P : Protocol} {B : Bounds} {gs : List Goal}
    (hsec : Goal.secrecy ∈ gs) (hU : univClosed (shapeOf P B) P) :
    Satisfiable (encodeGoalsOf P B gs) → boundedAttackGoals (Query.mk P B gs) := by
  rintro ⟨a, ha⟩
  have hs : Sat a (encode P B) := sat_encode_of_sat hsec ha
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := encoding_correct_sound hU ⟨a, hs⟩
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨Goal.secrecy, hsec, tr, Cs, hbt, (violation_secrecy P _ _).mpr hv⟩

/-- **A goal list that says nothing but secrecy is the old formula.** The secrecy goal has to be
there, and no other goal may be: then the selected violation group is exactly the old one. -/
theorem encodeGoalsOf_eq_encode_of {P : Protocol} {B : Bounds} {gs : List Goal}
    (hsec : Goal.secrecy ∈ gs) (hsub : ∀ g ∈ gs, g = Goal.secrecy) :
    encodeGoalsOf P B gs = encode P B := by
  have h1 : gs.elem Goal.secrecy = true := by simpa [List.elem, List.any_eq_true] using hsec
  have hne : Goal.agreement ∉ gs := by
    intro he
    exact absurd (hsub Goal.agreement he) (by simp)
  have h2 : gs.elem Goal.agreement = false := by
    by_contra e
    apply hne
    have he : gs.elem Goal.agreement = true := by
      cases gs.elem Goal.agreement <;> simp_all
    simpa [List.elem, List.any_eq_true] using he
  have hvg : violationGroups (shapeOf P B) P gs Matching.orderAware
      = [violationClauses (shapeOf P B) P] := by
    rw [violationGroups, h1, h2]
    rfl
  show encodeGoals P B gs Matching.orderAware = encode P B
  unfold encodeGoals encode
  rw [hvg, ← encodeGroups_eq]

/-- **Completeness for a goal list containing nothing but secrecy.** Goals the encoding cannot
represent contribute no clauses, so a secrecy-only list is exactly the old question. -/
theorem boundedAttackGoals_implies_sat_goals {P : Protocol} {B : Bounds} {gs : List Goal}
    (hsub : ∀ g ∈ gs, g = Goal.secrecy) (hU : univClosed (shapeOf P B) P)
    (hsecStore : SecretsOKStore (shapeOf P B) P) (hgap : domainGap P B = false) :
    boundedAttackGoals (Query.mk P B gs) → Satisfiable (encodeGoalsOf P B gs) := by
  rintro ⟨g, hg, tr, Cs, hbt, hv⟩
  have hgeq : g = Goal.secrecy := hsub g hg
  subst hgeq
  rw [violation_secrecy] at hv
  rw [encodeGoalsOf_eq_encode_of hg hsub]
  exact encoding_complete (P := P) (B := B) (tr := tr) (Cs := Cs) hU hsecStore
    hbt.1 hbt.2.1 hv (withinBounds_of_bounded hbt hgap)

/-! ### What the empty goal list means -/

/-- Selecting no goal asks for no violation at all, so the query has no attack for a purely logical
reason: there is nothing to violate. Restated here to mark the place where a SAT answer must NOT be
read as a security answer. -/
theorem no_attack_without_goals (P : Protocol) (B : Bounds) :
    ¬ boundedAttackGoals (Query.mk P B []) := not_boundedAttackGoals_of_nil P B

/-- **SAT of the empty-goal formula is not an attack claim.** It says a permitted run exists: the
semantic groups are exactly the clauses that describe a run of the protocol inside the bounds, and
nothing else. -/
theorem satisfiable_empty_goals {P : Protocol} {B : Bounds} :
    Satisfiable (encodeGoalsOf P B []) -> ∃ (a : Assignment), Sat a (baseEncode P B) := by
  rintro ⟨a, ha⟩
  exact ⟨a, sat_baseEncode_of_sat ha⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The AuthGap model's secrecy violation clause is the empty clause: it declares no secret, so
there is no literal left to demand. Decided by the kernel. -/
theorem empty_clause_in_encode_Authentication :
    ([] : List Lit) ∈ (encode Regressions.Authentication.P Regressions.Authentication.B).clauses := by
  decide

/-- Hence the secrecy formula for that model has no model at all. -/
theorem encode_unsat_Authentication :
    ProtSat.Unsat (encode Regressions.Authentication.P Regressions.Authentication.B) := by
  intro ⟨a, ha⟩
  have h := ha [] empty_clause_in_encode_Authentication
  rw [clause_eval_nil] at h
  exact absurd h (by simp)

/-- The empty-goal formula is satisfiable on the AuthGap model: the explicit assignment that
satisfies the agreement encoding also satisfies the semantic groups alone. -/
theorem empty_goals_sat_Authentication :
    Satisfiable (encodeGoalsOf Regressions.Authentication.P Regressions.Authentication.B []) := by
  obtain ⟨a, ha⟩ := gate_agreement_attack_found
  rw [encodeGoalsOf_nil]
  exact ⟨a, sat_baseEncode_of_sat_agreement ha⟩

/-- **The empty case cannot masquerade as a security answer, and the difference is not vacuous:**
the empty-goal formula is satisfiable on a model whose secrecy formula is unsatisfiable. The goal
index changes the question being asked, which is the point of this file. -/
theorem empty_goals_are_strictly_weaker :
    Satisfiable (encodeGoalsOf Regressions.Authentication.P Regressions.Authentication.B []) ∧
      ProtSat.Unsat (encode Regressions.Authentication.P Regressions.Authentication.B) :=
  ⟨empty_goals_sat_Authentication, encode_unsat_Authentication⟩

/-- **No transport from the semantic groups to the old formula.** The shortcut one would like - "a
model of the semantic groups is a model of `encode P B`" - is FALSE, and that is the precise reason
the agreement soundness direction cannot reuse `Encoding`'s decoding lemmas as they stand. The
witness is the AuthGap model with `AuthClauses.attackAsg`. -/
theorem no_transport_from_base :
    ∃ (P : Protocol) (B : Bounds) (a : Assignment),
      Sat a (baseEncode P B) ∧ ¬ Sat a (encode P B) := by
  obtain ⟨a, ha⟩ := gate_agreement_attack_found
  refine ⟨Regressions.Authentication.P, Regressions.Authentication.B, a,
    sat_baseEncode_of_sat_agreement ha, ?_⟩
  intro h
  exact encode_unsat_Authentication ⟨a, h⟩

/-! ### 3. The agreement case: the differential gates become goal-indexed -/

namespace Diff

open ProtSat.Reference.Contract

/-- **Differential, attacked side, goal-indexed.** On the AuthGap model the goal-indexed formula for
the agreement goal has a model and the reference enumeration finds an agreement attack: this is
`AuthClauses.Diff.diff_authentication` read through `encodeGoalsOf_agreement`. -/
theorem diff_authentication_goals :
    ProtSat.Satisfiable (encodeGoalsOf Regressions.Authentication.P
        Regressions.Authentication.B [Goal.agreement]) ∧
      attackFound (Query.mk Regressions.Authentication.P Regressions.Authentication.B
        [Goal.agreement]) = true :=
  ⟨by rw [encodeGoalsOf_agreement]; exact AuthClauses.Diff.diff_authentication.1,
    AuthClauses.Diff.diff_authentication.2⟩

/-- **Differential, attacked side, swapped-order model, goal-indexed.** -/
theorem diff_authSwapped_goals :
    ProtSat.Satisfiable (encodeGoalsOf ProtSat.Reference.Contract.Gates.authSwappedP
        ProtSat.Reference.Contract.Gates.authOrderB [Goal.agreement]) ∧
      attackFound (Query.mk ProtSat.Reference.Contract.Gates.authSwappedP
        ProtSat.Reference.Contract.Gates.authOrderB [Goal.agreement]) = true :=
  ⟨by rw [encodeGoalsOf_agreement]; exact AuthClauses.Diff.diff_authSwapped.1,
    AuthClauses.Diff.diff_authSwapped.2⟩

/-- **Differential, safe side, goal-indexed.** On the ordered model the goal-indexed formula is
unsatisfiable and the enumeration finds no attack. -/
theorem diff_authOrder_goals :
    ProtSat.Unsat (encodeGoalsOf ProtSat.Reference.Contract.Gates.authOrderP
        ProtSat.Reference.Contract.Gates.authOrderB [Goal.agreement]) ∧
      attackFound (Query.mk ProtSat.Reference.Contract.Gates.authOrderP
        ProtSat.Reference.Contract.Gates.authOrderB [Goal.agreement]) = false :=
  ⟨by rw [encodeGoalsOf_agreement]; exact AuthClauses.Diff.diff_authOrder.1,
    AuthClauses.Diff.diff_authOrder.2⟩

end Diff

/-! ### 4a. What the agreement clauses are proved to do, with no `Sat a (encode P B)` anywhere -/

/-- The demand clause of the agreement group is a clause of the goal-indexed formula. -/
theorem mem_demand_clause {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    (hag : Goal.agreement ∈ gs) :
    authViolationLits (shapeOf P B) P ∈ (encodeGoalsOfM P B gs m).clauses :=
  List.mem_flatMap.mpr ⟨authViolationClauses m (shapeOf P B) P,
    List.mem_append_right _ (authViolationClauses_mem (m := m) hag),
    List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _))⟩

/-- **The demand is satisfied.** A model of a goal-indexed formula that selects agreement makes some
commit occurrence's auxiliary variable true: the assignment names a commit candidate. No
`Sat a (encode P B)` is used, and none is needed. -/
theorem exists_commit_candidate {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {a : Assignment} (hag : Goal.agreement ∈ gs) (h : Sat a (encodeGoalsOfM P B gs m)) :
    ∃ o ∈ authOccs (shapeOf P B) P true, a (authOccVar (shapeOf P B) P o) = true := by
  have hs : Sat a (authViolationClauses m (shapeOf P B) P) :=
    sat_authViolationClauses_of_sat hag h
  have hcl : Clause.eval a (authViolationLits (shapeOf P B) P) = true :=
    hs _ (List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _)))
  rw [Clause.eval, List.any_eq_true] at hcl
  obtain ⟨l, hl, hal⟩ := hcl
  rw [authViolationLits, List.mem_map] at hl
  obtain ⟨o, ho, rfl⟩ := hl
  exact ⟨o, ho, by simpa using hal⟩

/-- **The selector implications do their job.** If a commit occurrence's selector variable is true,
all four literals that name the occurrence are true: the session acts, its program counter is the
position's, and the two annotation expressions evaluate to the recorded messages. -/
theorem authOccLits_true {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {a : Assignment} (hag : Goal.agreement ∈ gs) (h : Sat a (encodeGoalsOfM P B gs m))
    {o : AuthOcc} (ho : o ∈ authOccs (shapeOf P B) P true)
    (ha : a (authOccVar (shapeOf P B) P o) = true) :
    ∀ l ∈ authOccLits (shapeOf P B) P o, l.eval a = true := by
  have hs : Sat a (authViolationClauses m (shapeOf P B) P) :=
    sat_authViolationClauses_of_sat hag h
  have haux : Sat a (authSelectorClauses (authOccVar (shapeOf P B) P o)
      (authOccLits (shapeOf P B) P o)) := by
    intro cl hcl
    have hmem : cl ∈ authAuxClauses (shapeOf P B) P := List.mem_flatMap.mpr ⟨o, ho, hcl⟩
    exact hs cl (List.mem_append_right _ hmem)
  exact (sat_authSelectorClauses.mp haux) ha

/-- **No excusing claim is complete.** For a commit occurrence whose auxiliary variable is true,
every claim occurrence that could excuse it under the chosen monitor has at least one false
literal: the run the assignment describes does not contain that excuse. -/
theorem authNoExcuse {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {a : Assignment} (hag : Goal.agreement ∈ gs) (h : Sat a (encodeGoalsOfM P B gs m))
    {c k : AuthOcc} (hc : c ∈ authOccs (shapeOf P B) P true)
    (hk : k ∈ authOccs (shapeOf P B) P false)
    (hexc : claimExcuses m (shapeOf P B) P c k = true)
    (ha : a (authOccVar (shapeOf P B) P c) = true) :
    ∃ l ∈ authOccLits (shapeOf P B) P k, l.eval a = false := by
  have hs : Sat a (authViolationClauses m (shapeOf P B) P) :=
    sat_authViolationClauses_of_sat hag h
  have hcl : [neg (authOccVar (shapeOf P B) P c)]
      ++ (authOccLits (shapeOf P B) P k).map Lit.flip ∈ authExcuseClauses m (shapeOf P B) P := by
    rw [authExcuseClauses, List.mem_flatMap]
    exact ⟨c, hc, List.mem_filterMap.mpr ⟨k, hk, if_pos hexc⟩⟩
  have heval := hs _ (List.mem_append_left _ (List.mem_append_right _ hcl))
  rw [Clause.eval_append] at heval
  have h0 : (neg (authOccVar (shapeOf P B) P c)).eval a = false := by
    simp [neg_eval, ha]
  have h1 : Clause.eval a [neg (authOccVar (shapeOf P B) P c)] = false := by
    simp [Clause.eval, h0]
  rw [h1, Bool.false_or] at heval
  rw [Clause.eval, List.any_eq_true] at heval
  obtain ⟨l', hl', hal'⟩ := heval
  rw [List.mem_map] at hl'
  obtain ⟨l, hl, rfl⟩ := hl'
  refine ⟨l, hl, ?_⟩
  have this := hal'
  rw [Lit.flip_eval] at this
  cases h : l.eval a <;> simp_all

/-! ### 4b. The authentication bridge: what the clauses need from the decoded run -/

/-- The messages a claim or commit position records, when the position is nameable: the peer must be
a closed agent constant, the data a closed constant, and both must be messages the universe
contains. This is `AuthClauses.authOccIdx` with the two *messages* kept instead of their value
numbers, so the two are linked by `authOccIdx_map`. -/
def authOccMsgs (sh : Shape) (p : AuthPos) : Option (Agent × Term) :=
  match Expr.constVal p.peer, Expr.constVal p.val with
  | some (Term.agent a), some d =>
      if Term.agent a ∈ sh.U && d ∈ sh.U then some (a, d) else none
  | _, _ => none

/-- The value numbers `AuthClauses.authOccIdx` names, expressed through `authOccMsgs`: the two
definitions are the same match, so they agree. -/
theorem authOccIdx_map (sh : Shape) (p : AuthPos) :
    authOccIdx sh p =
      (authOccMsgs sh p).map fun (a, d) =>
        (uIdx sh (some d), uIdx sh (some (Term.agent a))) := by
  unfold authOccIdx authOccMsgs
  cases h1 : Expr.constVal p.peer with
  | none => simp
  | some t =>
      cases t with
      | agent a =>
          cases h2 : Expr.constVal p.val with
          | none => simp
          | some d =>
              by_cases hc : Term.agent a ∈ sh.U && d ∈ sh.U
              · simp [hc]
              · simp [hc]
      | nonce N => simp
      | key k => simp
      | pair x y => simp
      | encS m k => simp
      | encA m a => simp
      | hash m => simp

/-- The (tag, peer, value) triple an authentication occurrence records: what `ProtSat.AuthBreak`
compares. It is defined whenever the occurrence's position is nameable, which membership in
`AuthClauses.authOccs` guarantees by construction. -/
def authTriple (sh : Shape) (o : AuthOcc) : Option (Tag × Agent × Term) :=
  (authOccMsgs sh o.pos).map fun (a, d) => (o.pos.tag, a, d)

/-- An occurrence's own value numbers are the ones its position's messages denote. -/
theorem authOccIdx_of_mem {sh : Shape} {P : Protocol} {commit : Bool} {o : AuthOcc}
    (ho : o ∈ authOccs sh P commit) :
    authOccIdx sh o.pos = some (o.data, o.peerVal) := by
  unfold authOccs at ho
  rw [List.bind_eq_flatMap, List.mem_flatMap] at ho
  obtain ⟨p, hp, ho'⟩ := ho
  rw [List.mem_filter] at hp
  cases hidx : authOccIdx sh p with
  | none => simp [hidx] at ho'
  | some w =>
      rw [hidx] at ho'
      cases w with
      | mk u u' =>
          rw [List.mem_map] at ho'
          obtain ⟨i, hi, ho'⟩ := ho'
          have hEq : { pos := p, step := i, data := u, peerVal := u' } = o := ho'
          subst hEq
          exact hidx

/-- The messages an occurrence records, and the value numbers it carries: the two are the same fact
seen two ways. -/
theorem authOccMsgs_of_mem {sh : Shape} {P : Protocol} {commit : Bool} {o : AuthOcc}
    (ho : o ∈ authOccs sh P commit) :
    ∃ (a : Agent) (d : Term),
      authOccMsgs sh o.pos = some (a, d) ∧
        o.data = uIdx sh (some d) ∧ o.peerVal = uIdx sh (some (Term.agent a)) := by
  have hidx : authOccIdx sh o.pos = some (o.data, o.peerVal) := authOccIdx_of_mem ho
  rw [authOccIdx_map] at hidx
  cases hm : authOccMsgs sh o.pos with
  | none => rw [hm] at hidx; simp at hidx
  | some x =>
      cases x with
      | mk a d =>
          rw [hm] at hidx
          have h2 := Option.some.inj hidx
          have hfst : uIdx sh (some d) = o.data := congrArg Prod.fst h2
          have hsnd : uIdx sh (some (Term.agent a)) = o.peerVal := congrArg Prod.snd h2
          exact ⟨a, d, rfl, hfst.symm, hsnd.symm⟩

/-- A claim occurrence really is a claim and a commit occurrence really is a commit: the filter in
`authOccs` is the model's own `isCommit` flag. -/
theorem authOcc_isCommit {sh : Shape} {P : Protocol} {commit : Bool} {o : AuthOcc}
    (ho : o ∈ authOccs sh P commit) : o.pos.isCommit == commit := by
  unfold authOccs at ho
  rw [List.bind_eq_flatMap, List.mem_flatMap] at ho
  obtain ⟨p, hp, ho'⟩ := ho
  rw [List.mem_filter] at hp
  cases hidx : authOccIdx sh p with
  | none => simp [hidx] at ho'
  | some w =>
      rw [hidx] at ho'
      cases w with
      | mk u u' =>
          rw [List.mem_map] at ho'
          obtain ⟨i, hi, ho'⟩ := ho'
          have hEq : { pos := p, step := i, data := u, peerVal := u' } = o := ho'
          subst hEq
          exact hp.2

/-- **The authentication bridge, part 1 (the commit is real).** Every commit occurrence whose four
literals are true is a commit of the decoded run. -/
def CommitsReflect (P : Protocol) (B : Bounds) (a : Assignment) : Prop :=
  ∀ (o : AuthOcc), o ∈ authOccs (shapeOf P B) P true ->
    (∀ l ∈ authOccLits (shapeOf P B) P o, l.eval a = true) ->
      ∃ c ∈ commitsOf P (decCfgsFrom P B a B.steps) (decEvsFrom P B a B.steps),
        authTriple (shapeOf P B) o = some c

/-- **The authentication bridge, part 2 (every claim of the run is named).** Every claim the decoded
run makes is recorded by a claim occurrence of the model all of whose four literals are true. This
is the direction that needs `authNameable`: a claim whose annotations are not closed constants
could not be named by a fixed pair of value literals. -/
def ClaimsReflect (P : Protocol) (B : Bounds) (a : Assignment) : Prop :=
  ∀ t ∈ claimsOf P (decCfgsFrom P B a B.steps) (decEvsFrom P B a B.steps),
    ∃ k ∈ authOccs (shapeOf P B) P false,
      authTriple (shapeOf P B) k = some t ∧
        ∀ l ∈ authOccLits (shapeOf P B) P k, l.eval a = true

/-- **The decoded-run bridge.** The two things the agreement soundness needs and no lemma of
`ProtSat.Encoding` provides for a goal-indexed formula: that the decoded run is a bounded trace of
the protocol, and that the authentication literals agree with the events of the decoded run. See the
module header for why each is missing and what discharging them takes. -/
def DecodedRun (P : Protocol) (B : Bounds) (a : Assignment) : Prop :=
  BoundedTrace P B (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps)
    ∧ CommitsReflect P B a ∧ ClaimsReflect P B a

/-- Two occurrences that record the same triple have the same value numbers, so the excuse relation
of `AuthClauses` sees them as the same event. -/
theorem claimExcuses_tripleOnly_of_triples {sh : Shape} {P : Protocol}
    {c k : AuthOcc} (hc : c ∈ authOccs sh P true) (hk : k ∈ authOccs sh P false)
    {tc tk : Tag × Agent × Term} (htc : authTriple sh c = some tc)
    (htk : authTriple sh k = some tk) (h : tc = tk) :
    claimExcuses Matching.tripleOnly sh P c k = true := by
  obtain ⟨a, d, hm, hd, hp⟩ := authOccMsgs_of_mem hc
  obtain ⟨a', d', hm', hd', hp'⟩ := authOccMsgs_of_mem hk
  have hc' : authTriple sh c = some (c.pos.tag, a, d) := by
    unfold authTriple; rw [hm]; rfl
  have hk' : authTriple sh k = some (k.pos.tag, a', d') := by
    unfold authTriple; rw [hm']; rfl
  have het : tc = (c.pos.tag, a, d) := Option.some.inj (htc.symm.trans hc')
  have het' : tk = (k.pos.tag, a', d') := Option.some.inj (htk.symm.trans hk')
  have h2 : (c.pos.tag, a, d) = (k.pos.tag, a', d') := het.symm.trans (h.trans het')
  have htag : c.pos.tag = k.pos.tag := congrArg Prod.fst h2
  have ha : a = a' := congrArg (fun t => t.2.1) h2
  have hd2 : d = d' := congrArg (fun t => t.2.2) h2
  subst ha
  subst hd2
  have hc0 : k.pos.isCommit = false := by
    simpa using authOcc_isCommit hk
  rw [claimExcuses]
  simp [hc0, htag, hd, hd', hp, hp']

/-- **The excuse relation is a relation on triples.** Under `tripleOnly`, two occurrences that
record the same triple excuse each other, which is what lets the syntactic clause content and the
semantic `AuthBreak` predicate meet. -/
theorem claimExcuses_tripleOnly {sh : Shape} {P : Protocol}
    {c k : AuthOcc} (hc : c ∈ authOccs sh P true) (hk : k ∈ authOccs sh P false)
    {t : Tag × Agent × Term} (htc : authTriple sh c = some t) (htk : authTriple sh k = some t) :
    claimExcuses Matching.tripleOnly sh P c k = true :=
  claimExcuses_tripleOnly_of_triples hc hk htc htk (by rfl)

/-- **SOUND, agreement goal, modulo the decoded-run bridge.** A model of the goal-indexed formula
that selects the agreement goal, together with the decoded-run bridge, is a bounded attack on the
agreement goal of the query. Everything the *clauses* have to do is done here: the demand clause
supplies a commit candidate, the selector implications make its four literals true, the excuse
clauses make sure no claim occurrence with all its literals true excuses it, and `ClaimsReflect`
turns "the run has a claim of that triple" into "some claim occurrence has all its literals true" -
contradiction. The only assumption is `DecodedRun`, and it is no longer an assumption in substance:
`AgreesBase.decodedRun_of_sat_agreement` derives it from this same satisfaction hypothesis plus
`univClosed` and `authNameable`, and `AgreesBase.boundedAttackGoals_of_sat_agreement_discharged` is
the corollary with the bridge discharged. Note the conclusion is the UNORDERED `AuthBreak` reading of
`Goal.agreement` - see `ProtSat/AgreementPredicates.lean`. -/
theorem boundedAttackGoals_of_sat_agreement {P : Protocol} {B : Bounds} {a : Assignment}
    (h : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly))
    (hd : DecodedRun P B a) :
    boundedAttackGoals (Query.mk P B [Goal.agreement]) := by
  obtain ⟨htrace, hcomm, hclaim⟩ := hd
  obtain ⟨o, ho, hao⟩ := exists_commit_candidate (by simp) h
  have hall : ∀ l ∈ authOccLits (shapeOf P B) P o, l.eval a = true :=
    authOccLits_true (by simp) h ho hao
  obtain ⟨c, hc, hot⟩ := hcomm o ho hall
  refine ⟨Goal.agreement, by simp, decEvsFrom P B a B.steps, decCfgsFrom P B a B.steps, htrace, ?_⟩
  refine ⟨c, hc, ?_⟩
  intro hclaimed
  obtain ⟨k, hk, htk, kall⟩ := hclaim c hclaimed
  have hexc : claimExcuses Matching.tripleOnly (shapeOf P B) P o k = true :=
    claimExcuses_tripleOnly ho hk hot htk
  obtain ⟨l, hl, hf⟩ := authNoExcuse (by simp) h ho hk hexc hao
  exact absurd (kall l hl) (by cases h' : l.eval a <;> simp_all)

/-- **The existential form of the same statement.** -/
theorem boundedAttackGoals_of_satisfiable_agreement {P : Protocol} {B : Bounds}
    (h : Satisfiable (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly))
    (hd : ∀ a, Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) ->
      DecodedRun P B a) :
    boundedAttackGoals (Query.mk P B [Goal.agreement]) :=
  boundedAttackGoals_of_sat_agreement (h.choose_spec) (hd h.choose h.choose_spec)

/-- **The first half of the bridge is already a theorem - for the OLD formula.** A model of
`encode P B` decodes to a bounded trace (`Sound.boundedTrace_decRun`). This is what the module
header means by "the hypothesis has the shape the existing machinery delivers": the only thing the
goal-indexed formula lacks is the clause hypothesis `Sat a (encode P B)` itself, and
`no_transport_from_base` proves that no syntactic shortcut can supply it. -/
theorem decodedTrace_of_sat_encode {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    BoundedTrace P B (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps) :=
  boundedTrace_decRun hU h

/-- And the goal-indexed transport of it: a model of a goal-indexed formula that selects secrecy
decodes to a bounded trace, because such a model is a model of `encode P B`. -/
theorem decodedTrace_of_sat_goals {P : Protocol} {B : Bounds} {gs : List Goal} {a : Assignment}
    (hsec : Goal.secrecy ∈ gs) (hU : univClosed (shapeOf P B) P)
    (h : Sat a (encodeGoalsOf P B gs)) :
    BoundedTrace P B (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps) :=
  decodedTrace_of_sat_encode hU (sat_encode_of_sat hsec h)

/-! ### 4c. The goal-indexed correspondence, unconditional where the clauses suffice -/

/-- **Both goals selected, sound direction, no bridge needed.** A model of the formula that selects
*both* secrecy and agreement is a bounded attack on the two-goal query. This one is unconditional:
the secrecy half of the demand clause is enough to feed the existing decoding chain through
`sat_encode_of_sat`, and an attack on one selected goal is an attack on the query. It is the proof
that the goal index composes with the correspondence for a multi-goal query, and it is also the
honest limit of what the CNF route can say about agreement today: the attack it produces is a
*secrecy* attack, not an agreement one. -/
theorem boundedAttackGoals_of_sat_both {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) :
    Satisfiable (encodeGoalsOf P B [Goal.secrecy, Goal.agreement]) →
      boundedAttackGoals (Query.mk P B [Goal.secrecy, Goal.agreement]) :=
  boundedAttackGoals_of_sat_goals (hsec := List.Mem.head _) hU

/-- **Adding the agreement demand only adds clauses.** A model of the two-goal formula is a model
of the old formula: this is the direction the conjunction prototype of `AuthClauses.authEncode` got
backwards, and the goal index restores. -/
theorem sat_encode_of_sat_both {P : Protocol} {B : Bounds} {a : Assignment}
    (h : Sat a (encodeGoalsOf P B [Goal.secrecy, Goal.agreement])) : Sat a (encode P B) :=
  sat_encode_of_sat (List.Mem.head _) h

/-- Hence the two-goal formula is satisfiable only if the secrecy formula is: the agreement group
can never make a formula *easier* to satisfy, which is why selecting the violation group - not
conjoining it - was the necessary fix. -/
theorem sat_goals_secrecy_of_sat_both {P : Protocol} {B : Bounds} :
    Satisfiable (encodeGoalsOf P B [Goal.secrecy, Goal.agreement]) →
      Satisfiable (encodeGoalsOf P B [Goal.secrecy]) := by
  rintro ⟨a, ha⟩
  exact ⟨a, by rw [encodeGoalsOf_secrecy]; exact sat_encode_of_sat_both ha⟩

/-- **The agreement group is a demand, not decoration.** On the ordered model of
`ProtSat.Reference.Contract.Gates` - where every commit really is preceded by a matching claim -
the agreement-only goal-indexed formula has no model. So the clauses are constraining something:
selecting the agreement goal can make a formula unsatisfiable, which is exactly what a violation
demand must be able to do. Contrast `empty_goals_are_strictly_weaker`: with no goal selected there
is no demand and the same kind of formula is satisfiable. -/
theorem agreement_group_is_a_real_demand :
    ProtSat.Unsat (encodeGoalsOf ProtSat.Reference.Contract.Gates.authOrderP
      ProtSat.Reference.Contract.Gates.authOrderB [Goal.agreement]) :=
  (Diff.diff_authOrder_goals).1

/-- **The trace half of the bridge is realised, not hypothetical.** The leaky query of
`ProtSat.EndToEnd` has a model of `encode P B` - an assignment the solver produced and the kernel
checked (`Differential.leak_sat`) - and every model of that formula decodes to a bounded trace. So
`DecodedRun`'s first component is inhabited by a concrete witness; the two authentication
components are established in `ProtSat/AgreesBase.lean` (`commitsReflect_of_sat`,
`claimsReflect_of_sat`), and `AgreesBase.authGap_boundedAttackGoals_agreement` is the decided instance
on the AuthGap model. -/
theorem decodedTrace_is_realised :
    ∃ (a : Assignment), Sat a (encode EndToEnd.Leak EndToEnd.GB) ∧
      BoundedTrace EndToEnd.Leak EndToEnd.GB
        (decEvsFrom EndToEnd.Leak EndToEnd.GB a EndToEnd.GB.steps)
        (decCfgsFrom EndToEnd.Leak EndToEnd.GB a EndToEnd.GB.steps) := by
  obtain ⟨a, ha⟩ := Differential.leak_sat
  exact ⟨a, ha, decodedTrace_of_sat_encode Differential.leak_hU ha⟩

end ProtSat.GoalEncode
