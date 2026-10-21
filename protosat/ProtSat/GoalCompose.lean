/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.GoalAnalyze
import ProtSat.AgreesBaseComplete

/-!
# ProtSat/GoalCompose.lean - composing per-goal verdicts

## The defect this file fixes

`ProtSat/GoalEncode.lean` builds one formula per *goal list*: `violationGroups sh P gs m`
conjoins the violation group of every selected goal, so a query selecting both secrecy and agreement
asks "does one single execution violate both goals?". `ProtSat/Query.lean`'s contract asks
something else: `boundedAttackGoals q` is `∃ g ∈ q.goals, boundedAttackFor q g` -
*some* selected goal is violated by *some* permitted execution. Conjunction is therefore STRICTER
than the property, and a protocol attackable on secrecy and separately attackable on agreement,
never in the same run, would be reported safe. Section 5 exhibits such a protocol, proved.

## The fix: compose results, not clauses

`formulaOfGoal q g` is the goal-indexed formula of exactly one goal - `encodeGoalsOfM` at
the singleton list, at the monitor `Query.Violation` pairs with it (`Matching.tripleOnly`
for agreement, for the reason `GoalEncode`'s header gives). Nothing new is encoded: the
two-goal question is asked as two one-goal questions and the answers are composed at the level of
`Satisfiable` / `Unsat`.

* **Attack composition** (`boundedAttackGoals_of_exists_sat`): some selected goal's formula has
  a model, therefore the query has a bounded attack. Secrecy rides `Sound.encoding_correct_sound`;
  agreement rides `AgreesBase.boundedAttackGoals_of_satisfiable_agreement`, whose hypotheses
  (`univClosed`, `authNameable`) are exactly the two that theorem needs and no others.
* **Safety composition** (`boundedSafeGoals_of_forall_unsat`): every selected goal's formula is
  refutable, therefore the query is bounded-safe. This is the contrapositive of per-goal COMPLETENESS
  - `Complete.encoding_complete` for secrecy,
  `AgreesBaseComplete.encoding_complete_agreement` for agreement - and it is what makes an
  AGREEMENT safety verdict reachable for the first time. `GoalAnalyze` withholds it
  (`never_boundedSafe_of_agreement`) because its bridge is one formula for the whole goal list;
  per-goal formulas do not have that problem.
* **Evidence, not search** (`allGoalsRefuted`, `composedSafetyTests`,
  `composedSafeEvidence`): the UNSAT facts are taken from `Serialize.checkCode` against
  each goal's own formula, exactly as `AnalyzerEvidence` does for the secrecy formula, so no
  verdict depends on a solver run.
* **Goal-set laws** (section 4): the per-goal formulas depend on the goal list only through the two
  membership tests `violationGroups` makes, so they are invariant under permutation and
  duplication, and `Goal.agreementInj` contributes no clause at all.

## What is NOT claimed

* The composition is not a disjunctive encoding. There is no formula whose models are "a run
  violating some selected goal"; the disjunction lives in the meta-level case analysis on `g`.
* `Goal.agreementInj` is still unsupported: its `Query.Violation` is `True`, so a
  query naming it is never safe (`agreementInj_never_safe`) and the composed safety route
  refuses it.
* The agreement verdicts are for the UNORDERED `ProtSat.AuthBreak` reading of
  `Goal.agreement`; see `ProtSat/AgreementPredicates.lean` and
  `ProtSat/AgreesBase.lean`.
-/

namespace ProtSat.GoalCompose

open ProtSat Term Protocol OneHot Bounded Attacker Encode Encoding Complete Query DPLL Sound
  Represent BoundedExec Certificate Analyzer AuthClauses GoalEncode AgreesBase
  AgreesBaseComplete AgreementPredicates Serialize GoalAnalyze
open Protocol

/-! ### 1. One formula per goal -/

/-- **The formula of exactly one goal**: the ten semantic groups plus the violation group that goal
selects, at the monitor `Query.Violation` pairs with it. This is `GoalEncode.encodeGoalsOfM`
at a singleton list - not a third encoding - and `formulaOfGoal_secrecy` /
`formulaOfGoal_agreement` below are the equations that make that literal. -/
def formulaOfGoal (q : Query) (g : Goal) : CNF :=
  encodeGoalsOfM q.protocol q.bounds [g] Matching.tripleOnly

/-- The secrecy goal's own formula IS the old formula: the same term, at the singleton list. -/
theorem formulaOfGoal_secrecy (q : Query) :
    formulaOfGoal q Goal.secrecy = encode q.protocol q.bounds :=
  encodeGoals_secrecy q.protocol q.bounds Matching.tripleOnly

/-- The agreement goal's own formula is `AuthClauses.agreementEncode` at `tripleOnly`. -/
theorem formulaOfGoal_agreement (q : Query) :
    formulaOfGoal q Goal.agreement = agreementEncode q.protocol q.bounds Matching.tripleOnly :=
  encodeGoals_agreement q.protocol q.bounds Matching.tripleOnly

/-- An unsupported goal contributes no violation clause: its "own formula" is the semantic groups
alone, which demand nothing about any security property. This is why `agreementInj` cannot be
answered by a formula and must be refused. -/
theorem formulaOfGoal_agreementInj (q : Query) :
    formulaOfGoal q Goal.agreementInj = baseEncode q.protocol q.bounds := by
  show encodeGoals q.protocol q.bounds [Goal.agreementInj] Matching.tripleOnly =
      baseEncode q.protocol q.bounds
  unfold encodeGoals baseEncode
  have h1 : ([Goal.agreementInj] : List Goal).elem Goal.secrecy = false := by decide
  have h2 : ([Goal.agreementInj] : List Goal).elem Goal.agreement = false := by decide
  have hvg : violationGroups (shapeOf q.protocol q.bounds) q.protocol [Goal.agreementInj]
      Matching.tripleOnly = [] := by
    rw [violationGroups, h1, h2]
    rfl
  rw [hvg, List.append_nil]

/-- A goal the composition can decide: its violation is something the encoding represents. -/
def supportedGoal (g : Goal) : Bool := g == Goal.secrecy || g == Goal.agreement

theorem supportedGoal_secrecy : supportedGoal Goal.secrecy = true := by decide
theorem supportedGoal_agreement : supportedGoal Goal.agreement = true := by decide
theorem supportedGoal_agreementInj : supportedGoal Goal.agreementInj = false := by decide

theorem supportedGoal_iff (g : Goal) :
    supportedGoal g = true <-> g = Goal.secrecy ∨ g = Goal.agreement := by
  cases g
  · simp [supportedGoal]
  · simp [supportedGoal]
  · simp [supportedGoal]

/-! ### 2. Attack composition -/

/-- A model of the secrecy goal's own formula is a bounded attack on the secrecy goal:
`Sound.encoding_correct_sound` read through `formulaOfGoal_secrecy`. -/
theorem boundedAttackFor_of_sat_secrecy {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (h : Satisfiable (formulaOfGoal q Goal.secrecy)) : boundedAttackFor q Goal.secrecy := by
  rw [formulaOfGoal_secrecy] at h
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := encoding_correct_sound hU h
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨tr, Cs, hbt, hv⟩

/-- A model of the agreement goal's own formula is a bounded attack on the agreement goal:
`AgreesBase.boundedAttackGoals_of_satisfiable_agreement`, whose two hypotheses are exactly the
two this goal needs. The conclusion is the unordered `AuthBreak` reading. -/
theorem boundedAttackFor_of_sat_agreement {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (h : Satisfiable (formulaOfGoal q Goal.agreement)) : boundedAttackFor q Goal.agreement := by
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := boundedAttackGoals_of_satisfiable_agreement hU hN h
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨tr, Cs, hbt, hv⟩

/-- **ATTACK COMPOSITION.** If some selected goal's own formula has a model, the query has a bounded
attack: one execution violating that goal, which is what `boundedAttackGoals` asks for. The
`agreementInj` case is discharged by the contract's own degenerate reading
(`Violation = True`), not by the formula - the driver refuses that goal, and
`AgreementPredicates` says why. -/
theorem boundedAttackGoals_of_exists_sat {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (h : ∃ g ∈ q.goals, Satisfiable (formulaOfGoal q g)) : boundedAttackGoals q := by
  obtain ⟨g, hg, hs⟩ := h
  cases g with
  | secrecy => exact ⟨Goal.secrecy, hg, boundedAttackFor_of_sat_secrecy hU hs⟩
  | agreement => exact ⟨Goal.agreement, hg, boundedAttackFor_of_sat_agreement hU hN hs⟩
  | agreementInj => exact boundedAttackGoals_of_agreementInj hg

/-- The supported-goal form of the same statement: nothing rests on the degenerate goal. -/
theorem boundedAttackGoals_of_exists_sat_supported {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (h : ∃ g ∈ q.goals, supportedGoal g = true ∧ Satisfiable (formulaOfGoal q g)) :
    boundedAttackGoals q := by
  obtain ⟨g, hg, hsup, hs⟩ := h
  rw [supportedGoal_iff] at hsup
  cases hsup with
  | inl h => subst h; exact ⟨Goal.secrecy, hg, boundedAttackFor_of_sat_secrecy hU hs⟩
  | inr h => subst h; exact ⟨Goal.agreement, hg, boundedAttackFor_of_sat_agreement hU hN hs⟩

/-- Read backwards: a query with no bounded attack has every selected goal's formula refutable -
the contrapositive of the composition above, stated so the direction is visible. -/
theorem unsat_of_boundedSafeGoals {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (hne : boundedSafeGoals q) (g : Goal) (hg : g ∈ q.goals) :
    ProtSat.Unsat (formulaOfGoal q g) := by
  intro hsat
  exact hne (boundedAttackGoals_of_exists_sat hU hN ⟨g, hg, hsat⟩)

/-! ### 3. Safety composition -/

/-- **The semantic groups have a model whenever the protocol has a run.** The ten groups say what a
run looks like and demand nothing about any security property, so any bounded trace - the empty one
included - turns them into a satisfiable formula. This is what makes the `agreementInj` case of
the safety composition close: an unsupported goal's own formula is never refutable. -/
theorem satisfiable_baseEncode_of {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hgap : domainGap P B = false) :
    Satisfiable (AuthClauses.baseEncode P B) := by
  have hbnd := withinBounds_of_bounded hbt hgap
  have hrel := (runs_rel hbt.1).2
  have hcfg0 : cfgAt Cs 0 = initCfg P := ((runs_rel hbt.1).1).symm
  refine ⟨assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr), sat_baseEncode_of_groups
      (sat_oneHot (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd (univSub_shapeOf P B) hrel)
      (sat_init (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hcfg0)
      (sat_frame (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel)
      (sat_eval (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd)
      (sat_step (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel)
      (sat_ded (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd (univSub_shapeOf P B) hrel)
      (sat_pubAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd)
      (sat_knSupport (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) U_nodup hrel)
      (sat_fresh (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (fun N hN => nonces_subset_univ P B N hN) hrel)
      (sat_leakAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd)⟩

/-- **The semantic groups are satisfiable at any bounds at all**, by the empty run. -/
theorem satisfiable_baseEncode {P : Protocol} {B : Bounds} (hgap : domainGap P B = false) :
    Satisfiable (AuthClauses.baseEncode P B) :=
  satisfiable_baseEncode_of (empty_boundedTrace P B) hgap

/-- **SAFETY COMPOSITION - the exact statement as it landed.**

`∃ g ∈ q.goals, Satisfiable (formulaOfGoal q g)` is the contract's attack read goal by
goal; this theorem is its contrapositive, per goal: if EVERY selected goal's OWN formula is
refutable then no selected goal is violated by any permitted execution, i.e. `boundedSafeGoals
q`. Each goal is discharged under the hypotheses its own completeness theorem needs and no
others: secrecy through `Complete.encoding_complete` (`univClosed`,
`SecretsOKStore`, `domainGap = false`), agreement through
`AgreesBaseComplete.encoding_complete_agreement` (`authNameable`, `domainGap = false`)
at `Matching.tripleOnly`, the monitor `Query.Violation` pairs with `Goal.agreement`.
An `agreementInj` in the list makes the hypothesis unmeetable rather than the conclusion
vacuous: that goal's own formula is the semantic groups, which are satisfiable. -/
theorem boundedSafeGoals_of_forall_unsat {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    (h : ∀ g ∈ q.goals, ProtSat.Unsat (formulaOfGoal q g)) : boundedSafeGoals q := by
  intro hatk
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := hatk
  have hsat : Satisfiable (formulaOfGoal q g) := by
    cases g with
    | secrecy =>
        rw [violation_secrecy] at hv
        rw [formulaOfGoal_secrecy]
        exact encoding_complete hU hsecStore hbt.1 hbt.2.1 hv (withinBounds_of_bounded hbt hgap)
    | agreement =>
        rw [violation_agreement] at hv
        exact encoding_complete_agreement hN hgap hbt hv
    | agreementInj =>
        rw [formulaOfGoal_agreementInj]
        exact satisfiable_baseEncode hgap
  exact h g hg hsat

/-- The per-goal completeness facts as one implication each - the two halves of the theorem above
named separately, so a reader can see which hypothesis belongs to which goal. -/
theorem satisfiable_of_boundedAttackFor_secrecy {q : Query}
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) :
    boundedAttackFor q Goal.secrecy → Satisfiable (formulaOfGoal q Goal.secrecy) := by
  rintro ⟨tr, Cs, hbt, hv⟩
  rw [violation_secrecy] at hv
  rw [formulaOfGoal_secrecy]
  exact encoding_complete hU hsecStore hbt.1 hbt.2.1 hv (withinBounds_of_bounded hbt hgap)

theorem satisfiable_of_boundedAttackFor_agreement {q : Query}
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) :
    boundedAttackFor q Goal.agreement → Satisfiable (formulaOfGoal q Goal.agreement) := by
  rintro ⟨tr, Cs, hbt, hv⟩
  rw [violation_agreement] at hv
  exact encoding_complete_agreement hN hgap hbt hv

/-! #### 3b. The same composition driven by CHECKED evidence -/

/-- **Per-goal refutation evidence**: a function naming, for each selected goal, a serialized
refutation of THAT goal's own formula. Decidable, and the only thing the verdict below trusts:
`Serialize.checkCode` walks a resolution proof, it runs no search. -/
def allGoalsRefuted (q : Query) (ev : Goal → Option (Nat × List Int)) : Bool :=
  q.goals.all fun g => match ev g with
    | some kc => checkCode (formulaOfGoal q g) kc.1 kc.2
    | none => false

/-- Checked evidence is evidence, goal by goal. -/
theorem unsat_of_allGoalsRefuted {q : Query} {ev : Goal → Option (Nat × List Int)}
    (h : allGoalsRefuted q ev = true) {g : Goal} (hg : g ∈ q.goals) :
    ProtSat.Unsat (formulaOfGoal q g) := by
  rw [allGoalsRefuted, List.all_eq_true] at h
  have h2 := h g hg
  cases he : ev g with
  | none => simp [he] at h2
  | some kc =>
      rw [he] at h2
      cases kc with
      | mk k c => exact checkCode_sound h2

/-- **Safety from checked evidence, composed per goal.** No solver appears in the chain: the only
trusted component is the line-by-line resolution checker, run against each goal's own formula. -/
theorem boundedSafeGoals_of_allGoalsRefuted {q : Query} (ev : Goal → Option (Nat × List Int))
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    (h : allGoalsRefuted q ev = true) : boundedSafeGoals q :=
  boundedSafeGoals_of_forall_unsat hU hN hsecStore hgap
    (fun _g hg => unsat_of_allGoalsRefuted h hg)

/-- The decidable side conditions of the composed safety verdict, as one Boolean: the shape tests
`GoalAnalyze` already runs, the store-secret test, the gap test, and the per-goal evidence. -/
def composedSafetyTests (q : Query) (ev : Goal → Option (Nat × List Int)) : Bool :=
  univClosedBool (shapeOf q.protocol q.bounds) q.protocol
    && authNameableBool (shapeOf q.protocol q.bounds) q.protocol
    && secretsOKStoreBool (shapeOf q.protocol q.bounds) q.protocol
    && ! domainGap q.protocol q.bounds
    && allGoalsRefuted q ev

/-- **The composed safety verdict, from a Boolean test the caller can run.** -/
theorem boundedSafeGoals_of_composedSafetyTests {q : Query}
    (ev : Goal → Option (Nat × List Int))
    (h : composedSafetyTests q ev = true) : boundedSafeGoals q := by
  simp only [composedSafetyTests, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact boundedSafeGoals_of_allGoalsRefuted ev
    ((univClosedBool_iff _ _).mp h.1.1.1.1)
    ((authNameableBool_iff _ _).mp h.1.1.1.2)
    ((secretsOKStoreBool_iff _ _).mp h.1.1.2)
    h.1.2 h.2

/-- The evidence record: a `SafeEvidence` whose query is the query it was asked about. -/
def composedSafeEvidence (q : Query) (ev : Goal → Option (Nat × List Int)) :
    Option SafeEvidence :=
  if h : composedSafetyTests q ev = true then
    some (SafeEvidence.mk q (boundedSafeGoals_of_composedSafetyTests ev h))
  else none

/-- The verdict, when it is `boundedSafe`, is true. -/
theorem boundedSafeGoals_of_composedSafeEvidence {q : Query}
    {ev : Goal → Option (Nat × List Int)} {e : SafeEvidence}
    (h : composedSafeEvidence q ev = some e) : boundedSafeGoals q := by
  by_cases hs : composedSafetyTests q ev = true
  · have : composedSafeEvidence q ev =
        some (SafeEvidence.mk q (boundedSafeGoals_of_composedSafetyTests ev hs)) :=
      dite_eq_left hs
    rw [this] at h
    cases h
    exact boundedSafeGoals_of_composedSafetyTests ev hs
  · rw [composedSafeEvidence, dite_eq_right hs] at h
    cases h

/-- The composed safe-side verdict: evidence if the per-goal bridge accepts, otherwise the formula
fact and nothing more. -/
def composedSafeVerdict (q : Query) (ev : Goal → Option (Nat × List Int)) : Result :=
  match composedSafeEvidence q ev with
  | some e => Result.boundedSafe e
  | none => Result.encodingUnsat

/-- `Result.boundedSafe` out of the composed verdict always means `boundedSafeGoals q`. -/
theorem boundedSafeGoals_of_composedSafeVerdict {q : Query}
    {ev : Goal → Option (Nat × List Int)} {e : SafeEvidence}
    (h : composedSafeVerdict q ev = Result.boundedSafe e) : boundedSafeGoals q :=
  boundedSafeGoals_of_composedSafeEvidence (by
    unfold composedSafeVerdict at h
    cases h2 : composedSafeEvidence q ev with
    | some e' => rw [h2] at h; cases h; rfl
    | none => rw [h2] at h; cases h)

/-- **An unsupported goal cannot be refuted, so it cannot be silently absorbed into a safety
verdict.** A query selecting `Goal.agreementInj` never passes the evidence test: that goal's
own formula is the semantic groups, and the semantic groups have a model. -/
theorem not_allGoalsRefuted_of_agreementInj {q : Query} (ev : Goal → Option (Nat × List Int))
    (hg : Goal.agreementInj ∈ q.goals) (hgap : domainGap q.protocol q.bounds = false) :
    allGoalsRefuted q ev = false := by
  cases h : allGoalsRefuted q ev with
  | true =>
      have h2 := unsat_of_allGoalsRefuted h hg
      rw [formulaOfGoal_agreementInj] at h2
      exact absurd (satisfiable_baseEncode hgap) h2
  | false => rfl

/-- And the contract side of the same fact: a query naming `agreementInj` is attacked whatever
the protocol and the bounds, so no composition may call it safe. -/
theorem agreementInj_never_safe {q : Query} (hg : Goal.agreementInj ∈ q.goals) :
    ¬ boundedSafeGoals q := not_boundedSafeGoals_of_agreementInj hg

/-! ### 4. Goal-set laws -/

/-- Turning a Prop-level equality of memberships into the Boolean equality `violationGroups`
actually reads. -/
theorem elem_eq_of_mem_eq {alpha : Type} [DecidableEq alpha] {l l' : List alpha} {a : alpha}
    (h : (a ∈ l) = (a ∈ l')) : l.elem a = l'.elem a := by
  have e1 : (l.elem a = true) = (a ∈ l) := mem_iff_elem a l
  have e2 : (l'.elem a = true) = (a ∈ l') := mem_iff_elem a l'
  have h3 : (l.elem a = true) = (l'.elem a = true) := by rw [e1, h, ← e2]
  cases h1 : l.elem a <;> cases h2 : l'.elem a <;> simp_all

/-- The violation groups depend on the goal list through exactly two membership tests. -/
theorem violationGroups_eq_of_elem {sh : Shape} {P : Protocol} {gs gs' : List Goal} {m : Matching}
    (h1 : gs.elem Goal.secrecy = gs'.elem Goal.secrecy)
    (h2 : gs.elem Goal.agreement = gs'.elem Goal.agreement) :
    violationGroups sh P gs m = violationGroups sh P gs' m := by
  unfold violationGroups
  rw [h1, h2]

/-- Hence the goal-indexed formula depends on the goal list only through those two tests. -/
theorem encodeGoalsOfM_eq_of_elem {P : Protocol} {B : Bounds} {gs gs' : List Goal} {m : Matching}
    (h1 : gs.elem Goal.secrecy = gs'.elem Goal.secrecy)
    (h2 : gs.elem Goal.agreement = gs'.elem Goal.agreement) :
    encodeGoalsOfM P B gs m = encodeGoalsOfM P B gs' m := by
  unfold encodeGoalsOfM encodeGoals
  rw [violationGroups_eq_of_elem h1 h2]

/-- **PERMUTATION INVARIANCE.** Reordering the selected goals changes no clause of any formula, the
per-goal ones or the conjoined one. -/
theorem encodeGoalsOfM_perm {P : Protocol} {B : Bounds} {gs gs' : List Goal} {m : Matching}
    (h : List.Perm gs gs') : encodeGoalsOfM P B gs m = encodeGoalsOfM P B gs' m :=
  encodeGoalsOfM_eq_of_elem
    (elem_eq_of_mem_eq (propext (h.mem_iff (a := Goal.secrecy))))
    (elem_eq_of_mem_eq (propext (h.mem_iff (a := Goal.agreement))))

/-- A duplicate head changes no membership test, so it changes no formula. -/
theorem elem_cons_dup {alpha : Type} [DecidableEq alpha] {gs : List alpha} {a g : alpha}
    (hg : g ∈ gs) : (g :: gs).elem a = gs.elem a := by
  have h : (a ∈ (g :: gs)) = (a ∈ gs) := by
    apply propext
    constructor
    · intro hm
      cases List.mem_cons.mp hm with
      | inl he => subst he; exact hg
      | inr hm => exact hm
    · intro hm
      exact List.mem_cons.mpr (Or.inr hm)
  exact elem_eq_of_mem_eq h

/-- **DUPLICATION INVARIANCE.** Selecting a goal that is already selected adds no clause: the
formula depends on the goal SET the query selected, not on the list that named it. -/
theorem encodeGoalsOfM_cons_dup {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    (g : Goal) (hg : g ∈ gs) :
    encodeGoalsOfM P B (g :: gs) m = encodeGoalsOfM P B gs m :=
  encodeGoalsOfM_eq_of_elem (elem_cons_dup hg) (elem_cons_dup hg)

/-- **DUPLICATION, appended form.** -/
theorem encodeGoalsOfM_append_self {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching} :
    encodeGoalsOfM P B (gs ++ gs) m = encodeGoalsOfM P B gs m := by
  refine encodeGoalsOfM_eq_of_elem ?_ ?_
  · exact elem_eq_of_mem_eq (propext
      ⟨fun hm => (List.mem_append.mp hm).elim (fun h => h) (fun h => h), fun hm => List.mem_append.mpr (Or.inl hm)⟩)
  · exact elem_eq_of_mem_eq (propext
      ⟨fun hm => (List.mem_append.mp hm).elim (fun h => h) (fun h => h), fun hm => List.mem_append.mpr (Or.inl hm)⟩)

/-- **An unsupported goal adds no clause.** Naming `Goal.agreementInj` alongside other goals
changes the formula not at all - which is why the driver must refuse it rather than let it ride along
inside a conjunction that cannot see it. -/
theorem encodeGoalsOfM_agreementInj_cons {P : Protocol} {B : Bounds} {gs : List Goal}
    {m : Matching} :
    encodeGoalsOfM P B (Goal.agreementInj :: gs) m = encodeGoalsOfM P B gs m := by
  refine encodeGoalsOfM_eq_of_elem ?_ ?_
  · show (Goal.agreementInj :: gs).elem Goal.secrecy = gs.elem Goal.secrecy
    rw [List.elem_cons]
    have h : (Goal.secrecy == Goal.agreementInj) = false := by decide
    rw [h]
  · show (Goal.agreementInj :: gs).elem Goal.agreement = gs.elem Goal.agreement
    rw [List.elem_cons]
    have h : (Goal.agreement == Goal.agreementInj) = false := by decide
    rw [h]

/-- The same laws at the level of the driver's whole-list formula. -/
theorem formulaOfGoals_perm {P : Protocol} {B : Bounds} {gs gs' : List Goal}
    (h : List.Perm gs gs') :
    formulaOfGoals (Query.mk P B gs) = formulaOfGoals (Query.mk P B gs') :=
  encodeGoalsOfM_perm h

theorem formulaOfGoals_append_self {P : Protocol} {B : Bounds} {gs : List Goal} :
    formulaOfGoals (Query.mk P B (gs ++ gs)) = formulaOfGoals (Query.mk P B gs) :=
  encodeGoalsOfM_append_self

theorem formulaOfGoals_agreementInj_cons {P : Protocol} {B : Bounds} {gs : List Goal} :
    formulaOfGoals (Query.mk P B (Goal.agreementInj :: gs)) = formulaOfGoals (Query.mk P B gs) :=
  encodeGoalsOfM_agreementInj_cons

/-- Per-goal formulas are permutation- and duplication-insensitive too: each one is built from a
singleton list, so the only thing that can change it is the goal itself. -/
theorem formulaOfGoal_eq_of_mem_iff {q : Query} {g g' : Goal}
    (h : (g = Goal.secrecy) = (g' = Goal.secrecy) ∧ (g = Goal.agreement) = (g' = Goal.agreement)) :
    formulaOfGoal q g = formulaOfGoal q g' := by
  refine encodeGoalsOfM_eq_of_elem ?_ ?_
  · show ([g] : List Goal).elem Goal.secrecy = ([g'] : List Goal).elem Goal.secrecy
    cases g <;> cases g' <;> simp_all
  · show ([g] : List Goal).elem Goal.agreement = ([g'] : List Goal).elem Goal.agreement
    cases g <;> cases g' <;> simp_all



/-- A one-event run visits exactly its start and its end. -/
theorem runs_single {P : Protocol} {C : Cfg} {e : Ev} {Cs : List Cfg}
    (h : Runs P C [e] Cs) : ∃ C2, Cs = C :: [C2] ∧ Rel P C e C2 := by
  cases h with
  | cons hrel hrest =>
      cases hrest with
      | nil => exact ⟨_, rfl, hrel⟩

/-! ### 5. The counterexample: each goal attackable, no run violating both -/

/-- **The mixed-gap model.** Two sessions, one event of room. Session 0 publishes the declared
secret; session 1 commits a triple no session ever claims. With `steps := 1` a permitted
execution performs ONE event, so the leak and the agreement break are each reachable and never
together. This is the protocol the conjoined encoding cannot answer: `boundedAttackGoals` holds
through both goals, and `encodeGoalsOfM mixP mixB [secrecy, agreement]` has no model. -/
def mixP : Protocol :=
  { roles := [ { acts := [Action.send 0 (Expr.shrk 0 0)] },
               { acts := [Action.commit 0 (Expr.agent 0) (Expr.agent 0)] } ]
    sessions := [ { role := 0, self := 0, peer := 0 }, { role := 1, self := 0, peer := 0 } ]
    agents := [0], nonceDomain := [], compromised := [],
    secrets := [Secret.closed (Expr.shrk 0 0)], auths := [{ tag := 0 }] }

/-- One event: enough room for either violation, never for both. -/
def mixB : Bounds := { steps := 1, rounds := 0 }

/-- The query that selects both goals - the shape the conjoined encoding gets wrong. -/
def mixQ : Query := Query.mk mixP mixB [Goal.secrecy, Goal.agreement]

/-- The run that leaks: session 0 publishes the declared shared key. -/
def leakTr : List Ev := [Ev.act 0 (Term.agent 0) 0]

/-- The run that breaks agreement: session 1 commits the unclaimed triple. -/
def breakTr : List Ev := [Ev.act 1 (Term.agent 0) 0]

def leakCert : Certificate := Examples.certOfTrace mixP leakTr
def breakCert : Certificate := Examples.certOfTrace mixP breakTr

theorem mix_wf : WellFormed mixQ := by
  show validate mixQ = []
  decide

theorem mix_hU : univClosed (shapeOf mixP mixB) mixP := by
  unfold univClosed
  decide

theorem mix_hN : authNameable (shapeOf mixP mixB) mixP := by
  unfold authNameable
  decide

theorem mix_gap : domainGap mixP mixB = false := by decide

theorem mix_hsecStore : SecretsOKStore (shapeOf mixP mixB) mixP := by
  intro q x h
  have heq : Secret.store q x = Secret.closed (Expr.shrk 0 0) := List.mem_singleton.mp h
  cases heq

theorem leakCert_checked : checkCertificate mixP leakCert = true := by decide
theorem breakCert_checked : checkCertificate mixP breakCert = true := by decide

theorem leak_run : BoundedTrace mixP mixB (certTrace leakCert) (certCfgs leakCert) :=
  ⟨checkSteps_runs mixP leakCert.steps (initCfg mixP) (by decide),
    by decide,
    by
      change ∀ C ∈ certCfgs leakCert, cfgInUniverse C (univ mixP mixB) = true
      decide⟩

theorem break_run : BoundedTrace mixP mixB (certTrace breakCert) (certCfgs breakCert) :=
  ⟨checkSteps_runs mixP breakCert.steps (initCfg mixP) (by decide),
    by decide,
    by
      change ∀ C ∈ certCfgs breakCert, cfgInUniverse C (univ mixP mixB) = true
      decide⟩

/-- The leak run leaks, and does not break agreement. -/
theorem leak_run_leaks : runsLeaks mixP (certCfgs leakCert) := by
  rw [← runsLeaksBool_iff]
  decide

theorem leak_run_agrees : ¬ AuthBreak mixP (certCfgs leakCert) (certTrace leakCert) := by
  rw [← authBreakBool_iff]
  decide

/-- The agreement run breaks agreement, and does not leak. -/
theorem break_run_breaks : AuthBreak mixP (certCfgs breakCert) (certTrace breakCert) := by
  rw [← authBreakBool_iff]
  decide

theorem break_run_no_leak : ¬ runsLeaks mixP (certCfgs breakCert) := by
  rw [← runsLeaksBool_iff]
  decide

/-- **Each goal is separately attackable.** Two attacks on the SAME query, through different goals
and different executions. -/
theorem mix_attack_secrecy : boundedAttackFor mixQ Goal.secrecy :=
  ⟨certTrace leakCert, certCfgs leakCert, leak_run, by
    rw [violation_secrecy]; exact leak_run_leaks⟩

theorem mix_attack_agreement : boundedAttackFor mixQ Goal.agreement :=
  ⟨certTrace breakCert, certCfgs breakCert, break_run, by
    rw [violation_agreement]; exact break_run_breaks⟩


/-- The two actions of the model, at the program counters the initial configuration puts them at. -/
theorem mix_actionAt_send :
    mixP.actionAt 0 (pcOf (initCfg mixP) 0) = some (Action.send 0 (Expr.shrk 0 0)) := rfl

theorem mix_actionAt_commit :
    mixP.actionAt 1 (pcOf (initCfg mixP) 1) =
      some (Action.commit 0 (Expr.agent 0) (Expr.agent 0)) := rfl

/-- There is no third session: out of range, a session has no action at all. -/
theorem mix_actionAt_none {q pc : Nat} (hq : 2 ≤ q) : mixP.actionAt q pc = none := by
  have h1 : mixP.sessions.length = 2 := rfl
  have h2 : mixP.sessions.drop q = [] := List.drop_eq_nil_of_le (by omega)
  unfold Protocol.actionAt Protocol.roleAt
  rw [h2]
  simp [List.head?]

/-- What each single event records as an authentication instance: the send records nothing, the
commit records the unclaimed triple, and nothing else can happen. -/
theorem authOfStep_mix_send (m : Term) (d : NonceName) :
    authOfStep mixP (initCfg mixP) (Ev.act 0 m d) = [] := by
  unfold authOfStep
  dsimp only
  rw [mix_actionAt_send]

theorem authOfStep_mix_commit (m : Term) (d : NonceName) :
    authOfStep mixP (initCfg mixP) (Ev.act 1 m d) =
      [{ isCommit := true, tag := 0, peer := 0, val := Term.agent 0 }] := by
  unfold authOfStep
  dsimp only
  rw [mix_actionAt_commit]
  rfl

theorem authOfStep_mix_none {q : Nat} (hq : 2 ≤ q) (m : Term) (d : NonceName) :
    authOfStep mixP (initCfg mixP) (Ev.act q m d) = [] := by
  unfold authOfStep
  dsimp only
  rw [mix_actionAt_none hq]

/-- One event, two configurations: the authentication instances of a one-event run are exactly the
instances of that event in the initial configuration. -/
theorem authInsts_mix_one (e : Ev) (C1 : Cfg) :
    authInsts mixP [initCfg mixP, C1] [e] = authOfStep mixP (initCfg mixP) e := by
  simp [authInsts]

theorem commitsOf_mix_one (e : Ev) (C1 : Cfg) :
    commitsOf mixP [initCfg mixP, C1] [e] =
      (authOfStep mixP (initCfg mixP) e).filterMap fun a =>
        if a.isCommit then some (a.tag, a.peer, a.val) else none := by
  simp [commitsOf, authInsts_mix_one]

/-- **The only breaking event is session 1's commit.** Session 0's event is a send, which records no
commit; a deduction or an idle step records none either; and there is no third session. -/
theorem break_event : ∀ (e : Ev) (C1 : Cfg),
    AuthBreak mixP [initCfg mixP, C1] [e] →
      ∃ (m : Term) (d : NonceName), e = Ev.act 1 m d := by
  intro e C1 hbreak
  obtain ⟨c, hc, _hnc⟩ := hbreak
  rw [commitsOf_mix_one] at hc
  cases e with
  | idle => simp [authOfStep] at hc
  | ded t => simp [authOfStep] at hc
  | act q m d =>
      cases q with
      | zero => rw [authOfStep_mix_send] at hc; simp at hc
      | succ q1 =>
          cases q1 with
          | zero => exact ⟨m, d, rfl⟩
          | succ q2 => rw [authOfStep_mix_none (by omega)] at hc; simp at hc

/-- A commit step advances session 1 and publishes nothing, so the configuration it reaches holds
exactly the initial knowledge - and the initial knowledge does not contain the secret. -/
theorem mix_rel_commit : ∀ (m : Term) (d : NonceName) (C1 : Cfg),
    Rel mixP (initCfg mixP) (Ev.act 1 m d) C1 →
      C1 = succAdvance (initCfg mixP) 1 := by
  intro m d C1 hrel
  cases hrel with
  | rCommit => rfl
  | rSend => simp_all [mix_actionAt_commit]
  | rRecv => simp_all [mix_actionAt_commit]
  | rFresh => simp_all [mix_actionAt_commit]
  | rAssign => simp_all [mix_actionAt_commit]
  | rCheck => simp_all [mix_actionAt_commit]
  | rSecret => simp_all [mix_actionAt_commit]
  | rClaim => simp_all [mix_actionAt_commit]

/-- The configuration a commit reaches still leaks nothing. -/
theorem mix_commit_no_leak :
    ¬ runsLeaks mixP [initCfg mixP, succAdvance (initCfg mixP) 1] := by
  rw [← runsLeaksBool_iff]
  decide

/-- A send step records no commit, so the leaking run does not break agreement. -/
theorem mix_send_no_break : ¬ AuthBreak mixP
    [initCfg mixP, succSend (initCfg mixP) 0 (Term.key (Key.shrk 0 0))]
    [Ev.act 0 (Term.agent 0) 0] := by
  rw [← authBreakBool_iff]
  decide

/-- **No single execution violates both goals.** The content of the counterexample, and the only
part of it that is a proof about the semantics rather than about a formula: a run of `mixP`
within `mixB` has at most one event; an agreement break needs session 1's commit, and the
configuration a commit reaches still holds only what it started with, so a breaking run cannot
leak. No solver appears anywhere in this proof. -/
theorem no_run_does_both :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg),
      BoundedTrace mixP mixB tr Cs ∧ runsLeaks mixP Cs ∧ AuthBreak mixP Cs tr := by
  rintro ⟨tr, Cs, ⟨hruns, hlen, _hu⟩, hleak, hbreak⟩
  have hsteps : mixB.steps = 1 := rfl
  cases tr with
  | nil =>
      have hCs : Cs = [initCfg mixP] := by cases hruns with | nil => rfl
      rw [hCs] at hleak
      exact absurd hleak (by rw [← runsLeaksBool_iff]; decide)
  | cons e rest =>
      have hrest : rest.length = 0 := by
        rw [List.length_cons] at hlen
        omega
      have hrest2 : rest = [] := List.eq_nil_of_length_eq_zero hrest
      subst hrest2
      obtain ⟨C1, hCs, hrel⟩ := runs_single hruns
      subst hCs
      obtain ⟨m, d, he⟩ := break_event e C1 hbreak
      subst he
      have hC1 : C1 = succAdvance (initCfg mixP) 1 := mix_rel_commit m d C1 hrel
      rw [hC1] at hleak
      exact absurd hleak mix_commit_no_leak

/-- **The conjoined formula is refutable while the query is attacked.** The soundness direction of
each goal, applied to the SAME assignment, turns a model of the conjunction into a single execution
that both leaks and breaks agreement - and the lemma above says no such execution exists. -/
theorem mix_conjunction_unsat :
    ProtSat.Unsat (encodeGoalsOfM mixP mixB [Goal.secrecy, Goal.agreement] Matching.tripleOnly) := by
  rintro ⟨a, ha⟩
  have hsec : Sat a (Encode.encode mixP mixB) :=
    GoalAnalyze.sat_encode_of_satM (hsec := List.Mem.head _) ha
  have hleak : runsLeaks mixP (decCfgsFrom mixP mixB a mixB.steps) :=
    decCfgsFrom_runsLeaks mix_hU hsec
  have hbt : BoundedTrace mixP mixB (decEvsFrom mixP mixB a mixB.steps)
      (decCfgsFrom mixP mixB a mixB.steps) :=
    boundedTrace_decRun mix_hU hsec
  have hagr : Sat a (encodeGoalsOfM mixP mixB [Goal.agreement] Matching.tripleOnly) := by
    have hb : Sat a (baseEncode mixP mixB) := GoalEncode.sat_baseEncode_of_sat ha
    have hav : Sat a (authViolationClauses Matching.tripleOnly (shapeOf mixP mixB) mixP) :=
      GoalEncode.sat_authViolationClauses_of_sat (by simp) ha
    rw [encodeGoalsOfM_agreement, agreementEncode]
    exact sat_append.mpr ⟨hb, hav⟩
  have hbreak : AuthBreak mixP (decCfgsFrom mixP mixB a mixB.steps)
      (decEvsFrom mixP mixB a mixB.steps) :=
    GoalAnalyze.authBreak_of_sat_agreement mix_hU mix_hN hagr
  exact no_run_does_both ⟨decEvsFrom mixP mixB a mixB.steps, decCfgsFrom mixP mixB a mixB.steps,
    hbt, hleak, hbreak⟩

/-- Each goal's OWN formula, by contrast, has a model - obtained from the run that violates it,
through that goal's completeness theorem. -/
theorem mix_sat_secrecy : Satisfiable (formulaOfGoal mixQ Goal.secrecy) :=
  satisfiable_of_boundedAttackFor_secrecy mix_hU mix_hsecStore mix_gap mix_attack_secrecy

theorem mix_sat_agreement : Satisfiable (formulaOfGoal mixQ Goal.agreement) :=
  satisfiable_of_boundedAttackFor_agreement mix_hN mix_gap mix_attack_agreement

/-- **THE DEFECT, AS A PROVED FACT.** The contract says attacked; the conjoined formula says
refutable. A driver that read a refutation of the conjunction as safety would report SAFE on this
query, and it would be wrong. -/
theorem mixed_goal_conjunction_is_stricter :
    boundedAttackGoals mixQ ∧ ProtSat.Unsat (GoalAnalyze.formulaOfGoals mixQ) :=
  ⟨boundedAttackGoals_of_exists_sat mix_hU mix_hN
      ⟨Goal.secrecy, List.Mem.head _, mix_sat_secrecy⟩, mix_conjunction_unsat⟩

/-- The query is not safe, and the composed route is what says so. -/
theorem mix_not_safe : ¬ boundedSafeGoals mixQ :=
  fun h => h (boundedAttackGoals_of_exists_sat mix_hU mix_hN
    ⟨Goal.agreement, by simp [mixQ], mix_sat_agreement⟩)

/-- The composed per-goal route finds the attack the conjunction hides: some selected goal's own
formula has a model, so the verdict is ATTACK - and it can be read out of either goal. -/
theorem mix_composed_attack : boundedAttackGoals mixQ :=
  boundedAttackGoals_of_exists_sat mix_hU mix_hN ⟨Goal.agreement, by simp [mixQ], mix_sat_agreement⟩

theorem mix_composed_attack_secrecy : boundedAttackGoals mixQ :=
  boundedAttackGoals_of_exists_sat mix_hU mix_hN ⟨Goal.secrecy, List.Mem.head _, mix_sat_secrecy⟩

/-- **The invalid rule, refuted.** "The formula of the query has no model, therefore the query is
safe" is false, and `mixQ` is the witness: its conjoined formula is refutable while its
contract is attacked. -/
theorem conjunction_refutation_is_not_safety :
    ¬ (∀ q : Query, ProtSat.Unsat (GoalAnalyze.formulaOfGoals q) → boundedSafeGoals q) := by
  intro hall
  exact mix_not_safe (hall mixQ mix_conjunction_unsat)

/-- The conjunction is strictly stronger than the per-goal reading: both per-goal formulas have
models, the conjunction has none. -/
theorem conjunction_strictly_stronger :
    Satisfiable (formulaOfGoal mixQ Goal.secrecy) ∧
      Satisfiable (formulaOfGoal mixQ Goal.agreement) ∧
      ProtSat.Unsat (GoalAnalyze.formulaOfGoals mixQ) :=
  ⟨mix_sat_secrecy, mix_sat_agreement, mix_conjunction_unsat⟩


/-! ### 6. The composed driver, and decided instances -/

/-- **The composed attack verdict for one goal.** The caller hands over a candidate assignment for
THAT goal's own formula; the driver checks it clause by clause and, if it holds up, returns an attack
certificate. Nothing is trusted: `modelOK` is the walk, and the theorem below is the meaning. -/
def attackVerdictOfGoal (q : Query) (g : Goal) (asg : List (BVar × Bool)) : Result :=
  if modelOK (asgVal asg) (formulaOfGoal q g) = true then
    Result.attack (certOf q.protocol q.bounds (asgVal asg))
  else Result.unknown UnknownReason.resourceExhausted

/-- A candidate the verdict accepts really is a model of that goal's own formula. -/
theorem sat_of_attackVerdictOfGoal {q : Query} {g : Goal} {asg : List (BVar × Bool)}
    (h : attackVerdictOfGoal q g asg = Result.attack (certOf q.protocol q.bounds (asgVal asg))) :
    Satisfiable (formulaOfGoal q g) := by
  unfold attackVerdictOfGoal at h
  split at h
  · next he =>
      cases h
      exact ⟨asgVal asg, sat_of_modelOK he⟩
  · next => cases h

/-- **The composed attack verdict is sound.** An attack answer for a selected goal is a bounded
attack on the query, under the hypotheses that goal's own soundness theorem needs. -/
theorem boundedAttackGoals_of_attackVerdictOfGoal {q : Query} {g : Goal}
    {asg : List (BVar × Bool)} (hg : g ∈ q.goals)
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (h : attackVerdictOfGoal q g asg = Result.attack (certOf q.protocol q.bounds (asgVal asg))) :
    boundedAttackGoals q :=
  boundedAttackGoals_of_exists_sat hU hN ⟨g, hg, sat_of_attackVerdictOfGoal h⟩

/-- **The agreement safety verdict the conjunction could not give.** `authOrderP` is the
repository's honest authentication model: one session claims a triple and then commits it, so every
permitted execution that reaches the commit has already made the claim. Its agreement goal's own
formula is refutable, so the composition returns `boundedSafeGoals` - a verdict
`GoalAnalyze` withholds, because its bridge is the whole-list formula. -/
abbrev agreeP : Protocol := ProtSat.Reference.Contract.Gates.authOrderP

/-- The bounds of the honest authentication model. -/
abbrev agreeB : Bounds := ProtSat.Reference.Contract.Gates.authOrderB

/-- The agreement query over the honest model. -/
def agreeQ : Query := Query.mk agreeP agreeB [Goal.agreement]

theorem agree_hU : univClosed (shapeOf agreeP agreeB) agreeP := by
  unfold univClosed
  decide

theorem agree_hN : authNameable (shapeOf agreeP agreeB) agreeP :=
  AuthClauses.authNameable_gates.2.1

theorem agree_gap : domainGap agreeP agreeB = false := by decide

theorem agree_hsecStore : SecretsOKStore (shapeOf agreeP agreeB) agreeP := by
  intro q x h
  have h1 : agreeP.secrets = [] := rfl
  rw [h1] at h
  exact absurd h (by simp)

theorem agree_wf : WellFormed agreeQ := by
  show validate agreeQ = []
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Under `tripleOnly` every commit occurrence has at least the excusing claims it had under
`orderAware`, so the ordered formula's clause list is a sublist of the unordered one's and
unsatisfiability transfers. Decided on the model, not assumed. -/
theorem agree_excuse_subset :
    ∀ cl ∈ authExcuseClauses Matching.orderAware (shapeOf agreeP agreeB) agreeP,
      cl ∈ authExcuseClauses Matching.tripleOnly (shapeOf agreeP agreeB) agreeP := by decide

/-- The ordered violation group is a clause sublist of the unordered one: the demand and the
selector definitions are monitor-free, and every ordered excuse is an unordered excuse. Decided
over the handful of clauses the group actually has. -/
theorem agree_violation_subset :
    ∀ cl ∈ (authViolationClauses Matching.orderAware (shapeOf agreeP agreeB) agreeP).clauses,
      cl ∈ (authViolationClauses Matching.tripleOnly (shapeOf agreeP agreeB) agreeP).clauses := by
  decide

/-- Hence the whole ordered-monitor encoding is a clause sublist of the unordered-monitor one,
without searching the 675 shared semantic clauses. -/
theorem agree_clauses_subset :
    ∀ c ∈ (agreementEncode agreeP agreeB Matching.orderAware).clauses,
      c ∈ (agreementEncode agreeP agreeB Matching.tripleOnly).clauses := by
  intro c hc
  unfold AuthClauses.agreementEncode at hc ⊢
  cases List.mem_append.mp hc with
  | inl h => exact List.mem_append.mpr (Or.inl h)
  | inr h => exact List.mem_append.mpr (Or.inr (agree_violation_subset c h))

/-- **The agreement goal's own formula is refutable on the honest model.** The refutation is the
repository's own: `AuthClauses.gate_order_unsat` checks a resolution refutation of a small core of the
ordered encoding, and the clause-subset transfer carries it to the monitor `Query.Violation` pairs
with. No solver is replayed on the agreement formula itself.

Read this together with `allGoalsRefuted`, which is where a serialized refutation of a goal's
own formula would enter: the UNSAT fact here is inherited from the existing gate (a checked core plus
the proved-solver theorem `DPLL.dpll_complete` replayed by the kernel), not from a `checkCode` artifact
against `formulaOfGoal agreeQ Goal.agreement`. No such artifact is embedded anywhere in this file: the
repository's producers do not refute an agreement formula at affordable fuel, and the saturation
engine's own header records why. The safety conclusion is therefore kernel-checked and solver-independent
in the sense that the kernel re-runs the search and the transfer proofs, but it is not a linear proof
check the way the secrecy route's `AnalyzerEvidence.qgCode` is. -/
theorem agree_unsat_goal : ProtSat.Unsat (formulaOfGoal agreeQ Goal.agreement) := by
  rw [formulaOfGoal_agreement]
  exact AuthClauses.unsat_of_clauses_subset agree_clauses_subset AuthClauses.gate_order_unsat

/-- **AN AGREEMENT SAFETY VERDICT, for the first time on this route.** No selected goal of
`agreeQ` is violated by any permitted execution: the query's agreement goal is safe, in the
contract's own vocabulary. -/
theorem agree_boundedSafe : boundedSafeGoals agreeQ :=
  boundedSafeGoals_of_forall_unsat agree_hU agree_hN agree_hsecStore agree_gap
    (fun g hg => by
      have hgeq : g = Goal.agreement := List.mem_singleton.mp hg
      subst hgeq
      exact agree_unsat_goal)

/-- In the public vocabulary: no permitted execution of the honest model commits a triple that was
never claimed. -/
theorem agree_no_break :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg),
      BoundedTrace agreeP agreeB tr Cs ∧ AuthBreak agreeP Cs tr := by
  rintro ⟨tr, Cs, hbt, hv⟩
  exact agree_boundedSafe ⟨Goal.agreement, by simp [agreeQ], tr, Cs, hbt,
    by rw [violation_agreement]; exact hv⟩

/-! #### 6b. Decided: the mixed-goal attack through the composed route -/


def mixAgrAsg : List (BVar × Bool) := [(342, true), (343, true), (344, true), (345, true), (82, true), (337, true), (338, true), (339, true), (340, true), (77, true), (332, true), (333, true), (334, true), (335, true), (72, true), (307, true), (308, true), (309, true), (310, true), (175, true), (292, true), (293, true), (294, true), (295, true), (160, true), (277, true), (278, true), (279, true), (280, true), (145, true), (262, true), (263, true), (264, true), (265, true), (130, true), (247, true), (248, true), (249, true), (250, true), (115, true), (232, true), (233, true), (234, true), (235, true), (100, true), (87, true), (88, true), (89, true), (0, true), (180, true), (2, true), (182, true), (4, true), (184, true), (16, true), (21, true), (26, true), (42, true), (43, true), (47, true), (48, true), (93, true), (225, true), (95, true), (227, true), (228, true), (229, true), (230, true), (108, true), (240, true), (110, true), (242, true), (243, true), (244, true), (245, true), (123, true), (255, true), (125, true), (257, true), (258, true), (259, true), (260, true), (138, true), (270, true), (140, true), (272, true), (273, true), (274, true), (275, true), (153, true), (285, true), (155, true), (287, true), (288, true), (289, true), (290, true), (168, true), (300, true), (170, true), (302, true), (303, true), (304, true), (305, true), (10, true), (190, true), (41, true), (410, true), (54, true), (314, true), (315, true), (316, true), (317, true), (318, true), (319, true), (320, true), (6, true), (186, true), (31, true), (9, true), (36, true)]

def mixSecAsg : List (BVar × Bool) := [(342, true), (343, true), (344, true), (345, true), (82, true), (337, true), (338, true), (339, true), (340, true), (77, true), (332, true), (333, true), (334, true), (335, true), (72, true), (307, true), (308, true), (309, true), (310, true), (175, true), (292, true), (293, true), (294, true), (295, true), (160, true), (277, true), (278, true), (279, true), (280, true), (145, true), (262, true), (263, true), (264, true), (265, true), (130, true), (247, true), (248, true), (249, true), (250, true), (115, true), (232, true), (233, true), (234, true), (235, true), (100, true), (87, true), (88, true), (89, true), (0, true), (180, true), (2, true), (182, true), (4, true), (184, true), (16, true), (21, true), (26, true), (42, true), (43, true), (47, true), (48, true), (93, true), (225, true), (95, true), (227, true), (228, true), (229, true), (230, true), (108, true), (240, true), (110, true), (242, true), (243, true), (244, true), (245, true), (123, true), (255, true), (125, true), (257, true), (258, true), (259, true), (260, true), (138, true), (270, true), (140, true), (272, true), (273, true), (274, true), (275, true), (153, true), (285, true), (155, true), (287, true), (288, true), (289, true), (290, true), (168, true), (300, true), (170, true), (302, true), (303, true), (304, true), (305, true), (10, true), (190, true), (41, true), (50, true), (353, true), (53, true), (313, true), (314, true), (315, true), (316, true), (317, true), (318, true), (319, true), (320, true), (8, true), (188, true), (36, true), (7, true), (31, true)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **The kernel checks the agreement model of the agreement goal's own formula.** A walk over the
490 clauses of `formulaOfGoal mixQ Goal.agreement` - no search. -/
theorem mix_agr_modelOK :
    modelOK (asgVal mixAgrAsg) (formulaOfGoal mixQ Goal.agreement) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **The kernel checks the secrecy model of the secrecy goal's own formula.** -/
theorem mix_sec_modelOK :
    modelOK (asgVal mixSecAsg) (formulaOfGoal mixQ Goal.secrecy) = true := by decide

theorem mix_agr_sat_checked : Satisfiable (formulaOfGoal mixQ Goal.agreement) :=
  ⟨asgVal mixAgrAsg, sat_of_modelOK mix_agr_modelOK⟩

theorem mix_sec_sat_checked : Satisfiable (formulaOfGoal mixQ Goal.secrecy) :=
  ⟨asgVal mixSecAsg, sat_of_modelOK mix_sec_modelOK⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **A DECIDED MIXED-GOAL ATTACK VERDICT THROUGH THE COMPOSED ROUTE.** The kernel re-checks the
model of the agreement goal's own formula and the composed verdict is ATTACK - on a query whose
conjoined formula has no model at all. -/
theorem mix_composed_verdict_attack :
    (match attackVerdictOfGoal mixQ Goal.agreement mixAgrAsg with
     | Result.attack _ => true
     | _ => false) = true := by
  simp only [attackVerdictOfGoal, mix_agr_modelOK, ite_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The same on the secrecy goal's own formula. -/
theorem mix_composed_verdict_attack_secrecy :
    (match attackVerdictOfGoal mixQ Goal.secrecy mixSecAsg with
     | Result.attack _ => true
     | _ => false) = true := by
  simp only [attackVerdictOfGoal, mix_sec_modelOK, ite_true]

/-- The decided model, fed through the composition, gives the contract's attack - which the
conjunction could not. -/
theorem mix_composed_attack_checked : boundedAttackGoals mixQ :=
  boundedAttackGoals_of_attackVerdictOfGoal (by decide : Goal.agreement ∈ mixQ.goals) mix_hU mix_hN (by
    show attackVerdictOfGoal mixQ Goal.agreement mixAgrAsg
         = Result.attack (certOf mixP mixB (asgVal mixAgrAsg))
    rw [attackVerdictOfGoal, mix_agr_modelOK]
    rfl)

/-- The certificate the composed route hands back is accepted by the independent checker: the attack
does not depend on the encoder or the solver, only on the run. -/
theorem mix_composed_cert_checked :
    checkCertificate mixP (certOf mixP mixB (asgVal mixAgrAsg)) = true := by
  have hagr : Sat (asgVal mixAgrAsg)
      (encodeGoalsOfM mixP mixB [Goal.agreement] Matching.tripleOnly) :=
    sat_of_modelOK mix_agr_modelOK
  exact GoalAnalyze.certOf_checked_of_authBreak mix_hU
    (GoalEncode.sat_baseEncode_of_sat hagr)
    (GoalAnalyze.authBreak_of_sat_agreement mix_hU mix_hN hagr)

end ProtSat.GoalCompose
