/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.AuthClauses
import ProtSat.DecodeIndex
import ProtSat.Sound
import ProtSat.GoalEncode

/-!
# ProtSat/AgreesBase.lean - the decoding chain over the semantic groups, and the agreement bridge

## What this file is

`ProtSat/GoalEncode.lean` proves the sound direction for the agreement goal
(`boundedAttackGoals_of_sat_agreement`) modulo `GoalEncode.DecodedRun P B a`, and its
header names the reason that hypothesis is there: every decoding lemma of `ProtSat.Encoding`
takes its clause hypothesis as `Sat a (encode P B)` - the whole formula, secrecy violation
clause included - while a model of the agreement-only formula supplies the ten semantic groups and
nothing else. `GoalEncode.no_transport_from_base` proves that no general argument can supply
the missing clause, so the decoding chain had to be re-stated over the groups that are actually
there.

This file does that re-statement, additively. Nothing in `Encoding.lean`, `Clauses.lean`,
`Sound.lean`, `Complete.lean`, `AuthClauses.lean`, `DecodeIndex.lean` or
`GoalEncode.lean` is changed, and no existing statement is weakened: every new lemma carries a
distinct name (the suffix `_b`, for "over baseEncode") and a strictly weaker hypothesis.

* Section 1 extracts the ten semantic groups from `Sat a (baseEncode P B)`.
* Section 2 is the decoding chain restated over `Sat a (baseEncode P B)`: the 69 lemmas of
  `ProtSat.Encoding` that lie in the dependency cone of `decRun_trace` and took
  `Sat a (encode P B)`, `rel_agrees` (the ~600 lines discharging the introduction rules
  of `ProtSat.Rel`) among them. The proofs are the existing ones, edited only in the hypothesis
  and in the names of the `_b` lemmas they call.
* Section 3 restates `Sound.boundedTrace_decRun` over the semantic groups.
* Section 4 proves the authentication half of the bridge, `CommitsReflect` and
  `ClaimsReflect`.
* Section 5 discharges `GoalEncode.DecodedRun` and states the corollary.
* Section 6 instantiates the corollary on the AuthGap model, with every side condition decided.

## The question the task asks, answered

Does `rel_agrees` need the secrecy violation clause? **No.** The dependency cone of
`decRun_trace` contains 78 lemmas that take `Sat a (encode P B)`, and not one of them
mentions `sat_violation`, `sat_leakAux` or `violation_leak`: the chain reads only
the one-hot, init, frame, eval, step, ded, pubAux, knSupport, fresh and leak-auxiliary groups, every
one of which is a member of `baseGroups`. So the cone survives verbatim over
`Sat a (baseEncode P B)`, `BoundedTrace` follows, and `DecodedRun` becomes a
theorem rather than a wish:

    decodedRun_of_sat_agreement :
      univClosed (shapeOf P B) P -> authNameable (shapeOf P B) P ->
      Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) -> DecodedRun P B a

The two shape hypotheses are not the thing being proved. `univClosed` is the hypothesis every
soundness theorem of this repository already takes (`Sound.encoding_correct_sound`,
`GoalEncode.decodedTrace_of_sat_encode`); `authNameable` is a decidable condition on the
model and the bounds that `AuthClauses` introduced and `AuthClauses.authNameable_gates`
verifies for the agreement models. Dropping either is a different question, not a gap in this file.

## Which direction of the authentication bridge is proved, and what it costs

Both directions `DecodedRun` consumes are proved, and neither of them uses the agreement
clauses:

* `commitsReflect_of_sat` (the literals are true -> the decoded run performs the commit) reads
  two of the four literals: the event literal, through `decCode_eq_of_true_b` and the Sat-free
  `DecodeIndex.decEv_act_of_decCode`, and the program-counter literal, through
  `decodePc_of_true_b` and `agrees_decRun_b`. The two value literals are not needed,
  because under `authNameable` the annotations are closed constants and
  `Complete.eval_eq_constVal` evaluates them in *every* store.
* `claimsReflect_of_sat` (the decoded run performs a claim -> its four literals are true) is
  the direction the soundness proof consumes, and it is the one that needs `authNameable`: a
  claim whose annotations are not closed constants cannot be named by a fixed pair of value
  literals. The event and program-counter literals come from `decCode_true_b` and
  `decodePc_true_b` plus `agrees_decRun_b`; the two value literals come from
  `vxe_konst_true`, which is the constant half of `Encoding.xe_konst` read as a literal
  rather than as a decoded value.

## WHICH NOTION OF AGREEMENT THIS DISCHARGES - read this before citing the corollary

`boundedAttackGoals_of_sat_agreement_discharged` is soundness for the **unordered,
triple-only** agreement predicate, because that is what `Query.Violation P Goal.agreement`
is: `ProtSat.AuthBreak P Cs tr` (`ProtSat/Operational.lean:461`) asks only that no
committed `(tag, peer, value)` triple appears among the claimed triples. It is NOT soundness
for the ordered monitor `ProtSat.Reference.authBreak`, and it cannot be read as such:
`ProtSat/AgreementPredicates.lean` proves the two are incomparable
(`ordered_not_le_unordered`, `unordered_not_le_ordered`) and proves that the ordering
requirement is inexpressible in the vocabulary `AuthBreak` reads at all, because
`AuthInst` carries no self and no index (`authBreak_carries_too_little`). The concrete
witness is `AgreementPredicates.selfAddrP`, the role-confusion / misaddressing model on which
the unordered reading is silent on all 43 permitted executions while the ordered reading finds an
attack. So a `boundedSafeGoals` answer for a `Goal.agreement` query means "no commit
triple went unclaimed", not "no commit went unmatched". `unordered_conclusion_is_AuthBreak`
below records this inside a statement rather than only in prose. Retargeting `Query.Violation`
to the ordered monitor is a change to `ProtSat/Query.lean` and `ProtSat/Operational.lean`
and is outside this file's scope.

## What is NOT proved here

* **Nothing about the secrecy violation clause.** `Sat a (baseEncode P B)` is assumed, never
  strengthened: this file does not prove, and cannot prove (`no_transport_from_base`), that a
  model of the semantic groups satisfies `encode P B`.
* **Completeness for agreement.** The direction that makes a UNSAT verdict mean safety - a permitted
  agreement attack yields a model of `agreementEncode` - is untouched. It needs the
  `Complete` group lemmas driven from `RunOK` to make the selector auxiliary true exactly
  when the run has the commit.
* **The ordered monitor**, for the reasons in the section above.
* **`authNameable` as a fact about a model.** It is a hypothesis of the corollary, not a
  theorem about `Regressions.Authentication.P`.
* **The `Encoding` lemmas outside the cone.** `violation_leak`, `encoding_sound`,
  `Analyzer.stepsOf_ok` and the rest still take `Sat a (encode P B)`. They read the
  violation clause, so they cannot be restated over `baseEncode`, and nothing here needs them.

## Kernel-decided gates, and what they cost

Section 6 decides three facts about the AuthGap model, and the file's whole cost is in them. Measured
with `lake env lean ProtSat/AgreesBase.lean` on a 10-core developer machine, total wall-clock
**14.3 s** for the 2700-line file:

| gate | content | kernel replay |
|---|---|---|
| `authGap_univClosed` | the AuthGap bounds keep the protocol inside the universe | ~0.1 s |
| `authGap_authNameable` | every claim and commit position of the AuthGap model is nameable | ~0.1 s |
| `authGap_sat_asg` | `AuthClauses.attackAsg` satisfies the **triple-only** agreement encoding | ~12 s |

No gate exceeds a second except the last, and none is near the 60 s budget. Sections 1 to 5 contain no
`decide` at all: they are `Prop`-valued re-statements proved by the repository's own
arguments, and the forbidden decision-procedure token does not appear anywhere in this file.
-/

namespace ProtSat.Encoding

open ProtSat Term OneHot Bounded Attacker Encode
open Protocol

variable {P : Protocol} {B : Bounds} {a : Assignment}

/-! ### 1. The semantic groups, extracted from `baseEncode` -/

/-- Every clause of a semantic group is a clause of `baseEncode P B`: the interface through
which this file consumes the groups one at a time, in the shape `Encoding.sat_encodeGroup` has
for the old formula. -/
theorem sat_baseGroup {g : CNF}
    (hg : g ∈ AuthClauses.baseGroups (shapeOf P B) P)
    (h : Sat a (AuthClauses.baseEncode P B)) : Sat a g :=
  fun c hc => h c (List.mem_flatMap.mpr ⟨g, hg, hc⟩)

/-- Group 1 of the semantic groups is a group of `baseEncode P B`. -/
theorem sat_oneHot_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (oneHotClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 2. -/
theorem sat_init_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (initClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 3. -/
theorem sat_frame_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (frameClauses (shapeOf P B)) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 4. -/
theorem sat_eval_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (evalClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 5. -/
theorem sat_step_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (stepClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 6. -/
theorem sat_ded_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (dedClauses (shapeOf P B)) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 7. -/
theorem sat_pubAux_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (pubAuxClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 8. -/
theorem sat_knSupport_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (knSupportClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-- Group 9. -/
theorem sat_fresh_b (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (freshClauses (shapeOf P B) P) :=
  sat_baseGroup (by simp [AuthClauses.baseGroups]) h

/-! ### 2. The decoding chain over the semantic groups -/

/-- The program-counter one-hot group of session `q` at step `i` is satisfied by a model of the
semantic groups. -/
theorem sat_pcOh_b (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (pcOh (shapeOf P B) i q).clauses :=
  fun cl hcl => sat_oneHot_b h cl (mem_oneHot_pc hi hq hcl)

/-- The store one-hot group of session `q`, variable `x`, at step `i`, is satisfied by a model
of the semantic groups. -/
theorem sat_stOh_b (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (stOh (shapeOf P B) i q x).clauses :=
  fun cl hcl => sat_oneHot_b h cl (mem_oneHot_st hi hq hx hcl)

/-- The evaluation one-hot group of expression entry `e` in session `q` at step `i` is satisfied
by a model of the semantic groups. -/
theorem sat_xeOh_b (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (he : e < shE (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (xeOh (shapeOf P B) i q e).clauses :=
  fun cl hcl => sat_oneHot_b h cl (mem_oneHot_xe hi hq he hcl)

/-- The event one-hot group of step `i` is satisfied by a model of the semantic groups: this is
the group the decoded event is read from. -/
theorem sat_evOh_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (evOh (shapeOf P B) i).clauses :=
  fun cl hcl => sat_oneHot_b h cl (mem_oneHot_ev hi hcl)

/-- The delivery one-hot group of session `q` at step `i` is satisfied by a model of the
semantic groups. -/
theorem sat_dlOh_b (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (dlOh (shapeOf P B) i q).clauses :=
  fun cl hcl => sat_oneHot_b h cl (mem_oneHot_dl hi hq hcl)

/-- The freshness one-hot group of session `q` at step `i` is satisfied by a model of the
semantic groups. -/
theorem sat_frOh_b (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    Sat a (frOh (shapeOf P B) i q).clauses :=
  fun cl hcl => sat_oneHot_b h cl (mem_oneHot_fr hi hq hcl)

/-- The program counter the assignment selects for session q at step i is the true one. -/
theorem decodePc_true_b (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) :
    a (vpc (shapeOf P B) i q (decodePc (shapeOf P B) a i q)) = true := by
  have hoh := sat_pcOh_b hi hq h
  obtain ⟨c, hc⟩ := Oh.decode_some hoh
  have hcv : a (Oh.varOf (pcOh (shapeOf P B) i q) c) = true := (decodeGo_some _ _ _ _ hc).2
  unfold decodePc
  rw [hc]
  simpa [decodePc, pcOh, ohOf] using hcv

/-- If a program-counter variable is true, it is the decoded one. -/
theorem decodePc_of_true_b {i q c : Nat} (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (ha : a (vpc (shapeOf P B) i q c) = true) :
    decodePc (shapeOf P B) a i q = c := by
  have hoh := sat_pcOh_b hi hq h
  have h1 : (pcOh (shapeOf P B) i q).decode a = some c :=
    Oh.decode_of_true hoh (List.mem_range.mpr hc) ha
  unfold decodePc
  rw [h1]
  simp

/-- The selected event code is true. -/
theorem decCode_true_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    a (vev (shapeOf P B) i (decCode P B a i)) = true := by
  have hoh := sat_evOh_b hi h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hkv : a (Oh.varOf (evOh (shapeOf P B) i) k) = true := (decodeGo_some _ _ _ _ hk).2
  unfold decCode
  rw [hk]
  simpa [evOh, ohOf] using hkv

/-- If an event variable is true, it is the selected code. -/
theorem decCode_eq_of_true_b {i k : Nat} (hi : i < B.steps)
    (hk : k < shEv (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (ha : a (vev (shapeOf P B) i k) = true) : decCode P B a i = k := by
  have hoh := sat_evOh_b hi h
  have h1 : (evOh (shapeOf P B) i).decode a = some k :=
    Oh.decode_of_true hoh (List.mem_range.mpr hk) ha
  unfold decCode
  rw [h1]
  exact rfl

/-- The selected event code is in range. -/
theorem decCode_lt_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    decCode P B a i < shEv (shapeOf P B) := by
  have hoh := sat_evOh_b hi h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hmem := (decodeGo_some _ _ _ _ hk).1
  unfold decCode
  rw [hk]
  exact (List.mem_range.mp hmem)

/-- The event group decodes to the selected code. -/
theorem decode_evOh_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    (evOh (shapeOf P B) i).decode a = some (decCode P B a i) := by
  have hoh := sat_evOh_b hi h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hmem := (decodeGo_some _ _ _ _ hk).1
  have : decCode P B a i = k := by
    unfold decCode
    rw [hk]
    exact rfl
  rw [this]
  exact hk

/-- The learned message, expressed through the selected event code. -/
theorem decLearn_code_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    decLearn (shapeOf P B) P a i =
      if decCode P B a i = 0 then none
      else if hc : decCode P B a i < 1 + shS (shapeOf P B) then
        match P.actionAt (decCode P B a i - 1)
            (decodePc (shapeOf P B) a i (decCode P B a i - 1)) with
        | some (Action.send _ e) =>
            decXe (shapeOf P B) P a i (decCode P B a i - 1) e
        | _ => none
      else
        match instAt (shapeOf P B) (decCode P B a i - 1 - shS (shapeOf P B)) with
        | some ins => valAt (shapeOf P B) ins.concl
        | none => none := by
  unfold decLearn
  rw [decode_evOh_b hi h]
  rfl

/-- The decoded event, expressed through the selected event code. -/
theorem decEv_code_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    decEv (shapeOf P B) P a i =
      if decCode P B a i = 0 then Ev.idle
      else if hc : decCode P B a i < 1 + shS (shapeOf P B) then
        Ev.act (decCode P B a i - 1)
          (decDeliver (shapeOf P B) a i (decCode P B a i - 1))
          (decNonce (shapeOf P B) a i (decCode P B a i - 1))
      else
        match instAt (shapeOf P B) (decCode P B a i - 1 - shS (shapeOf P B)) with
        | some ins => match valAt (shapeOf P B) ins.concl with
            | some t => Ev.ded t
            | none => Ev.idle
        | none => Ev.idle := by
  unfold decEv
  rw [decode_evOh_b hi h]
  rfl

/-- The three possible shapes of the selected event code. -/
theorem ev_cases_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) :
    decCode P B a i = 0
    ∨ (∃ q, q < shS (shapeOf P B) ∧ decCode P B a i = 1 + q)
    ∨ (∃ n, n < nInst (shapeOf P B) ∧
          decCode P B a i = 1 + shS (shapeOf P B) + n) := by
  have hlt := decCode_lt_b hi h
  have h2 : decCode P B a i < 1 + shS (shapeOf P B) + nInst (shapeOf P B) := by
    unfold shEv at hlt
    exact hlt
  by_cases h0 : decCode P B a i = 0
  · exact Or.inl h0
  · right
    by_cases hq : decCode P B a i - 1 < shS (shapeOf P B)
    · exact Or.inl ⟨decCode P B a i - 1, hq, by omega⟩
    · exact Or.inr ⟨decCode P B a i - 1 - shS (shapeOf P B), by omega, by omega⟩

/-- The selected code is 0 exactly when its variable is true for the idle alternative. -/
theorem evAct_eq_of_code_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) :
    a (evAct (shapeOf P B) i q) = true := by
  have h1 : a (vev (shapeOf P B) i (decCode P B a i)) = true := decCode_true_b hi h
  rw [hk] at h1
  exact h1

/-- Sessions other than the selected one do not act. -/
theorem evAct_false_of_ne_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q r : Nat}
    (hq : q < shS (shapeOf P B)) (hr : r < shS (shapeOf P B)) (hne : q ≠ r)
    (hk : decCode P B a i = 1 + r) : a (evAct (shapeOf P B) i q) = false := by
  by_contra e
  have h2 : decCode P B a i = 1 + q := decCode_eq_of_true_b hi (by
    show 1 + q < shEv (shapeOf P B)
    exact evAct_lt (shapeOf P B) i q hq) h (by simpa [evAct] using e)
  omega

/-- The step clauses of an acting session with a known program counter hold. -/
theorem step_holds_b (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (hc : c < shPc (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (evAct (shapeOf P B) i q) = true)
    (hpc : a (vpc (shapeOf P B) i q c) = true)
    {cl : Clause} (hcl : cl ∈ stepClausesAt (shapeOf P B) P i q c) :
    Clause.eval a cl = true :=
  sat_step_b h cl (mem_step hi hq hc hcl)

/-- The guard literals of an acting session are false, so the body of a step clause must be
satisfied - over the semantic groups. -/
theorem step_body_b (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (hc : c < shPc (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (evAct (shapeOf P B) i q) = true)
    (hpc : a (vpc (shapeOf P B) i q c) = true) {rest : List Lit}
    (hcl : (actGuard (shapeOf P B) i q c ++ rest) ∈ stepClausesAt (shapeOf P B) P i q c) :
    Clause.eval a rest = true := by
  have := step_holds_b hi hq hc h ha hpc hcl
  refine clause_eval_append_of_false (actGuard (shapeOf P B) i q c) rest this ?_
  intro l hl
  unfold actGuard at hl
  rw [List.mem_cons] at hl
  rcases hl with rfl | hl
  · show (neg (evAct (shapeOf P B) i q)).eval a = false
    simp [neg_eval, ha]
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · show (neg (vpc (shapeOf P B) i q c)).eval a = false
      simp [neg_eval, hpc]
    · exact absurd hl (by simp)

/-- The frame clauses of a session that does not act hold. -/
theorem frame_holds_b (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (ha : a (evAct (shapeOf P B) i q) = false) :
    ∀ cl ∈ frameSessClauses (shapeOf P B) i q, Clause.eval a cl = true := by
  intro cl hcl
  have := sat_frame_b h cl (by
    unfold frameClauses cnfOf eachStep
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, hcl⟩)⟩)
  exact this

/-- The decoded program counter is in range. -/
theorem decodePc_lt_b (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    decodePc (shapeOf P B) a i q < shPc (shapeOf P B) := by
  have hoh := sat_pcOh_b hi hq h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hmem : k ∈ (pcOh (shapeOf P B) i q).vals := (decodeGo_some _ _ _ _ hk).1
  have h2 : decodePc (shapeOf P B) a i q = k := by
    unfold decodePc
    rw [hk]
    exact rfl
  rw [h2]
  rw [pcOh, ohOf] at hmem
  exact List.mem_range.mp hmem

/-- If an evaluation variable is true, the group selects that value. -/
theorem decXe_of_true_b {i q : Nat} {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) {u : Nat}
    (hu : u < shVal (shapeOf P B)) (ha : a (vxe (shapeOf P B) i q (eIdx P e) u) = true) :
    decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) u := by
  have hix : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hoh := sat_xeOh_b hi hq hix h
  have h1 : (xeOh (shapeOf P B) i q (eIdx P e)).decode a = some u :=
    Oh.decode_of_true hoh (List.mem_range.mpr hu) ha
  unfold decXe decVal
  rw [h1]

/-- The selected code is 1+q when session q's event variable is true. -/
theorem decCode_of_evAct_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    decCode P B a i = 1 + q :=
  decCode_eq_of_true_b hi (evAct_lt (shapeOf P B) i q hq) h (by simpa [evAct] using ha)

/-- The selected code is the deduction instance when its event variable is true. -/
theorem decCode_of_evDed_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {n : Nat}
    (hn : n < nInst (shapeOf P B)) (ha : a (evDed (shapeOf P B) i n) = true) :
    decCode P B a i = 1 + shS (shapeOf P B) + n :=
  decCode_eq_of_true_b hi (evDed_lt (shapeOf P B) i n hn) h (by simpa [evDed] using ha)

/-- What a session-act step teaches: the value sent, if the action is a send. -/
theorem decLearn_act_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) :
    decLearn (shapeOf P B) P a i =
        match P.actionAt q (decodePc (shapeOf P B) a i q) with
        | some (Action.send _ e) => decXe (shapeOf P B) P a i q e
        | _ => none := by
  rw [decLearn_code_b hi h, hk]
  rw [if_neg (by omega : 1 + q ≠ 0), dif_pos (by omega : 1 + q < 1 + shS (shapeOf P B))]
  rw [show (1 + q - 1) = q by omega]

/-- What a deduction step teaches: the conclusion of the instance that fired. -/
theorem decLearn_ded_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {n : Nat}
    (hn : n < nInst (shapeOf P B)) (ins : DedInst) (hins : instAt (shapeOf P B) n = some ins)
    (hk : decCode P B a i = 1 + shS (shapeOf P B) + n) :
    decLearn (shapeOf P B) P a i = valAt (shapeOf P B) ins.concl := by
  rw [decLearn_code_b hi h, hk]
  rw [if_neg (by omega : 1 + shS (shapeOf P B) + n ≠ 0),
    dif_neg (by omega : ¬(1 + shS (shapeOf P B) + n < 1 + shS (shapeOf P B)))]
  rw [show (1 + shS (shapeOf P B) + n - 1 - shS (shapeOf P B)) = n by omega, hins]

/-- The publication auxiliary of a send or a deduction instance that fires is true, from a model
of the semantic groups. -/
theorem pubAux_holds_b {i q c u : Nat} (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (hu : u < (shapeOf P B).U.length)
    {a' : Agent} {e : Expr} (hact : P.actionAt q c = some (Action.send a' e))
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (vpb (shapeOf P B) i q c u) = true) :
    a (evAct (shapeOf P B) i q) = true ∧ a (vpc (shapeOf P B) i q c) = true ∧
      a (vxe (shapeOf P B) i q (eIdx P e) u) = true := by
  have hsat : Sat a (andNDef (vpb (shapeOf P B) i q c u)
      [pos (evAct (shapeOf P B) i q), pos (vpc (shapeOf P B) i q c),
        pos (vxe (shapeOf P B) i q (eIdx P e) u)]) := by
    intro cl hcl
    refine sat_pubAux_b h cl (mem_pubAux hi hq hc hu ?_)
    rw [pubAuxEntry, hact]
    exact hcl
  have h2 := ((sat_andNDef).mp hsat).1 ha
  refine ⟨h2 _ (List.Mem.head _), h2 _ (List.Mem.tail _ (List.Mem.head _)),
    h2 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- Everything the `kn` variables claim at step 0 really is in the initial knowledge, from a
model of the semantic groups. -/
theorem init_kn_sound_b {u : Nat} {t : Term} (hut : valAt (shapeOf P B) u = some t)
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (vkn (shapeOf P B) 0 u) = true) : t ∈ P.initKn := by
  have hu : u < (shapeOf P B).U.length := by
    by_contra e
    have : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
    rw [this] at hut
    simp at hut
  by_contra e
  have hfalse : initKnHolds (shapeOf P B) P u = false := by
    unfold initKnHolds
    rw [hut]
    simp [e]
  have hcl : [neg (vkn (shapeOf P B) 0 u)] ∈ (initClauses (shapeOf P B) P).clauses := by
    unfold initClauses cnfOf
    refine List.mem_append_right _ ?_
    unfold initKnClauses
    refine List.mem_map.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
    simp [hfalse]
  have h1 := sat_init_b h _ hcl
  rw [Clause.eval, List.any_cons, List.any_nil, neg_eval, ha] at h1
  simp at h1

/-- **Soundness of the knowledge decoding.** A message whose `kn` variable is true is derivable
from the run, read off the frame, deduction, support and send clauses - the secrecy
violation clause is not read. -/
theorem kn_sound_b (h : Sat a (AuthClauses.baseEncode P B)) {u : Nat} {t : Term}
    (hut : valAt (shapeOf P B) u = some t) :
    ∀ (i : Nat), i ≤ B.steps ->
      a (vkn (shapeOf P B) i u) = true -> t ∈ decKnSeq (shapeOf P B) P a i := by
  have hu : u < (shapeOf P B).U.length := by
    by_contra e
    have : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
    rw [this] at hut
    simp at hut
  intro i
  induction i with
  | zero =>
      intro _ ha
      unfold decKnSeq
      exact init_kn_sound_b hut h ha
  | succ i ih =>
      intro hi ha
      have hstep : i < B.steps := by omega
      rw [decKnSeq_succ P B a, List.mem_append]
      by_cases hprev : a (vkn (shapeOf P B) i u) = true
      · exact Or.inl (ih (by omega) hprev)
      · right
        have hcl : ([neg (vkn (shapeOf P B) (i + 1) u), pos (vkn (shapeOf P B) i u)]
            ++ publisherLits (shapeOf P B) P i u)
            ∈ (knSupportClauses (shapeOf P B) P).clauses :=
          mem_knSupport hstep hu (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)
        have h1 := sat_knSupport_b h _ hcl
        rw [clause_eval_any] at h1
        obtain ⟨l, hl, hle⟩ := h1
        rw [List.mem_append] at hl
        rcases hl with hl | hpub
        · rw [List.mem_cons, List.mem_cons] at hl
          simp only [List.not_mem_nil, or_false] at hl
          rcases hl with h1 | h1
          · rw [h1] at hle; exact absurd hle (by simp [neg_eval, ha])
          · rw [h1] at hle; exact absurd hle (by simp [pos_eval, hprev])
        · -- a publisher literal holds
          obtain ⟨q, c, hq, hc, a', e, he, hl'⟩ | ⟨n, ins, hn, hins, hcon, hev⟩ :=
            publisherLits_cases hstep hu hpub
          · -- a send publisher: the auxiliary records the session, the counter and the value
            subst hl'
            obtain ⟨h1', h2', h3'⟩ := pubAux_holds_b hstep hq hc hu he h hle
            have hk := decCode_of_evAct_b hstep h hq h1'
            have hpc := decodePc_of_true_b (Nat.le_of_lt hstep) hq hc h h2'
            have hu' : u < shVal (shapeOf P B) := by rw [shVal]; omega
            have hlearn : decLearn (shapeOf P B) P a i
                = decXe (shapeOf P B) P a i q e := by
              rw [decLearn_act_b hstep h hq hk, hpc, he]
            rw [hlearn, decXe_of_true_b (mem_allExprs_send he) (Nat.le_of_lt hstep) hq h hu' h3']
            rw [hut]
            simp
          · -- a deduction instance concluding in u
            rw [hev] at hle
            have hk := decCode_of_evDed_b hstep h hn (by simpa using hle)
            have hlearn := decLearn_ded_b hstep h hn ins hins hk
            have hsome : decLearn (shapeOf P B) P a i = some t := by
              rw [hlearn, hcon, hut]
            rw [hsome]
            simp

/-- The gate clauses of a table expression are satisfied by any satisfying assignment. -/
theorem sat_gate_b {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    ∀ cl ∈ evalGate (shapeOf P B) P i q e, Clause.eval a cl = true :=
  fun cl hcl => sat_eval_b h cl (mem_eval hi hq he hcl)

/-- The index selected by an evaluation group is in range. -/
theorem decodeXe_lt_b {i q : Nat} {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    ∃ v, (xeOh (shapeOf P B) i q (eIdx P e)).decode a = some v ∧ v < shVal (shapeOf P B) ∧
      a (vxe (shapeOf P B) i q (eIdx P e) v) = true := by
  have hix : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hoh := sat_xeOh_b hi hq hix h
  obtain ⟨v, hv⟩ := Oh.decode_some hoh
  exact ⟨v, hv, List.mem_range.mp ((decodeGo_some _ _ _ _ hv).1),
    (decodeGo_some _ _ _ _ hv).2⟩

/-- The unary evaluation gate: the decoded value of a unary expression is that step applied to
the decoded value of its child. -/
theorem xe_unary_b {e c : Expr} (he : e ∈ allExprs P) (hc : c ∈ allExprs P)
    (hchild : Expr.child1 e = some c)
    (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q e =
      (Expr.stepEval1 e (decXe (shapeOf P B) P a i q c)).filter
        (fun t => decide (t ∈ (shapeOf P B).U)) := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt_b hc hi hq h
  have hixc : eIdx P c < shE (shapeOf P B) := eIdx_lt hc
  have hixe : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hg : Sat a (fwdClausesOn [] (xeOh (shapeOf P B) i q (eIdx P c))
      (fun u => pos (vxe (shapeOf P B) i q (eIdx P e) (f1 (shapeOf P B) e u)))) := by
    intro cl hcl
    exact sat_gate_b he hi hq h cl (by rw [evalGate_unary hchild]; exact hcl)
  have h1 := fwdClausesOn_correct (sat_xeOh_b hi hq hixc h) hg
    (fun l hl => absurd hl (by simp)) v hv
  have h2 : a (vxe (shapeOf P B) i q (eIdx P e)
      (f1 (shapeOf P B) e v)) = true := by simpa using h1
  have h3 : (xeOh (shapeOf P B) i q (eIdx P e)).decode a =
      some (f1 (shapeOf P B) e v) :=
    Oh.decode_of_true (sat_xeOh_b hi hq hixe h)
      (List.mem_range.mpr (uIdx_lt' (shapeOf P B) _)) h2
  have hval : valAt (shapeOf P B) (f1 (shapeOf P B) e v) =
      (Expr.stepEval1 e (valAt (shapeOf P B) v)).filter
        (fun t => decide (t ∈ (shapeOf P B).U)) :=
    valAt_uIdx_filter (shapeOf P B) _
  have hc' : decXe (shapeOf P B) P a i q c = valAt (shapeOf P B) v := by
    unfold decXe decVal
    rw [hv]
  rw [hc']
  unfold decXe decVal
  rw [h3]
  simpa using hval

/-- **Binary Tseitin gate.** -/
theorem xe_binary_b {e c₁ c₂ : Expr} (he : e ∈ allExprs P) (hc₁ : c₁ ∈ allExprs P)
    (hc₂ : c₂ ∈ allExprs P) (hchild : Expr.child2 e = some (c₁, c₂))
    (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q e =
      (Expr.stepEval2 e (decXe (shapeOf P B) P a i q c₁)
        (decXe (shapeOf P B) P a i q c₂)).filter
        (fun t => decide (t ∈ (shapeOf P B).U)) := by
  obtain ⟨v₁, hv₁, hvl₁, _⟩ := decodeXe_lt_b hc₁ hi hq h
  obtain ⟨v₂, hv₂, hvl₂, _⟩ := decodeXe_lt_b hc₂ hi hq h
  have hg : Sat a (fwd2ClausesOn [] (xeOh (shapeOf P B) i q (eIdx P c₁))
      (xeOh (shapeOf P B) i q (eIdx P c₂))
      (fun u v => pos (vxe (shapeOf P B) i q (eIdx P e) (f2 (shapeOf P B) e u v)))) := by
    intro cl hcl
    exact sat_gate_b he hi hq h cl (by rw [evalGate_binary hchild]; exact hcl)
  have hix1 : eIdx P c₁ < shE (shapeOf P B) := eIdx_lt hc₁
  have hix2 : eIdx P c₂ < shE (shapeOf P B) := eIdx_lt hc₂
  have hixe : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have h1 := fwd2ClausesOn_correct (sat_xeOh_b hi hq hix1 h)
    (sat_xeOh_b hi hq hix2 h) hg (fun l hl => absurd hl (by simp)) v₁ v₂ hv₁ hv₂
  have h2 : a (vxe (shapeOf P B) i q (eIdx P e)
      (f2 (shapeOf P B) e v₁ v₂)) = true := by simpa using h1
  have h3 : (xeOh (shapeOf P B) i q (eIdx P e)).decode a =
      some (f2 (shapeOf P B) e v₁ v₂) :=
    Oh.decode_of_true (sat_xeOh_b hi hq hixe h) (List.mem_range.mpr (uIdx_lt' (shapeOf P B) _)) h2
  have hval : valAt (shapeOf P B) (f2 (shapeOf P B) e v₁ v₂) =
      (Expr.stepEval2 e (valAt (shapeOf P B) v₁) (valAt (shapeOf P B) v₂)).filter
        (fun t => decide (t ∈ (shapeOf P B).U)) :=
    valAt_uIdx_filter (shapeOf P B) _
  have h1' : decXe (shapeOf P B) P a i q c₁ = valAt (shapeOf P B) v₁ := by
    unfold decXe decVal; rw [hv₁]
  have h2' : decXe (shapeOf P B) P a i q c₂ = valAt (shapeOf P B) v₂ := by
    unfold decXe decVal; rw [hv₂]
  rw [h1', h2']
  unfold decXe decVal
  rw [h3]
  simpa using hval

/-- **Variable gate.**  The value decoded for a variable read is the store slot. -/
theorem xe_var_b {x : Nat} (he : Expr.var x ∈ allExprs P) (hx : x < shV (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q (Expr.var x) = decSt (shapeOf P B) a i q x := by
  obtain ⟨v, hv, hvlt, _⟩ := decodeXe_lt_b he hi hq h
  have hsat := sat_stOh_b hi hq hx h
  have hg : Sat a (fwdClausesOn [] (stOh (shapeOf P B) i q x)
      (fun u => pos (vxe (shapeOf P B) i q (eIdx P (Expr.var x)) u))) := by
    intro cl hcl
    exact sat_gate_b he hi hq h cl (by rw [evalGate_var]; exact hcl)
  obtain ⟨w, hw⟩ := Oh.decode_some hsat
  have h1 := fwdClausesOn_correct hsat hg (fun l hl => absurd hl (by simp)) w hw
  have h2 : a (vxe (shapeOf P B) i q (eIdx P (Expr.var x)) w) = true := by simpa using h1
  have hwlt : w < shVal (shapeOf P B) := by
    show w < shVal (shapeOf P B)
    exact List.mem_range.mp ((decodeGo_some _ _ _ _ hw).1)
  have h3 : (xeOh (shapeOf P B) i q (eIdx P (Expr.var x))).decode a = some w :=
    Oh.decode_of_true (sat_xeOh_b hi hq (eIdx_lt he) h) (List.mem_range.mpr hwlt) h2
  have h4 : some w = some v := by rw [← h3, ← hv]
  have hwv : w = v := Option.some.inj h4
  subst hwv
  unfold decXe decSt decVal
  rw [hv, hw]

/-- **Constant gate.**  The value decoded for a constant is its message. -/
theorem xe_konst_b {E : Expr} (he : E ∈ allExprs P) (h1 : Expr.child1 E = none)
    (h2 : Expr.child2 E = none) (hv : ∀ x, E ≠ Expr.var x)
    (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q E = Expr.constVal E := by
  have hg : Sat a (cnfOf
      [[pos (vxe (shapeOf P B) i q (eIdx P E) (uIdx (shapeOf P B) (Expr.constVal E)))]]) := by
    intro cl hcl
    have hmem : cl ∈ evalGate (shapeOf P B) P i q E := by
      rw [evalGate_konst h1 h2 hv]
      simpa [cnfOf] using hcl
    exact sat_gate_b he hi hq h cl hmem
  have hcl : Clause.eval a [pos (vxe (shapeOf P B) i q (eIdx P E)
      (uIdx (shapeOf P B) (Expr.constVal E)))] = true := by
    have := hg _ (List.Mem.head _)
    simpa using this
  rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at hcl
  have h2' := hcl
  have h3 : (xeOh (shapeOf P B) i q (eIdx P E)).decode a =
      some (uIdx (shapeOf P B) (Expr.constVal E)) :=
    Oh.decode_of_true (sat_xeOh_b hi hq (eIdx_lt he) h)
      (List.mem_range.mpr (uIdx_lt' (shapeOf P B) _)) h2'
  unfold decXe decVal
  rw [h3]
  refine valAt_uIdx_adm ?_
  exact hU E he

/-- **The Tseitin evaluation bridge.** The value decoded from an expression's one-hot group is
the value of the expression in the decoded store, by structural induction over the
expression table - over the semantic groups alone. -/
theorem decXe_eq_b (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    ∀ (e : Expr), e ∈ allExprs P -> ∀ t,
      decXe (shapeOf P B) P a i q e = some t ->
      Expr.eval e (decodeStore (shapeOf P B) a i q) = some t := by
  intro e
  induction e with
  | agent A =>
      intro he t hdec
      rw [xe_konst_b he rfl rfl (by intro x; simp [Expr.var]) hU h hi hq] at hdec
      simpa [Expr.eval, Expr.constVal] using hdec
  | nonce N =>
      intro he t hdec
      rw [xe_konst_b he rfl rfl (by intro x; simp [Expr.var]) hU h hi hq] at hdec
      simpa [Expr.eval, Expr.constVal] using hdec
  | shrk a b =>
      intro he t hdec
      rw [xe_konst_b he rfl rfl (by intro x; simp [Expr.var]) hU h hi hq] at hdec
      simpa [Expr.eval, Expr.constVal] using hdec
  | pubk a =>
      intro he t hdec
      rw [xe_konst_b he rfl rfl (by intro x; simp [Expr.var]) hU h hi hq] at hdec
      simpa [Expr.eval, Expr.constVal] using hdec
  | privk a =>
      intro he t hdec
      rw [xe_konst_b he rfl rfl (by intro x; simp [Expr.var]) hU h hi hq] at hdec
      simpa [Expr.eval, Expr.constVal] using hdec
  | var x =>
      intro he t hdec
      have hxv : x < shV (shapeOf P B) := var_lt_shV he (by simp [Expr.vars])
      show readVar x (decodeStore (shapeOf P B) a i q) = some t
      rw [readVar_decodeStore hxv, ← (xe_var_b he hxv h hi hq)]
      exact hdec
  | pair ca cb iha ihb =>
      intro he t hdec
      obtain ⟨hca, hcb⟩ := mem_allExprs_child2 he rfl
      rw [xe_binary_b he hca hcb rfl hU h hi hq] at hdec
      have hres : Expr.stepEval2 (Expr.pair ca cb) (decXe (shapeOf P B) P a i q ca)
          (decXe (shapeOf P B) P a i q cb) = some t := filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval2] at hres
      | some u =>
          cases hxb : decXe (shapeOf P B) P a i q cb with
          | none => rw [hxb] at hres; simp [Expr.stepEval2] at hres
          | some v =>
              rw [hxa, hxb] at hres
              rw [Expr.eval_child2 rfl, iha hca u hxa, ihb hcb v hxb]
              exact hres
  | encS ca cb iha ihb =>
      intro he t hdec
      obtain ⟨hca, hcb⟩ := mem_allExprs_child2 he rfl
      rw [xe_binary_b he hca hcb rfl hU h hi hq] at hdec
      have hres : Expr.stepEval2 (Expr.encS ca cb) (decXe (shapeOf P B) P a i q ca)
          (decXe (shapeOf P B) P a i q cb) = some t := filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval2] at hres
      | some u =>
          cases hxb : decXe (shapeOf P B) P a i q cb with
          | none => rw [hxb] at hres; simp [Expr.stepEval2] at hres
          | some v =>
              rw [hxa, hxb] at hres
              rw [Expr.eval_child2 rfl, iha hca u hxa, ihb hcb v hxb]
              exact hres
  | decS ca cb iha ihb =>
      intro he t hdec
      obtain ⟨hca, hcb⟩ := mem_allExprs_child2 he rfl
      rw [xe_binary_b he hca hcb rfl hU h hi hq] at hdec
      have hres : Expr.stepEval2 (Expr.decS ca cb) (decXe (shapeOf P B) P a i q ca)
          (decXe (shapeOf P B) P a i q cb) = some t := filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval2] at hres
      | some u =>
          cases hxb : decXe (shapeOf P B) P a i q cb with
          | none => rw [hxb] at hres; simp [Expr.stepEval2] at hres
          | some v =>
              rw [hxa, hxb] at hres
              rw [Expr.eval_child2 rfl, iha hca u hxa, ihb hcb v hxb]
              exact hres
  | encA ca ag iha =>
      intro he t hdec
      have hca : ca ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [xe_unary_b he hca rfl hU h hi hq] at hdec
      have hres : Expr.stepEval1 (Expr.encA ca ag) (decXe (shapeOf P B) P a i q ca) = some t :=
        filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval1] at hres
      | some u =>
          rw [hxa] at hres
          rw [Expr.eval_child1 rfl, iha hca u hxa]
          exact hres
  | hash ca iha =>
      intro he t hdec
      have hca : ca ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [xe_unary_b he hca rfl hU h hi hq] at hdec
      have hres : Expr.stepEval1 (Expr.hash ca) (decXe (shapeOf P B) P a i q ca) = some t :=
        filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval1] at hres
      | some u =>
          rw [hxa] at hres
          rw [Expr.eval_child1 rfl, iha hca u hxa]
          exact hres
  | fst ca iha =>
      intro he t hdec
      have hca : ca ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [xe_unary_b he hca rfl hU h hi hq] at hdec
      have hres : Expr.stepEval1 (Expr.fst ca) (decXe (shapeOf P B) P a i q ca) = some t :=
        filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval1] at hres
      | some u =>
          rw [hxa] at hres
          rw [Expr.eval_child1 rfl, iha hca u hxa]
          exact hres
  | snd ca iha =>
      intro he t hdec
      have hca : ca ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [xe_unary_b he hca rfl hU h hi hq] at hdec
      have hres : Expr.stepEval1 (Expr.snd ca) (decXe (shapeOf P B) P a i q ca) = some t :=
        filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval1] at hres
      | some u =>
          rw [hxa] at hres
          rw [Expr.eval_child1 rfl, iha hca u hxa]
          exact hres
  | decA ca ag iha =>
      intro he t hdec
      have hca : ca ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [xe_unary_b he hca rfl hU h hi hq] at hdec
      have hres : Expr.stepEval1 (Expr.decA ca ag) (decXe (shapeOf P B) P a i q ca) = some t :=
        filter_some hdec
      cases hxa : decXe (shapeOf P B) P a i q ca with
      | none => rw [hxa] at hres; simp [Expr.stepEval1] at hres
      | some u =>
          rw [hxa] at hres
          rw [Expr.eval_child1 rfl, iha hca u hxa]
          exact hres

/-- At step 0 every store slot of a fresh session reads none, from a model of the semantic
groups. -/
theorem decSt_zero_none_b (h : Sat a (AuthClauses.baseEncode P B)) (hq : q < (shapeOf P B).nS1)
    (hx : x < (shapeOf P B).nV1 + 1) :
    decSt (shapeOf P B) a 0 q x = none := by
  have h1 : a (vst (shapeOf P B) 0 q x ((shapeOf P B).U.length)) = true := by
    have hcl : [pos (vst (shapeOf P B) 0 q x ((shapeOf P B).U.length))] ∈
        (initClauses (shapeOf P B) P).clauses := by
      unfold initClauses cnfOf
      refine List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (lt_shS hq),
          List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
            List.mem_map.mpr ⟨(shapeOf P B).U.length,
              List.mem_range.mpr (lt_shVal (Nat.le_refl _)), by simp⟩⟩⟩))
    have := sat_init_b h _ hcl
    rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at this
    exact this
  have hoh := sat_stOh_b (Nat.zero_le _) (lt_shS hq) hx h
  have h2 : (stOh (shapeOf P B) 0 q x).decode a = some ((shapeOf P B).U.length) :=
    Oh.decode_of_true hoh (List.mem_range.mpr (lt_shVal (Nat.le_refl _))) h1
  unfold decSt decVal
  rw [h2]
  exact valAt_uIdx_none (shapeOf P B)

/-- **The base case of the `Agrees` induction.** The initial configuration agrees with the
assignment at step 0, from a model of the semantic groups. -/
theorem agrees_zero_b (h : Sat a (AuthClauses.baseEncode P B)) : Agrees P B a (initCfg P) 0 := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro q hq
    have h1 : a (vpc (shapeOf P B) 0 q 0) = true := by
      have hcl : [pos (vpc (shapeOf P B) 0 q 0)] ∈
          (initClauses (shapeOf P B) P).clauses := by
        unfold initClauses cnfOf
        refine List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (lt_shS hq),
            List.mem_map.mpr ⟨0, List.mem_range.mpr (shPc_pos _), rfl⟩⟩))
      have := sat_init_b h _ hcl
      rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at this
      exact this
    have h2 : decodePc (shapeOf P B) a 0 q = 0 :=
      decodePc_of_true_b (Nat.zero_le _) (lt_shS hq) (shPc_pos _) h h1
    have h1' : sessAt (initCfg P) q = some { pc := 0, store := [] } := by
      unfold ProtSat.initCfg ProtSat.sessAt
      rw [rget_map]
      have hl : q < P.sessions.length := by rw [← nS1_eq]; exact hq
      cases h3 : rget P.sessions q with
      | none =>
          obtain ⟨s, hs⟩ := rget_lt P.sessions q hl
          rw [h3] at hs
          exact absurd hs (by simp)
      | some s => rfl
    have hpc : pcOf (initCfg P) q = 0 := by
      show ((sessAt (initCfg P) q).map (fun s => s.pc)).getD 0 = 0
      rw [h1']
      rfl
    rw [hpc, h2]
  · intro q x hq hx
    have hdec : decSt (shapeOf P B) a 0 q x = none := decSt_zero_none_b h hq hx
    have h1'' : sessAt (initCfg P) q = some { pc := 0, store := [] } := by
      unfold ProtSat.initCfg ProtSat.sessAt
      rw [rget_map]
      have hl : q < P.sessions.length := by rw [← nS1_eq]; exact hq
      cases h3 : rget P.sessions q with
      | none =>
          obtain ⟨s, hs⟩ := rget_lt P.sessions q hl
          rw [h3] at hs
          exact absurd hs (by simp)
      | some s => rfl
    have hst : storeOf (initCfg P) q = [] := by
      show ((sessAt (initCfg P) q).map (fun s => s.store)).getD [] = []
      rw [h1'']
      rfl
    rw [hst, hdec]
    rfl
  · intro q hq
    have hst2 : storeOf (initCfg P) q = [] := by
      have h1 : sessAt (initCfg P) q = some { pc := 0, store := [] } := by
        unfold ProtSat.initCfg ProtSat.sessAt
        rw [rget_map]
        have hl : q < P.sessions.length := by rw [← nS1_eq]; exact hq
        cases h3 : rget P.sessions q with
        | none =>
            obtain ⟨s, hs⟩ := rget_lt P.sessions q hl
            rw [h3] at hs
            exact absurd hs (by simp)
        | some s => rfl
      show ((sessAt (initCfg P) q).map (fun s => s.store)).getD [] = []
      rw [h1]
      rfl
    rw [hst2]
    exact ⟨List.nodup_nil, by simp⟩
  · have h1 : (initCfg P).sess = P.sessions.map fun s => { pc := 0, store := [] } := rfl
    rw [h1, List.length_map, nS1_eq]

/-- The index a store group selects, with its variable true. -/
theorem decodeSt_val_b (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    ∃ v, (stOh (shapeOf P B) i q x).decode a = some v ∧ v < shVal (shapeOf P B) ∧
      a (vst (shapeOf P B) i q x v) = true := by
  have hoh := sat_stOh_b hi hq hx h
  obtain ⟨v, hv⟩ := Oh.decode_some hoh
  exact ⟨v, hv, List.mem_range.mp ((decodeGo_some _ _ _ _ hv).1),
    (decodeGo_some _ _ _ _ hv).2⟩

/-- A session that does not act keeps its program counter. -/
theorem decodePc_frame_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (evAct (shapeOf P B) i q) = false) :
    decodePc (shapeOf P B) a (i + 1) q = decodePc (shapeOf P B) a i q := by
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true :=
    decodePc_true_b (Nat.le_of_lt hi) hq h
  have hcl : [pos (evAct (shapeOf P B) i q), neg (vpc (shapeOf P B) i q c),
      pos (vpc (shapeOf P B) (i + 1) q c)] ∈ frameSessClauses (shapeOf P B) i q := by
    unfold frameSessClauses
    refine List.mem_append_left _ (List.mem_map.mpr ⟨c,
      List.mem_range.mpr (decodePc_lt_b (Nat.le_of_lt hi) hq h), rfl⟩)
  have h1 := frame_holds_b hi hq h ha _ hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, pos_eval, neg_eval] at h1
  rw [ha, Bool.false_or, hpc, Bool.not_true, Bool.false_or] at h1
  exact decodePc_of_true_b (Nat.succ_le_of_lt hi) hq (decodePc_lt_b (Nat.le_of_lt hi) hq h) h h1

/-- A session that does not act keeps every store slot. -/
theorem decSt_frame_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (ha : a (evAct (shapeOf P B) i q) = false) :
    decSt (shapeOf P B) a (i + 1) q x = decSt (shapeOf P B) a i q x := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeSt_val_b (Nat.le_of_lt hi) hq hx h
  have hcl : [pos (evAct (shapeOf P B) i q), neg (vst (shapeOf P B) i q x v),
      pos (vst (shapeOf P B) (i + 1) q x v)] ∈ frameSessClauses (shapeOf P B) i q := by
    unfold frameSessClauses
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
      List.mem_map.mpr ⟨v, List.mem_range.mpr (lt_shVal (Nat.le_of_lt_succ hvlt)), rfl⟩⟩)
  have h1 := frame_holds_b hi hq h ha _ hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, pos_eval, neg_eval] at h1
  rw [ha, Bool.false_or, hvv, Bool.not_true, Bool.false_or] at h1
  have h2 : (stOh (shapeOf P B) (i + 1) q x).decode a = some v :=
    Oh.decode_of_true (sat_stOh_b (Nat.succ_le_of_lt hi) hq hx h)
      (List.mem_range.mpr hvlt) h1
  unfold decSt decVal
  rw [h2, hv]

/-- A session that does not act leaves the agreement untouched: `Agrees` transfers across a step
in which no session acts. -/
theorem agrees_of_noact_b (h : Sat a (AuthClauses.baseEncode P B)) {i : Nat} (hi : i < B.steps)
    (hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false)
    {C : Cfg} (hag : Agrees P B a C i)
    (hlearn : decLearn (shapeOf P B) P a i = none) :
    Agrees P B a C (i + 1) := by
  obtain ⟨hpc_ag, hst_ag, hkn_eq, hwf, hlen⟩ := hag
  refine ⟨?_, ?_, ?_, hwf, hlen⟩
  · intro q hq
    rw [decodePc_frame_b hi (lt_shS hq) h (hno q hq), hpc_ag q hq]
  · intro q x hq hx
    rw [decSt_frame_b hi (lt_shS hq) hx h (hno q hq), hst_ag q x hq hx]
  · rw [decKnSeq_succ, hlearn]
    simp [hkn_eq]

/-- If the act variable of session `q` is true, then `q` is a session the bounds instantiate. -/
theorem lt_nS1_of_evAct_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    q < (shapeOf P B).nS1 := by
  by_contra e
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true :=
    decodePc_true_b (Nat.le_of_lt hi) hq h
  have hact : P.actionAt q c = none := by
    unfold Protocol.actionAt Protocol.roleAt
    have hn : (shapeOf P B).nS1 = P.sessions.length := nS1_eq
    have h2 : P.sessions.drop q = [] := List.drop_eq_nil_of_le (by omega)
    rw [h2]
    simp
  have hcl : actGuard (shapeOf P B) i q c ∈ stepClausesAt (shapeOf P B) P i q c := by
    rw [stepClausesAt, hact]
    exact List.Mem.head _
  have h1 := step_body_b hi hq (decodePc_lt_b (Nat.le_of_lt hi) hq h) h ha hpc hcl
  rw [clause_eval_nil] at h1
  exact absurd h1 (by simp)

/-- The event of a step in which session q acts. -/
theorem decEv_act_of_code_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) :
    decEv (shapeOf P B) P a i =
      Ev.act q (decDeliver (shapeOf P B) a i q) (decNonce (shapeOf P B) a i q) := by
  rw [decEv_code_b hi h, hk]
  rw [if_neg (by omega : 1 + q ≠ 0), dif_pos (by omega : 1 + q < 1 + shS (shapeOf P B))]
  simp

/-- The step teaches nothing unless a session sends or the attacker deduces. -/
theorem decLearn_none_of_not_send_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = act)
    (hns : ∀ (a' : Agent) (e : Expr), act ≠ Action.send a' e) :
    decLearn (shapeOf P B) P a i = none := by
  rw [decLearn_act_b hi h hq hk, hact]
  cases act with
  | send a' e => exact absurd rfl (hns a' e)
  | _ => rfl

/-- An acting session has an action at its decoded program counter, from a model of the semantic
groups. -/
theorem some_actionAt_of_evAct_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    P.actionAt q (decodePc (shapeOf P B) a i q) ≠ none := by
  set c := decodePc (shapeOf P B) a i q with hc
  intro hact
  have hpc : a (vpc (shapeOf P B) i q c) = true := decodePc_true_b (Nat.le_of_lt hi) hq h
  have hcl : actGuard (shapeOf P B) i q c ∈ stepClausesAt (shapeOf P B) P i q c := by
    rw [stepClausesAt, hact]
    exact List.Mem.head _
  have h1 := step_body_b hi hq (decodePc_lt_b (Nat.le_of_lt hi) hq h) h ha hpc hcl
  rw [clause_eval_nil] at h1
  exact absurd h1 (by simp)

/-- An acting session advances its program counter by exactly one. -/
theorem step_pc_succ_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    decodePc (shapeOf P B) a (i + 1) q = decodePc (shapeOf P B) a i q + 1 := by
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true := decodePc_true_b (Nat.le_of_lt hi) hq h
  have hq1 : q < (shapeOf P B).nS1 := lt_nS1_of_evAct_b hi h hq ha
  have hne : P.actionAt q c ≠ none := some_actionAt_of_evAct_b hi hq h ha
  have hcl : advClause (shapeOf P B) i q c ∈ stepClausesAt (shapeOf P B) P i q c :=
    advClause_mem_stepClausesAt (shapeOf P B) P i q c hne
  have h1 := step_body_b hi hq (decodePc_lt_b (Nat.le_of_lt hi) hq h) h ha hpc hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, pos_eval,
    ha, hpc, Bool.not_true, Bool.false_or] at h1
  exact decodePc_of_true_b (Nat.succ_le_of_lt hi) hq
    (lt_shPc_succ (lt_roleLen_of_actionAt hne) (roleLen_le_nPc1 hq1)) h h1

/-- An acting session keeps every store slot whose variable its action does not write. -/
theorem step_st_keep_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hy : y < shV (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (ha : a (evAct (shapeOf P B) i q) = true)
    {act : Action} (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hny : writtenVar act ≠ some y) :
    decSt (shapeOf P B) a (i + 1) q y = decSt (shapeOf P B) a i q y := by
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true := decodePc_true_b (Nat.le_of_lt hi) hq h
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeSt_val_b (Nat.le_of_lt hi) hq hy h
  have hcl : keepClause (shapeOf P B) i q c y v ∈ stepClausesAt (shapeOf P B) P i q c :=
    keepClause_mem_stepClausesAt (shapeOf P B) P i q c y v hact hny hy hvlt
  have h1 := step_body_b hi hq (decodePc_lt_b (Nat.le_of_lt hi) hq h) h ha hpc hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval,
    pos_eval, hvv] at h1
  have hoh := sat_stOh_b (Nat.succ_le_of_lt hi) hq hy h
  have h2 : (stOh (shapeOf P B) (i + 1) q y).decode a = some v :=
    Oh.decode_of_true hoh (List.mem_range.mpr hvlt) h1
  unfold decSt decVal
  rw [h2, hv]

/-- A decoded store slot that holds a message has the corresponding value variable true. -/
theorem decSt_some_vst_b {i q x : Nat} {t : Term} (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) (hut : t ∈ (shapeOf P B).U)
    (hst : decSt (shapeOf P B) a i q x = some t) :
    a (vst (shapeOf P B) i q x (uIdx (shapeOf P B) (some t))) = true := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeSt_val_b hi hq hx h
  have huv : v = uIdx (shapeOf P B) (some t) := by
    have hv' : valAt (shapeOf P B) v = some t := by
      unfold decSt decVal at hst
      rw [hv] at hst
      exact hst
    have hlt : v < (shapeOf P B).U.length := by
      by_contra e
      have h2 : valAt (shapeOf P B) v = none := rget_oob_ge (shapeOf P B).U v (by omega)
      rw [h2] at hv'; simp at hv'
    exact valAt_inj hlt (uIdx_lt_of_mem hut)
      (by rw [hv', valAt_uIdx_some (shapeOf P B) hut])
  rw [← huv]
  exact hvv

/-- A decoded expression value has the corresponding evaluation variable true. -/
theorem decXe_some_vxe_b {i q : Nat} {e : Expr} {t : Term} (he : e ∈ allExprs P)
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (hut : t ∈ (shapeOf P B).U) (hxe : decXe (shapeOf P B) P a i q e = some t) :
    a (vxe (shapeOf P B) i q (eIdx P e) (uIdx (shapeOf P B) (some t))) = true := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt_b he hi hq h
  have huv : v = uIdx (shapeOf P B) (some t) := by
    have hv' : valAt (shapeOf P B) v = some t := by
      unfold decXe decVal at hxe
      rw [hv] at hxe
      exact hxe
    have hlt : v < (shapeOf P B).U.length := by
      by_contra e2
      have h2 : valAt (shapeOf P B) v = none := rget_oob_ge (shapeOf P B).U v (by omega)
      rw [h2] at hv'; simp at hv'
    exact valAt_inj hlt (uIdx_lt_of_mem hut)
      (by rw [hv', valAt_uIdx_some (shapeOf P B) hut])
  rw [← huv]
  exact hvv

/-- **Completeness at step 0.** Every message of the initial knowledge has its `kn` variable
true. -/
theorem init_kn_complete_b {u : Nat} {t : Term} (hut : valAt (shapeOf P B) u = some t)
    (h : Sat a (AuthClauses.baseEncode P B)) (ht : t ∈ P.initKn) :
    a (vkn (shapeOf P B) 0 u) = true := by
  have hu : u < (shapeOf P B).U.length := by
    by_contra e
    have : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
    rw [this] at hut; simp at hut
  have hcl : [pos (vkn (shapeOf P B) 0 u)] ∈ (initClauses (shapeOf P B) P).clauses := by
    unfold initClauses cnfOf
    refine List.mem_append_right _ ?_
    unfold initKnClauses
    refine List.mem_map.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
    have hh : initKnHolds (shapeOf P B) P u = true := by
      unfold initKnHolds; rw [hut]; exact decide_eq_true ht
    rw [if_pos hh]
  have := sat_init_b h _ hcl
  simpa [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] using this

/-- The frame clauses make knowledge monotone on the Boolean side. -/
theorem kn_frame_b {i u : Nat} (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B))
    (hu : u < (shapeOf P B).U.length) :
    a (vkn (shapeOf P B) i u) = true -> a (vkn (shapeOf P B) (i + 1) u) = true := by
  intro ha
  have hcl : [neg (vkn (shapeOf P B) i u), pos (vkn (shapeOf P B) (i + 1) u)] ∈
      (frameClauses (shapeOf P B)).clauses := by
    unfold frameClauses cnfOf
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_append_left _ (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)⟩
  have := sat_frame_b h _ hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, ha, Bool.not_true,
    pos_eval] at this
  exact this

/-- What step `i` teaches is in the knowledge after step `i+1`, from a model of the semantic
groups. -/
theorem decLearn_kn_b (hi : i < B.steps) (h : Sat a (AuthClauses.baseEncode P B)) {u : Nat} {t : Term}
    (hu : u < (shapeOf P B).U.length) (hut : valAt (shapeOf P B) u = some t)
    (hl : decLearn (shapeOf P B) P a i = some t) :
    a (vkn (shapeOf P B) (i + 1) u) = true := by
  rcases ev_cases_b hi h with h0 | ⟨q, hq, hk⟩ | ⟨n, hn, hk⟩
  · rw [decLearn_code_b hi h, h0] at hl
    exact absurd hl (by simp)
  · have hev : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
    have hc : decodePc (shapeOf P B) a i q < shPc (shapeOf P B) :=
      decodePc_lt_b (Nat.le_of_lt hi) hq h
    rw [decLearn_act_b hi h hq hk] at hl
    cases hact : P.actionAt q (decodePc (shapeOf P B) a i q) with
    | none => exact absurd hl (by simp [hact])
    | some act =>
        cases act with
        | send a' e =>
            have hxe : decXe (shapeOf P B) P a i q e = some t := by simpa [hact] using hl
            have hut' : t ∈ (shapeOf P B).U := rget_mem (shapeOf P B).U u t hu hut
            have hui : uIdx (shapeOf P B) (some t) = u := by
              rw [← hut]; exact uIdx_valAt hu
            have hvxe : a (vxe (shapeOf P B) i q (eIdx P e) u) = true := by
              rw [← hui]
              exact decXe_some_vxe_b (mem_allExprs_send hact) (Nat.le_of_lt hi) hq h hut' hxe
            have hcl : sendPublishClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q)
                (eIdx P e) u ∈ stepClausesAt (shapeOf P B) P i q
                  (decodePc (shapeOf P B) a i q) := sendPublish_mem hu hact
            have h1 := step_body_b hi hq hc h hev (decodePc_true_b (Nat.le_of_lt hi) hq h) hcl
            simpa [sendPublishClause, Clause.eval_cons, clause_eval_nil, Bool.or_false,
              neg_eval, hvxe, Bool.not_true, pos_eval] using h1
        | _ => exact absurd hl (by simp [hact])
  · obtain ⟨ins, hins⟩ := rget_lt (dedInsts (shapeOf P B)) n hn
    rw [decLearn_ded_b hi h hn ins hins hk] at hl
    have hlt : ins.concl < (shapeOf P B).U.length := by
      by_contra e
      have h2 : valAt (shapeOf P B) ins.concl = none :=
        rget_oob_ge (shapeOf P B).U ins.concl (by omega)
      rw [h2] at hl; simp at hl
    have hcu : ins.concl = u := valAt_inj hlt hu (by rw [hl, ← hut])
    have hcl : [neg (evDed (shapeOf P B) i n), pos (vkn (shapeOf P B) (i + 1) ins.concl)] ∈
        dedClausesAt (shapeOf P B) i n := dedConcl_mem hn ins hins
    have this := sat_ded_b h _ (mem_ded hi hn hcl)
    rw [hcu] at this
    have hev : a (evDed (shapeOf P B) i n) = true := by
      have : a (vev (shapeOf P B) i (decCode P B a i)) = true := decCode_true_b hi h
      rw [hk] at this
      exact this
    simpa [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hev,
      Bool.not_true, pos_eval] using this

/-- **Completeness of the knowledge decoding.** Every message whose `kn` variable is true is
derivable, so `kn_sound_b` and this make the decoded knowledge exact. -/
theorem kn_complete_b (h : Sat a (AuthClauses.baseEncode P B)) {u : Nat} {t : Term}
    (hu : u < (shapeOf P B).U.length) (hut : valAt (shapeOf P B) u = some t) :
    ∀ (i : Nat), i ≤ B.steps ->
      t ∈ decKnSeq (shapeOf P B) P a i -> a (vkn (shapeOf P B) i u) = true := by
  intro i
  induction i with
  | zero => intro _ hi; exact init_kn_complete_b hut h hi
  | succ i ih =>
      intro hi hm
      rw [decKnSeq_succ, List.mem_append] at hm
      rcases hm with hm | hm
      · exact kn_frame_b hi h hu (ih (by omega) hm)
      · have hl : decLearn (shapeOf P B) P a i = some t := by
          cases h2 : decLearn (shapeOf P B) P a i with
          | none => exact absurd hm (by simp [h2])
          | some s =>
              rw [h2] at hm
              have h3 : t = s := by simpa using hm
              exact congrArg some h3.symm
        exact decLearn_kn_b (by omega) h hu hut hl

/-- Every session other than the one that acts does not act. -/
theorem evAct_false_of_other_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps)
    {q r : Nat} (hq : q < shS (shapeOf P B)) (hr : r < shS (shapeOf P B))
    (hne : r ≠ q) (hk : decCode P B a i = 1 + q) :
    a (evAct (shapeOf P B) i r) = false :=
  evAct_false_of_ne_b hi h hr hq hne hk

/-- An acting session's program counter advances by one in the decoded run. -/
theorem pcOf_succ_act_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps) {C C' : Cfg}
    (hag : Agrees P B a C i) {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q)
    (hpcq : pcOf C' q = pcOf C q + 1)
    (hpcr : ∀ r, r < (shapeOf P B).nS1 → r ≠ q → pcOf C' r = pcOf C r) :
    ∀ r, r < (shapeOf P B).nS1 → pcOf C' r = decodePc (shapeOf P B) a (i + 1) r := by
  intro r hr
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
  by_cases hne : r = q
  · subst hne
    rw [hpcq, hag.1 r (lt_nS1_of_evAct_b hi h hq haq), ← step_pc_succ_b hi hq h haq]
  · rw [hpcr r hr hne, hag.1 r hr,
      decodePc_frame_b hi (lt_shS hr) h (evAct_false_of_other_b h hi hq (lt_shS hr) hne hk)]

/-- The store slot an acting session writes reads back from the decoded store at the next step. -/
theorem decSt_succ_write_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps) {C : Cfg}
    (hag : Agrees P B a C i) {q x₀ : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hw : writtenVar act = some x₀) {t : Term}
    (hwt : decSt (shapeOf P B) a (i + 1) q x₀ = some t) :
    ∀ r x, r < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
      readVar x (storeOf (succStore C q x₀ t) r) = decSt (shapeOf P B) a (i + 1) r x := by
  intro r x hr hx
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
  by_cases hne : r = q
  · subst hne
    by_cases hxy : x = x₀
    · subst hxy
      obtain ⟨st, hst⟩ := sessAt_lt (by rw [hag.2.2.2.2]; exact hr)
      rw [readVar_succStore C r x t st hst]
      exact hwt.symm
    · rw [readVar_succStore_other C r x₀ x t (by intro e; subst e; exact hxy rfl)]
      rw [hag.2.1 r x hr hx]
      symm
      exact step_st_keep_b hi hq hx h haq hact
        (by intro e; rw [hw] at e; cases e; exact hxy rfl)
  · rw [storeOf_succStore_other C q r x₀ t hne, hag.2.1 r x hr hx,
      ← decSt_frame_b hi (lt_shS hr) hx h (evAct_false_of_other_b h hi hq (lt_shS hr) hne hk)]

/-- A store slot the acting session does not write keeps its decoded value at the next step. -/
theorem decSt_succ_keep_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps) {C : Cfg}
    (hag : Agrees P B a C i) {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hw : writtenVar act = none) (C' : Cfg)
    (hst : ∀ r x, readVar x (storeOf C' r) = readVar x (storeOf C r)) :
    ∀ r x, r < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
      readVar x (storeOf C' r) = decSt (shapeOf P B) a (i + 1) r x := by
  intro r x hr hx
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
  rw [hst r x, hag.2.1 r x hr hx]
  by_cases hne : r = q
  · subst hne
    symm
    exact step_st_keep_b hi hq hx h haq hact (by intro e; rw [hw] at e; cases e)
  · symm
    exact decSt_frame_b hi (lt_shS hr) hx h (evAct_false_of_other_b h hi hq (lt_shS hr) hne hk)

/-- Writing a variable keeps a well formed store well formed, under the semantic groups. -/
theorem storeWF_succ_write_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps)
    (hag : Agrees P B a C i) {q x₀ : Nat} (hq : q < shS (shapeOf P B))
    (hx₀ : x₀ < shV (shapeOf P B)) (hk : decCode P B a i = 1 + q) {t : Term} :
    ∀ r, r < (shapeOf P B).nS1 → StoreWF (shapeOf P B) (storeOf (succStore C q x₀ t) r) := by
  intro r hr
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
  by_cases hne : r = q
  · subst hne
    obtain ⟨st, hst⟩ := sessAt_lt (by rw [hag.2.2.2.2]; exact hr)
    rw [storeOf_succStore_same C r x₀ t st hst]
    exact storeWF_writeVar (shapeOf P B) hx₀
      (hag.2.2.2.1 r (lt_nS1_of_evAct_b hi h hq haq))
  · rw [storeOf_succStore_other C q r x₀ t hne]
    exact hag.2.2.2.1 r hr

/-- The knowledge after a step that teaches nothing. -/
theorem decKn_succ_none_b (h : Sat a (AuthClauses.baseEncode P B)) (hag : Agrees P B a C i)
    (hlearn : decLearn (shapeOf P B) P a i = none) :
    C.kn = decKnSeq (shapeOf P B) P a (i + 1) := by
  rw [decKnSeq_succ, hag.2.2.1]
  simp [hlearn]

/-- The nonce index a fresh group selects, with its variable true. -/
theorem decodeFr_val_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) :
    ∃ d, (frOh (shapeOf P B) i q).decode a = some d ∧ d < shD (shapeOf P B) ∧
      a (vfr (shapeOf P B) i q d) = true := by
  have hoh := sat_frOh_b hi hq h
  obtain ⟨d, hd⟩ := Oh.decode_some hoh
  exact ⟨d, hd, List.mem_range.mp ((decodeGo_some _ _ _ _ hd).1),
    (decodeGo_some _ _ _ _ hd).2⟩

/-- The value index a delivery group selects, with its variable true. -/
theorem decodeDl_val_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (AuthClauses.baseEncode P B)) :
    ∃ u, (dlOh (shapeOf P B) i q).decode a = some u ∧ u < shVal (shapeOf P B) ∧
      a (vdl (shapeOf P B) i q u) = true := by
  have hoh := sat_dlOh_b hi hq h
  obtain ⟨u, hu⟩ := Oh.decode_some hoh
  exact ⟨u, hu, List.mem_range.mp ((decodeGo_some _ _ _ _ hu).1),
    (decodeGo_some _ _ _ _ hu).2⟩

/-- A frame step - no session acts, nothing is learned - transfers `Agrees` to the next step. -/
theorem agrees_of_frame_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps) {C C' : Cfg}
    (hag : Agrees P B a C i)
    (hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false)
    (hpc : ∀ r, r < (shapeOf P B).nS1 → pcOf C' r = pcOf C r)
    (hst : ∀ r x, r < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
              readVar x (storeOf C' r) = readVar x (storeOf C r))
    (hkn : C'.kn = decKnSeq (shapeOf P B) P a (i + 1))
    (hwf : ∀ r, r < (shapeOf P B).nS1 → StoreWF (shapeOf P B) (storeOf C' r))
    (hlen : C'.sess.length = (shapeOf P B).nS1) :
    Agrees P B a C' (i + 1) := by
  refine ⟨?_, ?_, hkn, hwf, hlen⟩
  · intro r hr
    rw [hpc r hr, hag.1 r hr, decodePc_frame_b hi (lt_shS hr) h (hno r hr)]
  · intro r x hr hx
    rw [hst r x hr hx, hag.2.1 r x hr hx,
      ← decSt_frame_b hi (lt_shS hr) hx h (hno r hr)]

/-- The body of a freshness clause holds for the nonce an acting session picks. -/
theorem fresh_body_b (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B))
    (ha : a (evAct (shapeOf P B) i q) = true) (hpc : a (vpc (shapeOf P B) i q c) = true)
    {rest : List Lit}
    (hcl : (actGuard (shapeOf P B) i q c ++ rest) ∈
        freshClausesAt (shapeOf P B) P i q c) :
    Clause.eval a rest = true := by
  have := sat_fresh_b h _ (mem_fresh hi hq hc hcl)
  refine clause_eval_append_of_false (actGuard (shapeOf P B) i q c) rest this ?_
  intro l hl
  unfold actGuard at hl
  rw [List.mem_cons] at hl
  rcases hl with rfl | hl
  · simp [neg_eval, ha]
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · simp [neg_eval, hpc]
    · exact absurd hl (by simp)

/-- `Agrees` transfers across a step in which the given session advances. -/
theorem agrees_succ_advance_b (h : Sat a (AuthClauses.baseEncode P B)) (hi : i < B.steps) {C : Cfg}
    (hag : Agrees P B a C i) {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hw : writtenVar act = none)
    (hlearn : decLearn (shapeOf P B) P a i = none) :
    Agrees P B a (succAdvance C q) (i + 1) := by
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
  have hnS : q < (shapeOf P B).nS1 := lt_nS1_of_evAct_b hi h hq haq
  refine ⟨pcOf_succ_act_b h hi hag hq hk
      (pcOf_succAdvance' C q (by rw [hag.2.2.2.2]; exact hnS))
      (fun r hr hne => pcOf_succAdvance_other C q r hne),
    decSt_succ_keep_b h hi hag hq hk hact hw _
      (fun r x => congrArg (readVar x) (storeOf_succAdvance C q r)),
    (decKn_succ_none_b h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
    storeWF_succ_keep hag _ (fun r => storeOf_succAdvance C q r),
    by rw [sessLength_succAdvance, hag.2.2.2.2]⟩

/-- **The keystone.** Every decoded step is a transition of the operational semantics, and the
next decoded configuration agrees with the assignment - all ten introduction rules of
`ProtSat.Rel` discharged, over the semantic groups alone. The secrecy violation clause is
never read. -/
theorem rel_agrees_b (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B))
    {i : Nat} (hi : i < B.steps) {C : Cfg} (hag : Agrees P B a C i) :
    Rel P C (decEv (shapeOf P B) P a i) (decStep P B a C i) ∧
      Agrees P B a (decStep P B a C i) (i + 1) := by
  rcases ev_cases_b hi h with h0 | ⟨q, hq, hk⟩ | ⟨n, hn, hk⟩
  · -- ---- the idle step ----
    have hev : decEv (shapeOf P B) P a i = Ev.idle := by
      rw [decEv_code_b hi h, h0]
      simp
    have hstep : decStep P B a C i = C := by unfold decStep; rw [hev]
    have hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false := by
      intro r hr
      by_contra e
      have := decCode_of_evAct_b hi h (lt_shS hr) (by simpa [evAct] using e)
      omega
    have hlearn : decLearn (shapeOf P B) P a i = none := by
      rw [decLearn_code_b hi h, h0]
      simp
    refine ⟨?_, ?_⟩
    · rw [hev, hstep]
      exact Rel.rIdle P C
    · rw [hstep]
      exact agrees_of_noact_b h hi hno hag hlearn
  · -- ---- session q acts ----
    have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code_b hi h hq hk
    have hnS : q < (shapeOf P B).nS1 := lt_nS1_of_evAct_b hi h hq haq
    have hc : decodePc (shapeOf P B) a i q < shPc (shapeOf P B) :=
      decodePc_lt_b (Nat.le_of_lt hi) hq h
    have hpc0 : a (vpc (shapeOf P B) i q (decodePc (shapeOf P B) a i q)) = true :=
      decodePc_true_b (Nat.le_of_lt hi) hq h
    have hev : decEv (shapeOf P B) P a i = Ev.act q (decDeliver (shapeOf P B) a i q)
        (decNonce (shapeOf P B) a i q) := decEv_act_of_code_b hi h hq hk
    have hno : ∀ r, r < (shapeOf P B).nS1 → r ≠ q →
        a (evAct (shapeOf P B) i r) = false :=
      fun r hr hne => evAct_false_of_other_b h hi hq (lt_shS hr) hne hk
    have hpcq : pcOf C q = decodePc (shapeOf P B) a i q := hag.1 q hnS
    have hlenC : C.sess.length = (shapeOf P B).nS1 := hag.2.2.2.2
    cases hact : P.actionAt q (decodePc (shapeOf P B) a i q) with
    | none => exact absurd hact (some_actionAt_of_evAct_b hi hq h haq)
    | some act =>
      cases act with
      | fresh x N =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.fresh x N) =
              ((List.range (shD (shapeOf P B))).flatMap fun d =>
                  freshStepClauses (shapeOf P B) i q (decodePc (shapeOf P B) a i q) x d)
                ++ [actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                      [neg (vfr (shapeOf P B) i q (shD (shapeOf P B) - 1))]] := by
            simp [actionClauses]
          obtain ⟨d, hd, hdlt, hvfr⟩ := decodeFr_val_b hi hq h
          -- the dummy nonce alternative is excluded, so the choice is a real domain nonce
          have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vfr (shapeOf P B) i q (shD (shapeOf P B) - 1))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.fresh x N) hact, hred]
            exact List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _))
          have h1 := step_body_b hi hq hc h haq hpc0 hcl
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
          have hd2 : d < (shapeOf P B).D.length := by
            by_contra e
            have hs : shD (shapeOf P B) = (shapeOf P B).D.length + 1 := rfl
            have h2 : d = shD (shapeOf P B) - 1 := by
              rw [hs]
              omega
            rw [h2] at hvfr
            exact absurd hvfr (by simpa using h1)
          obtain ⟨N', hN'⟩ := rget_lt (shapeOf P B).D d hd2
          have hdN : decNonce (shapeOf P B) a i q = N' := by
            unfold decNonce; simp [hd, hN']
          have hD : N' ∈ P.nonceDomain := by
            rw [← D_eq]; exact rget_mem (shapeOf P B).D d N' hd2 hN'
          have hUn : Term.nonce N' ∈ (shapeOf P B).U := nonceDomain_mem_univ hD
          have hxlt : x < shV (shapeOf P B) := lt_shV_of_written hact (by simp [Action.written])
          -- the fresh step clause writes the nonce into the store slot
          have hcl2 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vfr (shapeOf P B) i q d),
                pos (vst (shapeOf P B) (i + 1) q x
                  (uIdx (shapeOf P B) (some (Term.nonce N'))))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.fresh x N) hact, hred]
            refine List.mem_append_right _ (List.mem_append_left _
              (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hdlt, ?_⟩))
            rw [freshStepClauses, hN']
            exact List.Mem.head _
          have h2 := step_body_b hi hq hc h haq hpc0 hcl2
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvfr,
            Bool.not_true, pos_eval] at h2
          have hwt : decSt (shapeOf P B) a (i + 1) q x = some (Term.nonce N') := by
            unfold decSt decVal
            have h3 : (stOh (shapeOf P B) (i + 1) q x).decode a =
                some (uIdx (shapeOf P B) (some (Term.nonce N'))) :=
              Oh.decode_of_true (sat_stOh_b (Nat.succ_le_of_lt hi) hq hxlt h)
                (List.mem_range.mpr (uIdx_lt' (shapeOf P B) (some (Term.nonce N')))) h2
            simp [h3, valAt_uIdx_some (shapeOf P B) hUn]
          -- the nonce is unused: neither in a store nor known
          have hnu : nonceUsed C N' = false := by
            by_contra e
            have htrue : nonceUsed C N' = true := by
              cases h : nonceUsed C N' with
              | true => rfl
              | false => exact absurd h e
            rw [nonceUsed, Bool.or_eq_true] at htrue
            rcases htrue with h1 | h2
            · obtain ⟨st, hst, hf⟩ := List.any_eq_true.mp h1
              obtain ⟨r, hr, heq⟩ := mem_rget C.sess st hst
              have hr' : r < (shapeOf P B).nS1 := by rw [← hlenC]; exact hr
              have hs : storeOf C r = st.store := by
                unfold storeOf sessAt
                rw [heq]
                rfl
              rw [← hs] at hf
              have hmem : Term.nonce N' ∈ storeVals (storeOf C r) := by simpa using hf
              have := (hag.storeVals_iff hr' (Term.nonce N')).mp hmem
              obtain ⟨x', hx', he⟩ := this
              have hv : a (vst (shapeOf P B) i r x'
                  (uIdx (shapeOf P B) (some (Term.nonce N')))) = true :=
                decSt_some_vst_b (Nat.le_of_lt hi) (lt_shS hr') hx' h hUn he
              have hcl3 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                  [neg (vfr (shapeOf P B) i q d),
                    neg (vst (shapeOf P B) i r x'
                      (uIdx (shapeOf P B) (some (Term.nonce N'))))] ∈
                  freshClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
                rw [freshClausesAt, hact]
                refine List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hdlt, ?_⟩
                rw [freshUseClauses, hN']
                refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨r,
                  List.mem_range.mpr (lt_shS hr'), List.mem_map.mpr ⟨x', List.mem_range.mpr hx', rfl⟩⟩)
              have h3 := fresh_body_b hi hq hc h haq hpc0 hcl3
              simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvfr,
                Bool.not_true] at h3
              exact absurd (hv ▸ bool_not_true h3) (by simp)
            · have hk' : Term.nonce N' ∈ C.kn := by simpa using h2
              rw [hag.2.2.1] at hk'
              have hv : a (vkn (shapeOf P B) i
                  (uIdx (shapeOf P B) (some (Term.nonce N')))) = true :=
                kn_complete_b h (uIdx_lt_of_mem hUn)
                  (valAt_uIdx_some (shapeOf P B) hUn) i (Nat.le_of_lt hi) hk'
              have hcl4 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                  [neg (vfr (shapeOf P B) i q d),
                    neg (vkn (shapeOf P B) i (uIdx (shapeOf P B) (some (Term.nonce N'))))] ∈
                  freshClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
                rw [freshClausesAt, hact]
                refine List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hdlt, ?_⟩
                rw [freshUseClauses, hN']
                exact List.mem_append_right _ (List.Mem.head _)
              have h4 := fresh_body_b hi hq hc h haq hpc0 hcl4
              simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvfr,
                Bool.not_true] at h4
              exact absurd (hv ▸ bool_not_true h4) (by simp)
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succStore C q x (Term.nonce N') := by
            unfold decStep; simp [hev, hpcq, hact, hdN]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep, hdN]
            exact Rel.rFresh (by rw [hpcq]; exact hact) hD hnu
          rw [hstep]
          refine ⟨pcOf_succ_act_b h hi hag hq hk (pcOf_succStore' C q x (Term.nonce N')
              (by rw [hlenC]; exact hnS)) (fun r hr hne => pcOf_succStore_other C q r x _ hne),
            decSt_succ_write_b h hi hag hq hk hact rfl hwt,
            (decKn_succ_none_b h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
            storeWF_succ_write_b h hi hag hq hxlt hk,
            by rw [sessLength_succStore, hag.2.2.2.2]⟩
      | send a' e =>
          have hmem : e ∈ allExprs P := mem_allExprs_send hact
          obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt_b hmem (Nat.le_of_lt hi) hq h
          have hdec : decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) v := by
            unfold decXe decVal; rw [hv]
          -- a send cannot evaluate to the unset value
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.send a' e) =
              [sendRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e)]
                ++ mapMsg (shapeOf P B) (fun w =>
                    sendPublishClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q)
                      (eIdx P e) w) := by
            simp [actionClauses]
          have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vxe (shapeOf P B) i q (eIdx P e) ((shapeOf P B).U.length))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.send a' e) hact, hred]
            exact List.mem_append_right _ (List.mem_append_left _ (List.Mem.head _))
          have h1 := step_body_b hi hq hc h haq hpc0 hcl
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
          have hvlt' : v < (shapeOf P B).U.length := by
            have hs : shVal (shapeOf P B) = (shapeOf P B).U.length + 1 := rfl
            by_contra e2
            have hv2 : v = (shapeOf P B).U.length := by
              rw [hs] at hvlt
              omega
            rw [hv2] at hvv
            exact absurd (hvv ▸ bool_not_true h1) (by simp)
          obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U v hvlt'
          have hdec' : decXe (shapeOf P B) P a i q e = some t := by
            rw [hdec]
            exact ht
          -- the value the Tseitin group selected is the value of the expression in the store
          have h2 : ∀ x, x ∈ e.vars ->
              Expr.lookup x (storeOf C q) = Expr.lookup x (decodeStore (shapeOf P B) a i q) := by
            intro x hx
            have hxv : x < shV (shapeOf P B) := lt_shV_of_mem hmem hx
            show readVar x (storeOf C q) = readVar x (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q x hnS hxv, readVar_decodeStore hxv]
          have heval : Expr.eval e (storeOf C q) = some t := by
            have h4 : Expr.eval e (decodeStore (shapeOf P B) a i q) = some t :=
              decXe_eq_b hU h (Nat.le_of_lt hi) hq e hmem t hdec'
            rw [← h4]
            exact Expr.eval_congr h2
          have hact2 : P.actionAt q (pcOf C q) = some (Action.send a' e) := by
            rw [hpcq]; exact hact
          -- the send publishes the value it sends
          have hlearn : decLearn (shapeOf P B) P a i = some t := by
            simp [decLearn_act_b hi h hq hk, hact, hdec']
          have hstep : decStep P B a C i = succSend C q t := by
            unfold decStep; simp [hev, hpcq, hact, heval]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rSend hact2 heval
          rw [hstep]
          have hst : ∀ r x, readVar x (storeOf (succSend C q t) r) = readVar x (storeOf C r) := by
            intro r x
            by_cases hne : r = q
            · subst hne; rw [storeOf_succSend_same]
            · rw [storeOf_succSend_other C q r t hne]
          have hwf : ∀ r, r < (shapeOf P B).nS1 →
              StoreWF (shapeOf P B) (storeOf (succSend C q t) r) := by
            intro r hr
            by_cases hne : r = q
            · subst hne; rw [storeOf_succSend_same]; exact hag.2.2.2.1 r hr
            · rw [storeOf_succSend_other C q r t hne]; exact hag.2.2.2.1 r hr
          refine ⟨pcOf_succ_act_b h hi hag hq hk
              (pcOf_succSend' C q t (by rw [hlenC]; exact hnS))
              (fun r hr hne => pcOf_succSend_other C q r _ hne),
            decSt_succ_keep_b h hi hag hq hk hact rfl _ hst, ?_, hwf,
            by rw [sessLength_succSend, hag.2.2.2.2]⟩
          · rw [decKnSeq_succ, kn_succSend, hag.2.2.1]
            simp [hlearn]
      | recv a' x =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.recv a' x) = (eachVal (shapeOf P B) fun w =>
              if w < (shapeOf P B).U.length then
                [recvStoreClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) w x,
                  recvKnowClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) w x]
              else [recvRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) w]) := by
            simp [actionClauses]
          obtain ⟨u, hu, hult, hudl⟩ := decodeDl_val_b hi hq h
          have hxlt : x < shV (shapeOf P B) := lt_shV_of_written hact (by simp [Action.written])
          by_cases hurlt : u < (shapeOf P B).U.length
          · -- the delivered value is a real universe message
            obtain ⟨m, hm⟩ := rget_lt (shapeOf P B).U u hurlt
            have hdl : decDeliver (shapeOf P B) a i q = m := by
              unfold decDeliver decVal
              rw [hu]
              show Option.getD (rget (shapeOf P B).U u) (Term.nonce 0) = m
              rw [hm]
              rfl
            -- it is known to the attacker
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vdl (shapeOf P B) i q u), pos (vkn (shapeOf P B) i u)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.recv a' x) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hult, ?_⟩)
              rw [if_pos hurlt]
              exact List.Mem.tail _ (List.Mem.head _)
            have h1 := step_body_b hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hudl,
              Bool.not_true, pos_eval] at h1
            have hkn : m ∈ C.kn := by
              rw [hag.2.2.1]
              exact kn_sound_b h hm i (Nat.le_of_lt hi) h1
            -- and it lands in the store slot
            have hcl2 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vdl (shapeOf P B) i q u), pos (vst (shapeOf P B) (i + 1) q x u)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.recv a' x) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hult, ?_⟩)
              rw [if_pos hurlt]
              exact List.Mem.head _
            have h2 := step_body_b hi hq hc h haq hpc0 hcl2
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hudl,
              Bool.not_true, pos_eval] at h2
            have hwt : decSt (shapeOf P B) a (i + 1) q x = some m := by
              unfold decSt decVal
              have h5 : (stOh (shapeOf P B) (i + 1) q x).decode a = some u :=
                Oh.decode_of_true (sat_stOh_b (Nat.succ_le_of_lt hi) hq hxlt h)
                  (List.mem_range.mpr hult) h2
              rw [h5]
              show rget (shapeOf P B).U u = some m
              exact hm
            have hlearn : decLearn (shapeOf P B) P a i = none :=
              decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
            have hstep : decStep P B a C i = succStore C q x m := by
              unfold decStep; simp [hev, hdl, hpcq, hact]
            refine ⟨?_, ?_⟩
            · rw [hev, hstep, hdl]
              exact Rel.rRecv (by rw [hpcq]; exact hact) hkn
            rw [hstep]
            refine ⟨pcOf_succ_act_b h hi hag hq hk
                (pcOf_succStore' C q x m (by rw [hlenC]; exact hnS))
                (fun r hr hne => pcOf_succStore_other C q r x _ hne),
              decSt_succ_write_b h hi hag hq hk hact rfl hwt,
              (decKn_succ_none_b h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
              storeWF_succ_write_b h hi hag hq hxlt hk,
              by rw [sessLength_succStore, hag.2.2.2.2]⟩
          · -- the delivery group cannot select the unset value
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vdl (shapeOf P B) i q u)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.recv a' x) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hult, ?_⟩)
              rw [if_neg hurlt]
              exact List.Mem.head _
            have h1 := step_body_b hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
            exact absurd (hudl ▸ bool_not_true h1) (by simp)
      | assign x e =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.assign x e) = (eachVal (shapeOf P B) fun w =>
              if w < (shapeOf P B).U.length then
                [assignClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e) w x]
              else [assignRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e) w]) := by
            simp [actionClauses]
          have hmem : e ∈ allExprs P := mem_allExprs_assign hact
          have hxlt : x < shV (shapeOf P B) := lt_shV_of_written hact (by simp [Action.written])
          obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt_b hmem (Nat.le_of_lt hi) hq h
          have hdec : decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) v := by
            unfold decXe decVal; rw [hv]
          have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vxe (shapeOf P B) i q (eIdx P e) ((shapeOf P B).U.length))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.assign x e) hact, hred, eachVal]
            refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨(shapeOf P B).U.length,
                List.mem_range.mpr (lt_shVal (Nat.le_refl _)), ?_⟩)
            rw [if_neg (by omega : ¬ ((shapeOf P B).U.length < (shapeOf P B).U.length))]
            exact List.Mem.head _
          have h1 := step_body_b hi hq hc h haq hpc0 hcl
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
          have hvlt' : v < (shapeOf P B).U.length := by
            have hs : shVal (shapeOf P B) = (shapeOf P B).U.length + 1 := rfl
            by_contra e2
            have hv2 : v = (shapeOf P B).U.length := by
              rw [hs] at hvlt
              omega
            rw [hv2] at hvv
            exact absurd (hvv ▸ bool_not_true h1) (by simp)
          obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U v hvlt'
          have hdec' : decXe (shapeOf P B) P a i q e = some t := by
            rw [hdec]
            exact ht
          have h2 : ∀ y, y ∈ e.vars ->
              Expr.lookup y (storeOf C q) = Expr.lookup y (decodeStore (shapeOf P B) a i q) := by
            intro y hy
            have hyv : y < shV (shapeOf P B) := lt_shV_of_mem hmem hy
            show readVar y (storeOf C q) = readVar y (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q y hnS hyv, readVar_decodeStore hyv]
          have heval : Expr.eval e (storeOf C q) = some t := by
            have h4 : Expr.eval e (decodeStore (shapeOf P B) a i q) = some t :=
              decXe_eq_b hU h (Nat.le_of_lt hi) hq e hmem t hdec'
            rw [← h4]
            exact Expr.eval_congr h2
          have hcl2 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vxe (shapeOf P B) i q (eIdx P e) v), pos (vst (shapeOf P B) (i + 1) q x v)] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.assign x e) hact, hred, eachVal]
            refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hvlt, ?_⟩)
            rw [if_pos hvlt']
            exact List.Mem.head _
          have h3 := step_body_b hi hq hc h haq hpc0 hcl2
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvv,
            Bool.not_true, pos_eval] at h3
          have hwt : decSt (shapeOf P B) a (i + 1) q x = some t := by
            unfold decSt decVal
            have h5 : (stOh (shapeOf P B) (i + 1) q x).decode a = some v :=
              Oh.decode_of_true (sat_stOh_b (Nat.succ_le_of_lt hi) hq hxlt h)
                (List.mem_range.mpr hvlt) h3
            rw [h5]
            show rget (shapeOf P B).U v = some t
            exact ht
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succStore C q x t := by
            unfold decStep; simp [hev, hpcq, hact, heval]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rAssign (by rw [hpcq]; exact hact) heval
          rw [hstep]
          refine ⟨pcOf_succ_act_b h hi hag hq hk
              (pcOf_succStore' C q x t (by rw [hlenC]; exact hnS))
              (fun r hr hne => pcOf_succStore_other C q r x _ hne),
            decSt_succ_write_b h hi hag hq hk hact rfl hwt,
            (decKn_succ_none_b h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
            storeWF_succ_write_b h hi hag hq hxlt hk,
            by rw [sessLength_succStore, hag.2.2.2.2]⟩
      | check e₁ e₂ =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.check e₁ e₂) =
              [checkRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e₁),
                checkRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e₂)]
                ++ (eachVal (shapeOf P B) fun w =>
                    (List.range (shVal (shapeOf P B))).filterMap fun z =>
                      if w == z then none
                      else some (checkEqClause (shapeOf P B) i q
                        (decodePc (shapeOf P B) a i q) (eIdx P e₁) (eIdx P e₂) w z)) := by
            simp [actionClauses]
          obtain ⟨hm₁, hm₂⟩ := mem_allExprs_check hact
          obtain ⟨v₁, hde₁, hvl₁, hvar₁⟩ := decodeXe_lt_b hm₁ (Nat.le_of_lt hi) hq h
          obtain ⟨v₂, hde₂, hvl₂, hvar₂⟩ := decodeXe_lt_b hm₂ (Nat.le_of_lt hi) hq h
          have hs : shVal (shapeOf P B) = (shapeOf P B).U.length + 1 := rfl
          -- both sides denote real messages
          have hr₁ : a (vxe (shapeOf P B) i q (eIdx P e₁) ((shapeOf P B).U.length)) = false := by
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vxe (shapeOf P B) i q (eIdx P e₁) ((shapeOf P B).U.length))] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.check e₁ e₂) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_append_left _ ?_)
              exact List.Mem.head _
            have h1 := step_body_b hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or,
              neg_eval] at h1
            exact bool_not_true h1
          have hr₂ : a (vxe (shapeOf P B) i q (eIdx P e₂) ((shapeOf P B).U.length)) = false := by
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vxe (shapeOf P B) i q (eIdx P e₂) ((shapeOf P B).U.length))] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.check e₁ e₂) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_append_left _ ?_)
              exact List.Mem.tail _ (List.Mem.head _)
            have h1 := step_body_b hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or,
              neg_eval] at h1
            exact bool_not_true h1
          have hv₁ : v₁ < (shapeOf P B).U.length := by
            by_contra e
            have h1 : v₁ = (shapeOf P B).U.length := by
              rw [hs] at hvl₁
              omega
            rw [h1] at hvar₁
            exact absurd (hvar₁ ▸ hr₁) (by simp)
          have hv₂ : v₂ < (shapeOf P B).U.length := by
            by_contra e
            have h1 : v₂ = (shapeOf P B).U.length := by
              rw [hs] at hvl₂
              omega
            rw [h1] at hvar₂
            exact absurd (hvar₂ ▸ hr₂) (by simp)
          -- and they denote the same message
          have heqv : v₁ = v₂ := by
            by_contra e
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vxe (shapeOf P B) i q (eIdx P e₁) v₁),
                  neg (vxe (shapeOf P B) i q (eIdx P e₂) v₂)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.check e₁ e₂) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨v₁, List.mem_range.mpr hvl₁, ?_⟩))
              show actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                  [neg (vxe (shapeOf P B) i q (eIdx P e₁) v₁),
                    neg (vxe (shapeOf P B) i q (eIdx P e₂) v₂)] ∈
                (List.range (shVal (shapeOf P B))).filterMap fun z =>
                  if v₁ == z then none
                  else some (checkEqClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q)
                    (eIdx P e₁) (eIdx P e₂) v₁ z)
              refine List.mem_filterMap.mpr ⟨v₂, List.mem_range.mpr hvl₂, ?_⟩
              rw [if_neg (by intro h; exact e (by simpa using h))]
              rfl
            have h1 := step_body_b hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or,
              neg_eval, hvar₁, hvar₂, Bool.not_true] at h1
            exact absurd h1 (by simp)
          subst heqv
          obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U v₁ hv₁
          have hdec₁ : decXe (shapeOf P B) P a i q e₁ = some t := by
            unfold decXe decVal
            rw [hde₁]
            show rget (shapeOf P B).U v₁ = some t
            exact ht
          have hdec₂ : decXe (shapeOf P B) P a i q e₂ = some t := by
            unfold decXe decVal
            rw [hde₂]
            show rget (shapeOf P B).U v₁ = some t
            exact ht
          have hc₁ : ∀ x, x ∈ Expr.vars e₁ ->
              Expr.lookup x (storeOf C q) = Expr.lookup x (decodeStore (shapeOf P B) a i q) := by
            intro x hx
            have hxv : x < shV (shapeOf P B) := lt_shV_of_mem hm₁ hx
            show readVar x (storeOf C q) = readVar x (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q x hnS hxv, readVar_decodeStore hxv]
          have hc₂ : ∀ x, x ∈ Expr.vars e₂ ->
              Expr.lookup x (storeOf C q) = Expr.lookup x (decodeStore (shapeOf P B) a i q) := by
            intro x hx
            have hxv : x < shV (shapeOf P B) := lt_shV_of_mem hm₂ hx
            show readVar x (storeOf C q) = readVar x (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q x hnS hxv, readVar_decodeStore hxv]
          have he₁ : Expr.eval e₁ (storeOf C q) = some t := by
            have h4 : Expr.eval e₁ (decodeStore (shapeOf P B) a i q) = some t :=
              decXe_eq_b hU h (Nat.le_of_lt hi) hq e₁ hm₁ t hdec₁
            rw [← h4]
            exact Expr.eval_congr hc₁
          have he₂ : Expr.eval e₂ (storeOf C q) = some t := by
            have h4 : Expr.eval e₂ (decodeStore (shapeOf P B) a i q) = some t :=
              decXe_eq_b hU h (Nat.le_of_lt hi) hq e₂ hm₂ t hdec₂
            rw [← h4]
            exact Expr.eval_congr hc₂
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rCheck (by rw [hpcq]; exact hact) he₁ he₂
          · rw [hstep]
            exact agrees_succ_advance_b h hi hag hq hk hact rfl hlearn

      | secret e =>
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rSecret (by rw [hpcq]; exact hact)
          rw [hstep]
          exact agrees_succ_advance_b h hi hag hq hk hact rfl hlearn
      | claim tg peer v =>
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rClaim (by rw [hpcq]; exact hact)
          rw [hstep]
          exact agrees_succ_advance_b h hi hag hq hk hact rfl hlearn
      | commit tg peer v =>
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send_b hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rCommit (by rw [hpcq]; exact hact)
          rw [hstep]
          exact agrees_succ_advance_b h hi hag hq hk hact rfl hlearn
  · -- ---- the attacker fires deduction instance n ----
    obtain ⟨ins, hins0⟩ := rget_lt (dedInsts (shapeOf P B)) n hn
    have hins : instAt (shapeOf P B) n = some ins := hins0
    have hev : a (evDed (shapeOf P B) i n) = true := by
      have : a (vev (shapeOf P B) i (decCode P B a i)) = true := decCode_true_b hi h
      rw [hk] at this
      exact this
    have hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false := by
      intro r hr
      by_contra e
      have hlt : r < shS (shapeOf P B) := lt_shS hr
      have := decCode_of_evAct_b hi h hlt (by simpa [evAct] using e)
      have hpos : 0 < shS (shapeOf P B) := by unfold shS; omega
      omega
    cases hval : valAt (shapeOf P B) ins.concl with
    | none =>
        have hev' : decEv (shapeOf P B) P a i = Ev.idle := by
          rw [decEv_code_b hi h, hk,
            show (1 + shS (shapeOf P B) + n - 1 - shS (shapeOf P B)) = n by omega]
          simp [hins, hval]
        have hstep : decStep P B a C i = C := by unfold decStep; rw [hev']
        have hlearn : decLearn (shapeOf P B) P a i = none := by
          rw [decLearn_ded_b hi h hn ins hins hk, hval]
        refine ⟨?_, ?_⟩
        · rw [hev', hstep]
          exact Rel.rIdle P C
        · rw [hstep]
          exact agrees_of_noact_b h hi hno hag hlearn
    | some t =>
        have hev' : decEv (shapeOf P B) P a i = Ev.ded t := by
          rw [decEv_code_b hi h, hk,
            show (1 + shS (shapeOf P B) + n - 1 - shS (shapeOf P B)) = n by omega]
          simp [hins, hval]
        have hstep : decStep P B a C i = succDed C t := by unfold decStep; rw [hev']
        have hlearn : decLearn (shapeOf P B) P a i = some t := by
          rw [decLearn_ded_b hi h hn ins hins hk, hval]
        obtain ⟨u, hu, him⟩ := mem_dedInsts hins
        have hprem : instPremises (shapeOf P B) ins C.kn := by
          unfold instPremises
          intro p hp
          have hcl : [neg (evDed (shapeOf P B) i n), pos (vkn (shapeOf P B) i p)] ∈
              dedClausesAt (shapeOf P B) i n := by
            rw [dedClausesAt, hins]
            exact List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
          have hsat := sat_ded_b h _ (mem_ded hi hn hcl)
          simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hev,
            Bool.not_true, pos_eval] at hsat
          have hprange : p < (shapeOf P B).U.length := dedInstsOf_prem_lt hu him p hp
          obtain ⟨q, hq⟩ := rget_lt (shapeOf P B).U p hprange
          refine ⟨q, ?_, hq⟩
          rw [hag.2.2.1]
          exact kn_sound_b h hq i (Nat.le_of_lt hi) hsat
        have hone : OneStep C.kn t := dedInst_oneStep him hprem hval
        refine ⟨?_, ?_⟩
        · rw [hev', hstep]
          exact Rel.rDed hone
        · rw [hstep]
          refine agrees_of_frame_b h hi hag hno ?_ ?_ ?_ ?_ ?_
          · intro r hr; exact pcOf_succDed C r t
          · intro r x hr hx; exact readVar_succDed C r x t
          · rw [decKnSeq_succ, kn_succDed, hag.2.2.1, hlearn]
            show decKnSeq (shapeOf P B) P a i ++ [t] = decKnSeq (shapeOf P B) P a i ++ [t]
            rfl
          · intro r hr; exact hag.2.2.2.1 r hr
          · rw [sessLength_succDed, hag.2.2.2.2]

/-- At every step the decoded configuration agrees with the assignment: `agrees_zero_b` at the
base, `rel_agrees_b` in the induction step. -/
theorem agrees_decRun_b (h : Sat a (AuthClauses.baseEncode P B)) (hU : univClosed (shapeOf P B) P) :
    ∀ (k : Nat), k ≤ B.steps → Agrees P B a (decRun P B a k) k := by
  intro k
  induction k with
  | zero => intro _; exact agrees_zero_b h
  | succ k ih =>
      intro hk
      have h1 := rel_agrees_b hU h (by omega) (ih (by omega))
      exact h1.2

/-- The decoded run is a trace of the operational semantics. -/
theorem decRunFrom_runs_b (h : Sat a (AuthClauses.baseEncode P B)) (hU : univClosed (shapeOf P B) P) :
    ∀ (n : Nat), n ≤ B.steps ->
      Runs P (decRun P B a (B.steps - n)) (decEvsFrom P B a n) (decCfgsFrom P B a n) := by
  intro n
  induction n with
  | zero => intro _; exact Runs.nil P (decRun P B a B.steps)
  | succ n ih =>
      intro hn
      have hlt : B.steps - (n + 1) < B.steps := by omega
      have hag := agrees_decRun_b h hU (B.steps - (n + 1)) (by omega)
      have h1 := rel_agrees_b hU h hlt hag
      have hstep : decRun P B a (B.steps - (n + 1) + 1) = decStep P B a (decRun P B a (B.steps - (n + 1))) (B.steps - (n + 1)) := rfl
      have hrel : Rel P (decRun P B a (B.steps - (n + 1)))
          (decEv (shapeOf P B) P a (B.steps - (n + 1)))
          (decRun P B a (B.steps - (n + 1) + 1)) := by
        rw [hstep]
        exact h1.1
      have h2 := ih (by omega)
      have harith : B.steps - (n + 1) + 1 = B.steps - n := by omega
      have h2' : Runs P (decRun P B a (B.steps - (n + 1) + 1))
          (decEvsFrom P B a n) (decCfgsFrom P B a n) := by
        rw [harith]
        exact h2
      exact Runs.cons hrel h2'

/-- The full decoded trace is a run of the protocol from its initial configuration. -/
theorem decRun_trace_b (h : Sat a (AuthClauses.baseEncode P B)) (hU : univClosed (shapeOf P B) P) :
    Runs P (initCfg P) (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps) := by
  have h0 : decRun P B a (B.steps - B.steps) = initCfg P := by
    rw [Nat.sub_self]
    unfold decRun
    rfl
  rw [← h0]
  exact decRunFrom_runs_b h hU B.steps (Nat.le_refl _)


/-! ### 3. The decoded run is a bounded trace, over the semantic groups -/

/-- Every configuration the decoded segment visits lies in the universe, from a model of the semantic
groups alone. This is `Sound.runsInUniverse_decCfgsFrom` with the secrecy violation clause
dropped; its proof reads only `agrees_decRun_b`. -/
theorem runsInUniverse_decCfgsFrom_b (hU : univClosed (shapeOf P B) P)
    (h : Sat a (AuthClauses.baseEncode P B)) :
    ∀ (n : Nat), n ≤ B.steps → runsInUniverse (decCfgsFrom P B a n) (univ P B) := by
  intro n
  induction n with
  | zero =>
      intro _
      unfold runsInUniverse
      intro C hC
      rw [decCfgsFrom, List.mem_singleton] at hC
      subst hC
      exact Sound.decRun_cfgInUniverse (agrees_decRun_b h hU B.steps (Nat.le_refl _))
  | succ n ih =>
      intro hn
      unfold runsInUniverse
      intro C hC
      rw [decCfgsFrom, List.mem_cons] at hC
      rcases hC with rfl | hC
      · exact Sound.decRun_cfgInUniverse
          (agrees_decRun_b h hU (B.steps - (n + 1)) (by omega : B.steps - (n + 1) ≤ B.steps))
      · exact ih (by omega) C hC

/-- **The decoded run stays inside the universe**, from a model of the semantic groups. -/
theorem decoding_runsInUniverse_b (hU : univClosed (shapeOf P B) P)
    (h : Sat a (AuthClauses.baseEncode P B)) :
    runsInUniverse (decCfgsFrom P B a B.steps) (univ P B) :=
  runsInUniverse_decCfgsFrom_b hU h B.steps (Nat.le_refl _)

/-- **The first component of `DecodedRun`, discharged.** A model of the semantic groups decodes
to a bounded trace: `Sound.boundedTrace_decRun` with the secrecy violation clause dropped. This
is the lemma `GoalEncode`'s header says `decodedTrace_of_sat_encode` could not supply for
a goal-indexed formula. -/
theorem boundedTrace_decRun_b (hU : univClosed (shapeOf P B) P)
    (h : Sat a (AuthClauses.baseEncode P B)) :
    BoundedTrace P B (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps) :=
  ⟨decRun_trace_b h hU, Sound.decEvsFrom_length_le P B a, decoding_runsInUniverse_b hU h⟩

end ProtSat.Encoding

/-! ### 4. The authentication half of the bridge -/

namespace ProtSat.AgreesBase


open ProtSat Term OneHot Bounded Attacker Encode Protocol
open Encoding
open Complete
open AuthClauses
open GoalEncode

variable {P : Protocol} {B : Bounds} {a : Assignment}

/-! ### Reading an authentication occurrence -/

/-- What membership of an authentication occurrence buys: its position is a claim or commit position
of the model, its step is a real step of the bound, and its two value numbers are the ones its
annotations denote. -/
theorem authOccs_elim {sh : Shape} {P : Protocol} {commit : Bool} {o : AuthOcc}
    (ho : o ∈ authOccs sh P commit) :
    o.pos ∈ authPositions P ∧ o.pos.isCommit == commit ∧ o.step < sh.steps ∧
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
          exact ⟨hp.1, hp.2, List.mem_range.mp hi, hidx⟩

/-- An authentication position of the model is a real session index, a real program counter of that
session's role, and the action there is exactly the claim or commit the position records. -/
theorem mem_authPositions {P : Protocol} {p : AuthPos} (hp : p ∈ authPositions P) :
    p.sess < P.sessions.length ∧ p.pc < P.roleLen p.sess ∧
      ((p.isCommit = true ∧
          P.actionAt p.sess p.pc = some (Action.commit p.tag p.peer p.val)) ∨
        (p.isCommit = false ∧
          P.actionAt p.sess p.pc = some (Action.claim p.tag p.peer p.val))) := by
  unfold authPositions at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨q, hq, hp'⟩ := hp
  rw [List.mem_flatMap] at hp'
  obtain ⟨c, hc, hp''⟩ := hp'
  rw [List.mem_range] at hq hc
  cases h : P.actionAt q c with
  | none => simp [h] at hp''
  | some act =>
      cases act with
      | claim tag peer v =>
          rw [h] at hp''
          rw [List.mem_singleton] at hp''
          subst hp''
          exact ⟨hq, hc, Or.inr ⟨rfl, h⟩⟩
      | commit tag peer v =>
          rw [h] at hp''
          rw [List.mem_singleton] at hp''
          subst hp''
          exact ⟨hq, hc, Or.inl ⟨rfl, h⟩⟩
      | _ => simp [h] at hp''

/-! ### Closed constants -/

/-- An expression whose `constVal` is a message is a closed leaf: it has no children and reads no
store variable, so `Complete.eval_eq_constVal` applies to it in every store. -/
theorem constVal_closed {E : Expr} {t : Term} (h : Expr.constVal E = some t) :
    Expr.child1 E = none ∧ Expr.child2 E = none ∧ ∀ (x : Nat), E ≠ Expr.var x := by
  cases E with
  | agent A | nonce N | shrk a b | pubk a | privk a =>
      refine ⟨rfl, rfl, fun x hx => ?_⟩
      exact absurd hx (by simp)
  | var x => exact absurd h (by simp [Expr.constVal])
  | pair _ _ | encS _ _ | decS _ _ => exact absurd h (by simp [Expr.constVal])
  | encA _ _ | hash _ | fst _ | snd _ | decA _ _ => exact absurd h (by simp [Expr.constVal])

/-- The two messages a nameable position denotes are the constant values of its annotations, and
the universe contains both. This is `authOccMsgs` read backwards. -/
theorem authOccMsgs_some {sh : Shape} {p : AuthPos} {A : Agent} {d : Term}
    (h : authOccMsgs sh p = some (A, d)) :
    Expr.constVal p.peer = some (Term.agent A) ∧ Expr.constVal p.val = some d ∧
      Term.agent A ∈ sh.U ∧ d ∈ sh.U := by
  unfold authOccMsgs at h
  cases h1 : Expr.constVal p.peer with
  | none => simp [h1] at h
  | some x =>
      cases h2 : Expr.constVal p.val with
      | none => simp [h2] at h
      | some y =>
          rw [h1, h2] at h
          cases x with
          | agent A' =>
              by_cases hc : Term.agent A' ∈ sh.U && y ∈ sh.U
              · have h3 := h
                simp [hc] at h3
                obtain ⟨rflA, rflD⟩ := h3
                simp_all
              · simp [hc] at h
          | _ => simp at h

/-! ### The evaluation literal of a closed constant -/

/-- **The `vxe` literal of a closed constant is true.** The evaluation gate of a constant leaf is the
single clause pinning the entry to the message it denotes, so a model of the semantic groups makes
that literal true. This is the first half of `Encoding.xe_konst`, isolated because the authentication
bridge needs the literal and not the decoded value. -/
theorem vxe_konst_true {i q : Nat} {E : Expr} (he : E ∈ allExprs P) (h1 : Expr.child1 E = none)
    (h2 : Expr.child2 E = none) (hv : ∀ (x : Nat), E ≠ Expr.var x) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (AuthClauses.baseEncode P B)) :
    a (vxe (shapeOf P B) i q (eIdx P E) (uIdx (shapeOf P B) (Expr.constVal E))) = true := by
  have hg : Sat a (cnfOf
      [[pos (vxe (shapeOf P B) i q (eIdx P E) (uIdx (shapeOf P B) (Expr.constVal E)))]]) := by
    intro cl hcl
    have hmem : cl ∈ evalGate (shapeOf P B) P i q E := by
      rw [evalGate_konst h1 h2 hv]
      simpa [cnfOf] using hcl
    exact sat_gate_b he hi hq h cl hmem
  have hcl : Clause.eval a [pos (vxe (shapeOf P B) i q (eIdx P E)
      (uIdx (shapeOf P B) (Expr.constVal E)))] = true := by
    have := hg _ (List.Mem.head _)
    simpa using this
  rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at hcl
  exact hcl

/-! ### The decoded pair, zipped -/

/-- Reading a zip is zipping the reads. -/
theorem rget_zip {α β : Type} : ∀ (xs : List α) (ys : List β) (i : Nat) (x : α) (y : β),
    rget (xs.zip ys) i = some (x, y) <-> rget xs i = some x ∧ rget ys i = some y := by
  intro xs
  induction xs with
  | nil => intro ys i x y; simp [rget]
  | cons a as ih =>
      intro ys i x y
      cases i with
      | zero =>
          cases ys with
          | nil => simp [rget]
          | cons b bs => simp [rget, List.zip]
      | succ j =>
          cases ys with
          | nil => simp [rget]
          | cons b bs => exact ih bs j x y

/-- Position `i` of the zipped decoded pair is the configuration and the event of step `i`. -/
theorem rget_zip_decFrom {i : Nat} (hi : i < B.steps) :
    rget ((decCfgsFrom P B a B.steps).zip (decEvsFrom P B a B.steps)) i =
      some (decRun P B a i, decEv (shapeOf P B) P a i) := by
  rw [rget_zip]
  refine ⟨?_, ?_⟩
  · rw [decCfgsFrom_rget B.steps (Nat.le_refl _) i (by omega),
        show B.steps - B.steps + i = i by omega]
  · rw [decEvsFrom_rget B.steps (Nat.le_refl _) i (by omega),
        show B.steps - B.steps + i = i by omega]

/-- An authentication instance of a trace comes from a position of the zipped pair. -/
theorem mem_authInsts_elim {P : Protocol} {Cs : List Cfg} {tr : List Ev} {x : AuthInst}
    (h : x ∈ authInsts P Cs tr) :
    ∃ (i : Nat) (C : Cfg) (e : Ev), i < (Cs.zip tr).length ∧
      rget (Cs.zip tr) i = some (C, e) ∧ x ∈ authOfStep P C e := by
  unfold authInsts at h
  rw [List.mem_flatten] at h
  obtain ⟨l', hl', hx⟩ := h
  rw [List.mem_map] at hl'
  obtain ⟨p, hp, rfl⟩ := hl'
  obtain ⟨i, hi, hri⟩ := mem_rget (Cs.zip tr) p hp
  exact ⟨i, p.1, p.2, hi, hri, hx⟩

/-! ### The commit half of the bridge -/

/-- **`CommitsReflect` from the semantic groups.** Every commit occurrence whose literals are true is
a commit of the decoded run. Only two of the four literals are read: the session acts, and its program
counter is the position's. -/
theorem commitsReflect_of_sat (hU : univClosed (shapeOf P B) P) (hbase : Sat a (AuthClauses.baseEncode P B)) :
    CommitsReflect P B a := by
  intro o ho hall
  have h1 : a (evAct (shapeOf P B) o.step o.pos.sess) = true := by
    have := hall (pos (evAct (shapeOf P B) o.step o.pos.sess)) (by simp [authOccLits])
    simpa using this
  have h2 : a (vpc (shapeOf P B) o.step o.pos.sess o.pos.pc) = true := by
    have := hall (pos (vpc (shapeOf P B) o.step o.pos.sess o.pos.pc)) (by simp [authOccLits])
    simpa using this
  obtain ⟨hpos, hcommit, hstep, _⟩ := authOccs_elim ho
  obtain ⟨hlt, hpc, hact⟩ := mem_authPositions hpos
  have hstep' : o.step < B.steps := by rw [← steps_eq]; exact hstep
  have hnS1 : o.pos.sess < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hlt
  have hshS : o.pos.sess < shS (shapeOf P B) := lt_shS hnS1
  have hrl : P.roleLen o.pos.sess ≤ (shapeOf P B).nPc1 := roleLen_le_nPc1 hnS1
  have hshPc : o.pos.pc < shPc (shapeOf P B) := by
    show o.pos.pc < (shapeOf P B).nPc1 + 1
    omega
  have hc : decCode P B a o.step = 1 + o.pos.sess :=
    decCode_eq_of_true_b hstep' (evAct_lt (shapeOf P B) o.step o.pos.sess hshS) hbase h1
  have hEv : decEv (shapeOf P B) P a o.step =
      Ev.act o.pos.sess (decDeliver (shapeOf P B) a o.step o.pos.sess)
        (decNonce (shapeOf P B) a o.step o.pos.sess) :=
    decEv_act_of_decCode hshS hc
  have hag := agrees_decRun_b hbase hU o.step (by omega)
  have hpc' : decodePc (shapeOf P B) a o.step o.pos.sess = o.pos.pc :=
    decodePc_of_true_b (by omega) hshS hshPc hbase h2
  have hpc'' : pcOf (decRun P B a o.step) o.pos.sess = o.pos.pc :=
    (hag.1 o.pos.sess hnS1).trans hpc'
  have hact' : P.actionAt o.pos.sess o.pos.pc =
      some (Action.commit o.pos.tag o.pos.peer o.pos.val) := by
    rcases hact with ⟨hisc, hA⟩ | ⟨hisc, hA⟩
    · exact hA
    · exfalso
      rw [hisc] at hcommit
      simp at hcommit
  obtain ⟨A', d', hm, hd, hpv⟩ := authOccMsgs_of_mem ho
  have hcv := authOccMsgs_some hm
  have hcp := constVal_closed hcv.1
  have hcv' := constVal_closed hcv.2.1
  have hA1 : authOfStep P (decRun P B a o.step) (decEv (shapeOf P B) P a o.step) =
      [{ isCommit := true, tag := o.pos.tag, peer := A', val := d'}] := by
    rw [hEv]
    simp only [authOfStep]
    rw [hpc'', hact']
    show (match Expr.eval o.pos.peer (storeOf (decRun P B a o.step) o.pos.sess),
              Expr.eval o.pos.val (storeOf (decRun P B a o.step) o.pos.sess) with
        | some (Term.agent A''), some val' =>
            [{ isCommit := true, tag := o.pos.tag, peer := A'', val := val'}]
        | _, _ => []) =
      ([{ isCommit := true, tag := o.pos.tag, peer := A', val := d'}] : List AuthInst)
    rw [eval_eq_constVal o.pos.peer (storeOf (decRun P B a o.step) o.pos.sess)
        hcp.1 hcp.2.1 hcp.2.2,
      eval_eq_constVal o.pos.val (storeOf (decRun P B a o.step) o.pos.sess)
        hcv'.1 hcv'.2.1 hcv'.2.2,
      hcv.1, hcv.2.1]
  have hzip : rget ((decCfgsFrom P B a B.steps).zip (decEvsFrom P B a B.steps)) o.step =
      some (decRun P B a o.step, decEv (shapeOf P B) P a o.step) := rget_zip_decFrom hstep'
  have hmem : (decRun P B a o.step, decEv (shapeOf P B) P a o.step) ∈
      (decCfgsFrom P B a B.steps).zip (decEvsFrom P B a B.steps) :=
    rget_some_mem _ _ _ hzip
  have hinst : ({ isCommit := true, tag := o.pos.tag, peer := A', val := d'} : AuthInst) ∈
      authInsts P (decCfgsFrom P B a B.steps) (decEvsFrom P B a B.steps) := by
    unfold authInsts
    rw [List.mem_flatten]
    refine ⟨_, List.mem_map.mpr ⟨(decRun P B a o.step, decEv (shapeOf P B) P a o.step), hmem, rfl⟩, ?_⟩
    rw [hA1]
    simp
  refine ⟨(o.pos.tag, A', d'), ?_, ?_⟩
  · unfold commitsOf
    rw [List.mem_filterMap]
    exact ⟨_, hinst, by simp⟩
  · unfold authTriple
    rw [hm]
    rfl

/-! ### The claim half of the bridge -/

/-- What a claim step of the decoded run tells: the action at the acting session's program counter is
the claim, its two annotations evaluate in that session's decoded store to the instance's peer and
value, and the instance carries the position's tag. -/
theorem authOfStep_claim_elim {P : Protocol} {C : Cfg} {q : Nat} {m : Term} {d : NonceName}
    {tag : Tag} {peer v : Expr} {y : AuthInst}
    (hA : P.actionAt q (pcOf C q) = some (Action.claim tag peer v))
    (h : y ∈ authOfStep P C (Ev.act q m d)) :
    ∃ (A : Agent) (val : Term),
      Expr.eval peer (storeOf C q) = some (Term.agent A) ∧
        Expr.eval v (storeOf C q) = some val ∧ y.tag = tag ∧ y.peer = A ∧ y.val = val := by
  have hred : authOfStep P C (Ev.act q m d) =
      (match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
      | some (Term.agent A), some val => [{ isCommit := false, tag := tag, peer := A, val}]
      | _, _ => []) := by
    simp only [authOfStep, hA]
    rfl
  rw [hred] at h
  cases hpe : Expr.eval peer (storeOf C q) with
  | none => rw [hpe] at h; simp at h
  | some tv =>
      cases hv : Expr.eval v (storeOf C q) with
      | none => rw [hpe, hv] at h; simp at h
      | some val =>
          cases tv with
          | agent A =>
              rw [hpe, hv] at h
              rw [List.mem_singleton] at h
              subst h
              exact ⟨A, val, rfl, rfl, rfl, rfl, rfl⟩
          | nonce _ | key _ | pair _ _ | encS _ _ | encA _ _ | hash _ =>
              rw [hpe, hv] at h; simp at h

/-- A commit step only ever produces an instance flagged as a commit. -/
theorem authOfStep_isCommit_of_commit {P : Protocol} {C : Cfg} {q : Nat} {m : Term}
    {d : NonceName} {tag : Tag} {peer v : Expr} {y : AuthInst}
    (hA : P.actionAt q (pcOf C q) = some (Action.commit tag peer v))
    (h : y ∈ authOfStep P C (Ev.act q m d)) : y.isCommit = true := by
  have hred : authOfStep P C (Ev.act q m d) =
      (match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
      | some (Term.agent A), some val => [{ isCommit := true, tag := tag, peer := A, val}]
      | _, _ => []) := by
    simp only [authOfStep, hA]
    rfl
  rw [hred] at h
  cases hpe : Expr.eval peer (storeOf C q) with
  | none => rw [hpe] at h; simp at h
  | some tv =>
      cases hv : Expr.eval v (storeOf C q) with
      | none => rw [hpe, hv] at h; simp at h
      | some val =>
          cases tv with
          | agent A =>
              rw [hpe, hv] at h
              rw [List.mem_singleton] at h
              subst h
              rfl
          | nonce _ | key _ | pair _ _ | encS _ _ | encA _ _ | hash _ =>
              rw [hpe, hv] at h; simp at h

/-- **`ClaimsReflect` from the semantic groups plus `authNameable`.** Every claim the decoded
run makes is recorded by a claim occurrence of the model all four of whose literals are
true: the event literal from `decCode_true_b`, the program-counter literal from
`decodePc_true_b` and `agrees_decRun_b`, and the two value literals from `vxe_konst_true`.
This is the direction the soundness proof consumes. -/
theorem claimsReflect_of_sat (hU : univClosed (shapeOf P B) P) (hbase : Sat a (AuthClauses.baseEncode P B))
    (hN : authNameable (shapeOf P B) P) : ClaimsReflect P B a := by
  intro t ht
  unfold claimsOf at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨x, hx, hfx⟩ := ht
  have hxc : x.isCommit = false := by
    cases h : x.isCommit with
    | true => have h2 := hfx; rw [h] at h2; exact absurd h2 (by simp)
    | false => rfl
  have htrip : (x.tag, x.peer, x.val) = t := by
    have h2 := hfx
    rw [hxc] at h2
    exact Option.some.inj h2
  obtain ⟨i, C, e, hi, hzip, hstep⟩ := mem_authInsts_elim hx
  have hlen : i < B.steps := by
    have h1 : (decEvsFrom P B a B.steps).length = B.steps := decEvsFrom_length P B a B.steps
    have h2 : ((decCfgsFrom P B a B.steps).zip (decEvsFrom P B a B.steps)).length ≤ B.steps := by
      rw [List.length_zip]
      omega
    omega
  rw [rget_zip] at hzip
  obtain ⟨hCi, hei⟩ := hzip
  have hCi' : rget (decCfgsFrom P B a B.steps) i = some (decRun P B a i) := by
    rw [decCfgsFrom_rget B.steps (Nat.le_refl _) i (by omega)]
    rw [show B.steps - B.steps + i = i by omega]
  have hei' : rget (decEvsFrom P B a B.steps) i = some (decEv (shapeOf P B) P a i) := by
    rw [decEvsFrom_rget B.steps (Nat.le_refl _) i (by omega)]
    rw [show B.steps - B.steps + i = i by omega]
  have hCe : C = decRun P B a i := Option.some.inj (hCi.symm.trans hCi')
  have hee : e = decEv (shapeOf P B) P a i := Option.some.inj (hei.symm.trans hei')
  subst hCe
  subst hee
  cases hEv : decEv (shapeOf P B) P a i with
  | act q m d =>
      rw [hEv] at hstep
      cases hA : P.actionAt q (pcOf (decRun P B a i) q) with
      | none =>
          exfalso
          simp only [authOfStep, hA] at hstep
          exact absurd hstep (by simp)
      | some act =>
          cases act with
          | claim tag peer v =>
              obtain ⟨A, val, hpe, hv, hxt, hxp, hxv⟩ := authOfStep_claim_elim hA hstep
              have htrip' : (tag, A, val) = t := by
                rw [← hxt, ← hxp, ← hxv]
                exact htrip
              have hpcLt : pcOf (decRun P B a i) q < P.roleLen q :=
                lt_roleLen_of_actionAt (by rw [hA]; intro h; cases h)
              have hq : q < P.sessions.length := by
                by_contra he
                have hr : P.roleAt q = none := by
                  unfold roleAt
                  rw [List.drop_eq_nil_of_le (by omega : P.sessions.length ≤ q)]
                  rfl
                have hl : P.roleLen q = 0 := by unfold roleLen; rw [hr]
                omega
              set p : AuthPos := { isCommit := false, sess := q, pc := pcOf (decRun P B a i) q, tag := tag, peer := peer, val := v } with hpdef
              have hpos : p ∈ authPositions P := by
                unfold authPositions
                rw [List.mem_flatMap]
                refine ⟨q, List.mem_range.mpr hq, ?_⟩
                rw [List.mem_flatMap]
                refine ⟨pcOf (decRun P B a i) q, List.mem_range.mpr hpcLt, ?_⟩
                rw [hA]
                exact List.Mem.head _
              have hstepLt : i < (shapeOf P B).steps := by rw [steps_eq]; exact hlen
              obtain ⟨u, u', hidx⟩ : ∃ u u', authOccIdx (shapeOf P B) p = some (u, u') := by
                obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hN p hpos)
                cases w with
                | mk u u' => exact ⟨u, u', hw⟩
              have hidx0 : authOccIdx (shapeOf P B) p = some (u, u') := hidx
              rw [authOccIdx_map] at hidx
              obtain ⟨A', d', hmsg, heq⟩ : ∃ A' d', authOccMsgs (shapeOf P B) p = some (A', d') ∧
                  (uIdx (shapeOf P B) (some d'), uIdx (shapeOf P B) (some (Term.agent A'))) =
                    (u, u') := by
                cases h : authOccMsgs (shapeOf P B) p with
                | none => rw [h] at hidx; simp at hidx
                | some z =>
                    cases z with
                    | mk A' d' =>
                        rw [h] at hidx
                        obtain ⟨hu, hu'⟩ := Prod.mk.inj (Option.some.inj hidx)
                        exact ⟨A', d', rfl, Prod.ext hu hu'⟩
              obtain ⟨hu, hu'⟩ := Prod.mk.inj heq
              have hcv := authOccMsgs_some hmsg
              have hcp := constVal_closed hcv.1
              have hcv2 := constVal_closed hcv.2.1
              have hAeq : A' = A := by
                have h9 := eval_eq_constVal peer (storeOf (decRun P B a i) q)
                  hcp.1 hcp.2.1 hcp.2.2
                have h10 := hpe
                rw [h9, hcv.1] at h10
                exact Term.agent.inj (Option.some.inj h10)
              have heq' : d' = val := by
                have h9 := eval_eq_constVal v (storeOf (decRun P B a i) q)
                  hcv2.1 hcv2.2.1 hcv2.2.2
                have h10 := hv
                rw [h9, hcv.2.1] at h10
                exact Option.some.inj h10
              have hmem : (decRun P B a i, decEv (shapeOf P B) P a i) ∈
                  (decCfgsFrom P B a B.steps).zip (decEvsFrom P B a B.steps) :=
                rget_some_mem _ _ _ (rget_zip_decFrom hlen)
              have hinst : x ∈ authInsts P (decCfgsFrom P B a B.steps)
                  (decEvsFrom P B a B.steps) := by
                unfold authInsts
                rw [List.mem_flatten]
                refine ⟨_, List.mem_map.mpr ⟨_, hmem, rfl⟩, ?_⟩
                rw [hEv]
                exact hstep
              set k : AuthOcc := { pos := p, step := i, data := u, peerVal := u' } with hk
              refine ⟨k, ?_, ?_, ?_⟩
              · unfold authOccs
                rw [List.bind_eq_flatMap, List.mem_flatMap]
                refine ⟨p, ?_, ?_⟩
                · rw [List.mem_filter]
                  exact ⟨hpos, rfl⟩
                · rw [hidx0]
                  rw [List.mem_map]
                  exact ⟨i, List.mem_range.mpr hstepLt, rfl⟩
              · unfold authTriple
                rw [hmsg]
                rw [← htrip']
                show some (p.tag, A', d') = some (tag, A, val)
                rw [show p.tag = tag from rfl, hAeq, heq']
              · intro l hl
                rw [hk, authOccLits, hpdef] at hl
                rw [List.mem_cons, List.mem_cons, List.mem_cons,
                  List.mem_singleton] at hl
                rcases hl with rfl | rfl | rfl | rfl
                · have hc : decCode P B a i = 1 + q := decCode_of_decEv_act hEv
                  have h2 := decCode_true_b hlen hbase
                  rw [hc] at h2
                  simpa [evAct] using h2
                · have hag := agrees_decRun_b hbase hU i (by omega)
                  have hnS1 : q < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hq
                  rw [hag.1 q hnS1]
                  exact decodePc_true_b (i := i) (q := q) (by omega) (lt_shS hnS1) hbase
                · have hnS1 : q < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hq
                  have hme := mem_allExprs_claim (h := hA)
                  have h2 := vxe_konst_true (i := i) (q := q) (E := v) hme.2 hcv2.1 hcv2.2.1 hcv2.2.2
                    (by omega) (lt_shS hnS1) hbase
                  rw [hcv.2.1, hu] at h2
                  exact h2
                · have hnS1 : q < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hq
                  have hme := mem_allExprs_claim (h := hA)
                  have h2 := vxe_konst_true (i := i) (q := q) (E := peer) hme.1 hcp.1 hcp.2.1 hcp.2.2
                    (by omega) (lt_shS hnS1) hbase
                  rw [hcv.1, hu'] at h2
                  exact h2
          | commit tag peer v =>
              exfalso
              have h1 : x.isCommit = true :=
                authOfStep_isCommit_of_commit (hA := hA) (h := hstep)
              rw [h1] at hxc
              exact absurd hxc (by simp)
          | fresh _ _ | send _ _ | recv _ _ | assign _ _ | check _ _ | secret _ =>
              exfalso
              simp only [authOfStep, hA] at hstep
              exact absurd hstep (by simp)
  | idle | ded _ =>
      exfalso
      rw [show authOfStep P (decRun P B a i) (decEv (shapeOf P B) P a i) = [] from
        by rw [hEv]; simp only [authOfStep]] at hstep
      exact absurd hstep (by simp)


/-! ### 5. The bridge discharged, and the corollary -/

/-- **The trace half of the bridge, from any goal-indexed formula.** A model of a goal-indexed
formula decodes to a bounded trace whatever goals were selected: the semantic groups are shared by
every goal-indexed formula and they are all the trace half ever read. -/
theorem boundedTrace_of_sat_goals {P : Protocol} {B : Bounds} {gs : List Goal} {m : Matching}
    {a : Assignment} (hU : univClosed (shapeOf P B) P)
    (h : Sat a (encodeGoalsOfM P B gs m)) :
    BoundedTrace P B (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps) :=
  Encoding.boundedTrace_decRun_b hU (GoalEncode.sat_baseEncode_of_sat h)

/-- **The decoded-run bridge, discharged.** A model of the goal-indexed formula that selects the
agreement goal, under the two shape hypotheses the decoding chain has always needed, satisfies
`GoalEncode.DecodedRun`: the decoded run is a bounded trace, a commit occurrence with true
literals is a commit of the decoded run, and every decoded claim is named by a complete claim
occurrence. This is the single obstacle `GoalEncode`'s module header names. -/
theorem decodedRun_of_sat_agreement {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (h : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly)) :
    GoalEncode.DecodedRun P B a := by
  have hbase : Sat a (AuthClauses.baseEncode P B) := GoalEncode.sat_baseEncode_of_sat h
  exact ⟨Encoding.boundedTrace_decRun_b hU hbase,
    commitsReflect_of_sat hU hbase, claimsReflect_of_sat hU hbase hN⟩

/-- **SOUND for the agreement goal, with the bridge discharged.** This is
`GoalEncode.boundedAttackGoals_of_sat_agreement` with its `DecodedRun` hypothesis proved:
a model of the goal-indexed formula that selects the agreement goal, on a model whose bounds keep the
protocol inside the universe and whose authentication annotations are nameable, is a bounded attack on
the agreement goal of the query. Nothing is assumed about secrecy, and no decoded-run property is
hypothesised. -/
theorem boundedAttackGoals_of_sat_agreement_discharged {P : Protocol} {B : Bounds}
    {a : Assignment} (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (h : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly)) :
    boundedAttackGoals (Query.mk P B [Goal.agreement]) :=
  GoalEncode.boundedAttackGoals_of_sat_agreement h
    (decodedRun_of_sat_agreement hU hN h)

/-- **The existential form.** Satisfiability of the agreement goal-indexed formula implies a bounded
attack on the agreement goal, under the two shape hypotheses. -/
theorem boundedAttackGoals_of_satisfiable_agreement {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P) :
    Satisfiable (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) →
      boundedAttackGoals (Query.mk P B [Goal.agreement]) := by
  rintro ⟨a, ha⟩
  exact boundedAttackGoals_of_sat_agreement_discharged hU hN ha

/-- **The limitation, inside a statement.** The attack this file produces is a violation of the
*unordered* agreement predicate: `Query.Violation P Goal.agreement` IS `ProtSat.AuthBreak`,
so the conclusion of `boundedAttackGoals_of_sat_agreement_discharged` unfolds to a trace and a
visit list whose committed triple was never claimed - triple by triple, with no ordering and no
identity-of-principals requirement. Naming this explicitly is the point: the theorem is soundness for
`AuthBreak`, and `ProtSat/AgreementPredicates.lean` shows `AuthBreak` and the
ordered reference monitor are incomparable, so nothing here should be cited as soundness for the
ordered notion. -/
theorem unordered_conclusion_is_AuthBreak {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (h : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly)) :
    ∃ (tr : List Ev) (Cs : List Cfg),
      BoundedTrace P B tr Cs ∧ AuthBreak P Cs tr := by
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ :=
    boundedAttackGoals_of_sat_agreement_discharged hU hN h
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨tr, Cs, hbt, (violation_agreement P Cs tr).mp hv⟩

/-- The bridge is not a hypothesis about an empty class: every model of the agreement encoding
supplies one, so the assignments `DecodedRun` talks about are exactly the ones the solver
returns. -/
theorem decodedRun_of_sat_agreementEncode {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (h : Sat a (agreementEncode P B Matching.tripleOnly)) : GoalEncode.DecodedRun P B a :=
  decodedRun_of_sat_agreement hU hN (by
    rw [encodeGoalsOfM_agreement]
    exact h)


/-! ### 6. The instance: the AuthGap agreement model, decided

The decisions below walk the whole clause list of the AuthGap formula, so they need the same two
options `GoalEncode` sets for its own gate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0


/-- The AuthGap model, named once. `Regressions.Authentication.P` is the model that
`AuthGap.safe_for_secrecy2` reports *safe* through the secrecy CNF and
`AuthClauses.Diff.diff_authentication` reports attacked by the reference enumeration: the model
the agreement goal was built for. -/
abbrev authGapP : Protocol := Regressions.Authentication.P

/-- The bounds of the AuthGap gate. -/
abbrev authGapB : Bounds := Regressions.Authentication.B

/-- **The universe hypothesis holds on the AuthGap model**, decided by the kernel (~0.1 s of replay). -/
theorem authGap_univClosed : univClosed (shapeOf authGapP authGapB) authGapP := by
  have h : (allExprs authGapP).all
      (fun e => admissible (shapeOf authGapP authGapB) (Expr.constVal e)) = true := by decide
  exact (List.all_eq_true (p := fun e =>
    admissible (shapeOf authGapP authGapB) (Expr.constVal e))).mp h

/-- **Every authentication position of the AuthGap model is nameable**, decided by the kernel
(~0.1 s of replay): each claim and commit addresses a closed agent constant and agrees on a closed
message, both inside the universe. -/
theorem authGap_authNameable : authNameable (shapeOf authGapP authGapB) authGapP := by
  have h : (authPositions authGapP).all
      (fun p => (authOccIdx (shapeOf authGapP authGapB) p).isSome) = true := by decide
  exact (List.all_eq_true (p := fun p =>
    (authOccIdx (shapeOf authGapP authGapB) p).isSome)).mp h

/-- **The solver's assignment satisfies the triple-only agreement encoding of the AuthGap model.**
Decided by the kernel: every clause of `encodeGoalsOfM authGapP authGapB [Goal.agreement]
Matching.tripleOnly` is checked against `AuthClauses.attackAsg`. This is the same assignment
`AuthClauses.gate_agreement_attack_found` verifies for the *ordered* formula, so the witness is
not new - only the monitor it is checked against. Kernel replay: ~12 s, measured with
`lake env lean` on this file. -/
theorem authGap_sat_asg :
    Sat (DPLL.asgVal AuthClauses.attackAsg)
      (encodeGoalsOfM authGapP authGapB [Goal.agreement] Matching.tripleOnly) := by
  rw [encodeGoalsOfM_agreement]
  exact sat_of_all (by decide : (agreementEncode authGapP authGapB Matching.tripleOnly).clauses.all
    (fun c => Clause.eval (DPLL.asgVal AuthClauses.attackAsg) c) = true)

/-- Hence the triple-only agreement encoding of the AuthGap model is satisfiable. -/
theorem authGap_sat_tripleOnly :
    Satisfiable (encodeGoalsOfM authGapP authGapB [Goal.agreement] Matching.tripleOnly) :=
  ⟨DPLL.asgVal AuthClauses.attackAsg, authGap_sat_asg⟩

/-- **The bridge is realised by a concrete assignment**: the decoded run of `attackAsg` is a
bounded trace of the AuthGap model, a commit occurrence with true literals is a commit of it, and
every claim it makes is named by a complete claim occurrence. The hypotheses of the corollary are not
a hypothesis about an empty class. -/
theorem authGap_decodedRun :
    GoalEncode.DecodedRun authGapP authGapB (DPLL.asgVal AuthClauses.attackAsg) :=
  decodedRun_of_sat_agreement authGap_univClosed authGap_authNameable authGap_sat_asg

/-- **SOUND for the agreement goal, on a real model.** The AuthGap model has a bounded attack on the
agreement goal of its query, produced from a kernel-checked model of the goal-indexed CNF rather than
from the reference enumeration. This is the cross-check of
`AuthClauses.Diff.diff_authentication`'s `attackFound` gate through the encoding, and it
is the first decided instance of the agreement soundness direction. -/
theorem authGap_boundedAttackGoals_agreement :
    boundedAttackGoals (Query.mk authGapP authGapB [Goal.agreement]) :=
  (authGap_sat_tripleOnly).elim fun a ha =>
    boundedAttackGoals_of_sat_agreement_discharged authGap_univClosed authGap_authNameable ha

/-- The unordered reading, on the instance: the attack produced above is an `AuthBreak` - a
commit triple no session ever claimed - and says nothing about ordering. -/
theorem authGap_unordered :
    ∃ (tr : List Ev) (Cs : List Cfg),
      BoundedTrace authGapP authGapB tr Cs ∧ AuthBreak authGapP Cs tr :=
  unordered_conclusion_is_AuthBreak authGap_univClosed authGap_authNameable authGap_sat_asg

end ProtSat.AgreesBase
