/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import Mathlib.Tactic.Linarith

/-!
# ProtSat: the converse correspondence (specification section 8B)

## What this module proves

ProtSat.Encoding.encoding_sound (8A) turns a satisfying assignment of the generated CNF
into a genuine bounded attack.  This module proves the converse, **encoding_complete**:

> every valid bounded attack execution of the protocol is represented by a satisfying
> assignment of the encoded formula.

Together the two theorems are the correspondence the project is about: within the declared
bounds, "the solver finds a model" and "the protocol has an attack" are the same statement.
8B is what makes a SAFE verdict meaningful (specification 8G): if the solver says UNSAT
then no bounded attack exists, because had one existed the construction below would have
produced a model.

## The construction

The assignment is the *characteristic function of the run*.  For a run with configurations
`cfg : Nat -> Cfg` and events `ev : Nat -> Ev`, a propositional variable is true exactly
when the semantic fact it names holds in the run.  Because the variables are laid out in
disjoint blocks (ProtSat.Encode.bsPc, bsSt, bsKn, bsEv, bsDl, bsFr, bsXe, bsTotal, bsAu),
the test is a cascade of range comparisons, and inside a block a bounded search over that
block's own index ranges.  Nothing is decoded by division: the block of a variable is found
by comparison, and inside the block the index is recovered from the injectivity of the
positional codes (ProtSat.Encode.vpc_inj and friends).

## Where the bounds are used

The construction needs the run to stay inside the analysis bounds: every message the
attacker knows and every value a session stores must be a universe message, every session
that acts must be instantiated, every generated nonce must be in the nonce domain, and
every attacker step must be one of the enumerated rule instances.  That hypothesis is
ProtSat.Complete.WithinBounds; it is not a technicality - a run that leaves the universe
cannot be represented by a finite encoding at all, and the README says so.
-/

namespace ProtSat.Complete

open ProtSat Term OneHot Bounded Attacker Encode Encoding

/-! ### Reading a run by position -/

/-- Walking down a visited list: the current configuration while there are configurations
left, and the last one repeated forever afterwards.  A finished run stands still, which is
what the idle steps of the encoding require. -/
def cfgGo : Cfg → List Cfg → Nat → Cfg
  | C, [], _ => C
  | C, D :: rest, 0 => C
  | _, D :: rest, k + 1 => cfgGo D rest k

/-- The configuration at step i of a visited list: the i-th one, or the last one when i goes
past the end (a finished run stays where it is, which is what the idle steps do). -/
def cfgAt (Cs : List Cfg) (i : Nat) : Cfg :=
  match Cs with
  | [] => ⟨[], []⟩
  | C :: rest => cfgGo C rest i

/-- The event taken at step i: the i-th one, or ProtSat.Ev.idle past the end. -/
def evAt (tr : List Ev) (i : Nat) : Ev := (tr.drop i).headD Ev.idle

/-- The head of a run is its initial configuration. -/
theorem cfgAt_head {C : Cfg} {rest : List Cfg} : cfgAt (C :: rest) 0 = C := by
  cases rest <;> rfl

/-- Inside a non-empty tail, reading one step further is reading the tail one step less. -/
theorem cfgAt_cons_succ {C : Cfg} {rest : List Cfg} (h : rest ≠ []) (i : Nat) :
    cfgAt (C :: rest) (i + 1) = cfgAt rest i := by
  cases rest with
  | nil => exact absurd rfl h
  | cons y ys => rfl

theorem evAt_head {e : Ev} {rest : List Ev} : evAt (e :: rest) 0 = e := by
  unfold evAt
  simp [List.headD]

theorem evAt_cons_succ {e : Ev} {rest : List Ev} (i : Nat) :
    evAt (e :: rest) (i + 1) = evAt rest i := rfl

/-- Reading a singleton run always gives its only configuration. -/
theorem cfgAt_single {C : Cfg} (i : Nat) : cfgAt [C] i = C := rfl

/-- Past the end of the event list the read is idle. -/
theorem evAt_past {tr : List Ev} (i : Nat) (h : tr.length ≤ i) : evAt tr i = Ev.idle := by
  unfold evAt
  rw [List.drop_eq_nil_of_le h]
  rfl

theorem evAt_nil (i : Nat) : evAt ([] : List Ev) i = Ev.idle := by
  unfold evAt
  cases i <;> simp [List.headD]

/-- Past the end of the visited list the read stands still on the last configuration. -/
theorem cfgAt_past {Cs : List Cfg} (h : Cs ≠ []) (i : Nat) (hi : i + 1 ≥ Cs.length) :
    cfgAt Cs i = cfgAt Cs (i + 1) := by
  cases Cs with
  | nil => exact absurd rfl h
  | cons x xs =>
      cases i with
      | zero =>
          have hlen : xs.length = 0 := by simpa [List.length_cons] using hi
          cases xs with
          | nil => rfl
          | cons y ys => simp at hlen
      | succ i =>
          cases xs with
          | nil => show cfgGo x [] (i + 1) = cfgGo x [] (i + 1 + 1); rfl
          | cons y ys =>
              rw [cfgAt_cons_succ (by simp) i, cfgAt_cons_succ (by simp) (i + 1)]
              have h2 : i + 1 ≥ (y :: ys).length := by
                simp [List.length_cons] at hi ⊢
                omega
              exact cfgAt_past (by simp) i h2

/-- **Every position of a run is a transition.**  Reading the visited list and the event list
by position turns a ProtSat.Runs derivation into a pointwise ProtSat.Rel statement, valid
also past the end of the trace, where the run idles. -/
theorem runs_rel {P : Protocol} {C0 : Cfg} {tr : List Ev} {Cs : List Cfg}
    (hr : Runs P C0 tr Cs) :
    C0 = cfgAt Cs 0 ∧
      ∀ (i : Nat), Rel P (cfgAt Cs i) (evAt tr i) (cfgAt Cs (i + 1)) := by
  induction hr with
  | nil C =>
      refine ⟨rfl, ?_⟩
      intro i
      simp [cfgAt_single, evAt_nil]
      exact Rel.rIdle P C
  | cons hstep hrest ih =>
      rename_i C C' e tr' rest
      obtain ⟨h1, h2⟩ := ih
      have hne : rest ≠ [] := by
        intro hz
        have hl := runs_length hrest
        rw [hz] at hl
        simp at hl
      refine ⟨cfgAt_head.symm, ?_⟩
      intro i
      by_cases hi : i < (e :: tr').length
      · cases i with
        | zero =>
            rw [cfgAt_head, evAt_head, cfgAt_cons_succ hne 0, ← h1]
            exact hstep
        | succ i =>
            rw [cfgAt_cons_succ hne i, evAt_cons_succ i, cfgAt_cons_succ hne (i + 1)]
            have hlen'' : i < tr'.length := by simpa using hi
            exact h2 i
      · -- past the end: the run stands still and idles
        have hlen : (e :: tr').length ≤ i := by omega
        have he : evAt (e :: tr') i = Ev.idle := evAt_past i hlen
        have hcs : (C :: rest).length = (e :: tr').length + 1 := by
          have hl := runs_length hrest
          simp [List.length_cons, hl]
        have h3 : cfgAt (C :: rest) i = cfgAt (C :: rest) (i + 1) :=
          cfgAt_past (by simp) i (by omega)
        rw [he, h3]
        exact Rel.rIdle P _

/-! ### The boundedness hypothesis -/

/-- **The run stays inside the shape** (the general form, stated for an arbitrary shape).
Every message the attacker ever knows and every value any session ever stores is a universe
message; every session that acts is one the shape instantiates, and both the message
delivered to it and the nonce it generates belong to the shape; every message the attacker
learns in one step is in the universe; and every program counter and every store variable
stays inside the shape's bounds.  These are exactly the conditions under which a finite
encoding can represent the run at all - a run that leaves the universe has no finite name,
and a run whose session index is not instantiated has no event alternative. -/
def RunOK (sh : Shape) (P : Protocol) (cfg : Nat → Cfg) (ev : Nat → Ev) : Prop :=
  (∀ i t, t ∈ (cfg i).kn → t ∈ sh.U) ∧
  (∀ i q v, q < sh.nS1 → v ∈ storeVals (storeOf (cfg i) q) → v ∈ sh.U) ∧
  (∀ i q m d, ev i = Ev.act q m d → q < sh.nS1 ∧ m ∈ sh.U ∧ d ∈ sh.D) ∧
  (∀ i t, ev i = Ev.ded t → t ∈ sh.U) ∧
  (∀ i q, q < sh.nS1 → pcOf (cfg i) q < shPc sh) ∧
  (∀ i q x, q < sh.nS1 → x ∈ (storeOf (cfg i) q).map Prod.fst → x < shV sh)

/-- **The run stays inside the bounds**: ProtSat.Complete.RunOK at the shape of the analysis.
This is the hypothesis the completeness theorem (specification 8B) needs and the analyser
checks, because a run that leaves the declared bounds cannot be named by the formula at all.
-/
def WithinBounds (P : Protocol) (B : Bounds) (cfg : Nat → Cfg) (ev : Nat → Ev) : Prop :=
  RunOK (shapeOf P B) P cfg ev

/-! ### Block ranges of the positional codes

The variables of the encoding live in nine disjoint blocks (ProtSat.Encode.bsPc, bsSt, bsKn,
bsEv, bsDl, bsFr, bsXe, bsTotal, bsAu).  The lemmas below say that every positional code of a
family, evaluated at in-range indices, lands inside its own block.  They are what makes the
cascade of range tests in ProtSat.Complete.assignOf unambiguous: the block of a variable is
found by comparison, never by division. -/

section Ranges

/-- Scaling a bounded index: i ≤ L and q < S put i*S + q strictly below (L+1)*S. -/
theorem scale_lt {i L S q : Nat} (hi : i ≤ L) (hS : 0 < S) (hq : q < S) :
    i * S + q < (L + 1) * S := by
  have h1 : i * S ≤ L * S := Nat.mul_le_mul_right S hi
  have h2 : i * S + q < L * S + S := Nat.add_lt_add_of_le_of_lt h1 hq
  have h3 : (L + 1) * S = L * S + S := by rw [Nat.add_mul, Nat.one_mul]
  rw [h3]
  exact h2

/-- Scaling a strictly bounded index: i < L and q < S put i*S + q strictly below L*S. -/
theorem scale_lt' {i L S q : Nat} (hi : i < L) (hS : 0 < S) (hq : q < S) :
    i * S + q < L * S := by
  have h1 : i * S + q < (i + 1) * S := by
    have h1' : (i + 1) * S = i * S + S := by rw [Nat.add_mul, Nat.one_mul]
    rw [h1']
    exact Nat.add_lt_add_left hq _
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right S (Nat.succ_le_of_lt hi))

/-- One Horner step: X < A and c < C with C positive put X*C + c strictly below A*C. -/
theorem horner_lt {X A C c : Nat} (hX : X < A) (hC : 0 < C) (hc : c < C) :
    X * C + c < A * C := by
  have h1 : X * C + c < X * C + C := Nat.add_lt_add_left hc _
  have h2 : X * C + C = (X + 1) * C := by rw [Nat.add_mul, Nat.one_mul]
  rw [h2] at h1
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right C (Nat.succ_le_of_lt hX))

variable (sh : Shape)

/-- A program-counter code lies below the store block. -/
theorem vpc_lt_bsSt (i q c : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (hc : c < shPc sh) :
    vpc sh i q c < bsSt sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shPc sh + c < (sh.steps + 1) * shS sh * shPc sh :=
    horner_lt h1 (shPc_pos sh) hc
  simp only [vpc, bsPc, bsSt, szPc, Nat.zero_add]
  exact h2

/-- A store code lies at or above the store block's base. -/
theorem vst_ge (i q x u : Nat) : bsSt sh ≤ vst sh i q x u := Nat.le_add_right _ _

/-- A store code lies below the knowledge block. -/
theorem vst_lt_bsKn (i q x u : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh)
    (hu : u < shVal sh) : vst sh i q x u < bsKn sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shV sh + x < (sh.steps + 1) * shS sh * shV sh :=
    horner_lt h1 (shV_pos sh) hx
  have h3 : ((i * shS sh + q) * shV sh + x) * shVal sh + u
      < (sh.steps + 1) * shS sh * shV sh * shVal sh := horner_lt h2 (shVal_pos sh) hu
  simp only [vst, bsKn, bsSt, bsPc, szSt, szPc, Nat.zero_add]
  exact Nat.add_lt_add_left h3 _

/-- A knowledge code lies at or above the knowledge block's base. -/
theorem vkn_ge (i u : Nat) : bsKn sh ≤ vkn sh i u := Nat.le_add_right _ _

/-- A knowledge code lies below the event block. -/
theorem vkn_lt_bsEv (i u : Nat) (hi : i ≤ sh.steps) (hu : u < shVal sh) :
    vkn sh i u < bsEv sh := by
  have h1 : i * shVal sh + u < (sh.steps + 1) * shVal sh :=
    horner_lt (by omega : i < sh.steps + 1) (shVal_pos sh) hu
  simp only [vkn, bsEv, bsKn, bsSt, bsPc, szKn, szSt, szPc, Nat.zero_add]
  exact Nat.add_lt_add_left h1 _

/-- An event code lies at or above the event block's base. -/
theorem vev_ge (i k : Nat) : bsEv sh ≤ vev sh i k := Nat.le_add_right _ _

/-- An event code lies below the delivery block. -/
theorem vev_lt_bsDl (i k : Nat) (hi : i < sh.steps) (hk : k < shEv sh) :
    vev sh i k < bsDl sh := by
  have h1 : i * shEv sh + k < sh.steps * shEv sh := horner_lt hi (shEv_pos sh) hk
  have h2 : i * shEv sh + k < (sh.steps + 1) * shEv sh :=
    Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right (shEv sh) (Nat.le_succ sh.steps))
  simp only [vev, bsDl, bsEv, bsKn, bsSt, bsPc, szEv, szKn, szSt, szPc, Nat.zero_add]
  exact Nat.add_lt_add_left h2 _

/-- A delivery code lies at or above the delivery block's base. -/
theorem vdl_ge (i q u : Nat) : bsDl sh ≤ vdl sh i q u := Nat.le_add_right _ _

/-- A delivery code lies below the freshness block. -/
theorem vdl_lt_bsFr (i q u : Nat) (hi : i < sh.steps) (hq : q < shS sh) (hu : u < shVal sh) :
    vdl sh i q u < bsFr sh := by
  have h1 : i * shS sh + q < sh.steps * shS sh := scale_lt' hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shVal sh + u < sh.steps * shS sh * shVal sh :=
    horner_lt h1 (shVal_pos sh) hu
  simp only [vdl, bsFr, bsDl, bsEv, bsKn, bsSt, bsPc, szDl, szEv, szKn, szSt, szPc, Nat.zero_add]
  exact Nat.add_lt_add_left h2 _

/-- A freshness code lies at or above the freshness block's base. -/
theorem vfr_ge (i q d : Nat) : bsFr sh ≤ vfr sh i q d := Nat.le_add_right _ _

/-- A freshness code lies below the evaluation block. -/
theorem vfr_lt_bsXe (i q d : Nat) (hi : i < sh.steps) (hq : q < shS sh) (hd : d < shD sh) :
    vfr sh i q d < bsXe sh := by
  have h1 : i * shS sh + q < sh.steps * shS sh := scale_lt' hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shD sh + d < sh.steps * shS sh * shD sh :=
    horner_lt h1 (shD_pos sh) hd
  simp only [vfr, bsXe, bsFr, bsDl, bsEv, bsKn, bsSt, bsPc, szFr, szDl, szEv, szKn, szSt, szPc,
    Nat.zero_add]
  exact Nat.add_lt_add_left h2 _

/-- An evaluation code lies at or above the evaluation block's base. -/
theorem vxe_ge (i q e u : Nat) : bsXe sh ≤ vxe sh i q e u := Nat.le_add_right _ _

/-- An evaluation code lies below the publisher-auxiliary block. -/
theorem vxe_lt_bsTotal (i q e u : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh)
    (hu : u < shVal sh) : vxe sh i q e u < bsTotal sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shE sh + e < (sh.steps + 1) * shS sh * shE sh :=
    horner_lt h1 (shE_pos sh) he
  have h3 : ((i * shS sh + q) * shE sh + e) * shVal sh + u
      < (sh.steps + 1) * shS sh * shE sh * shVal sh := horner_lt h2 (shVal_pos sh) hu
  simp only [vxe, bsTotal, bsXe, bsFr, bsDl, bsEv, bsKn, bsSt, bsPc, szXe, szFr, szDl, szEv,
    szKn, szSt, szPc, Nat.zero_add]
  exact Nat.add_lt_add_left h3 _

/-- A publisher-auxiliary code lies at or above the main blocks' base. -/
theorem vpb_ge (i q c u : Nat) : bsTotal sh ≤ vpb sh i q c u := by
  rw [vpb, Nat.add_assoc]
  exact Nat.le_trans (bsTotal_le_bsAfterAux sh) (Nat.le_add_right _ _)

/-- A publisher-auxiliary code lies below the leak-auxiliary block. -/
theorem vpb_lt_bsAu (i q c u : Nat) (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh)
    (hu : u < shVal sh) : vpb sh i q c u < bsAu sh := by
  have h1 : i * shS sh + q < sh.steps * shS sh := scale_lt' hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shPc sh + c < sh.steps * shS sh * shPc sh :=
    horner_lt h1 (shPc_pos sh) hc
  have h3 : ((i * shS sh + q) * shPc sh + c) * shVal sh + u
      < sh.steps * shS sh * shPc sh * shVal sh := horner_lt h2 (shVal_pos sh) hu
  simp only [vpb, bsAu, bsTotal, bsXe, bsFr, bsDl, bsEv, bsKn, bsSt, bsPc, szPb, szXe, szFr,
    szDl, szEv, szKn, szSt, szPc, Nat.zero_add]
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left h3 _

/-- A leak-auxiliary code lies at or above the leak block's base. -/
theorem vau_ge (i q x u : Nat) : bsAu sh ≤ vau sh i q x u :=
  Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- A leak-auxiliary code lies below the total number of variables. -/
theorem vau_lt_nVarsAll (i q x u : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh)
    (hu : u < shVal sh) : vau sh i q x u < nVarsAll sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shV sh + x < (sh.steps + 1) * shS sh * shV sh :=
    horner_lt h1 (shV_pos sh) hx
  have h3 : ((i * shS sh + q) * shV sh + x) * shVal sh + u
      < (sh.steps + 1) * shS sh * shV sh * shVal sh := horner_lt h2 (shVal_pos sh) hu
  simp only [vau, nVarsAll, bsAu, bsTotal, bsXe, bsFr, bsDl, bsEv, bsKn, bsSt, bsPc, szAu,
    szPb, szXe, szFr, szDl, szEv, szKn, szSt, szPc, Nat.zero_add]
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left h3 _

end Ranges

/-! ### Full injectivity of the positional codes

The one-argument injectivity lemmas of ProtSat.Encode are not enough for the cascade: when a
variable is recognised as belonging to a family, *all* of the family's indices have to be
recovered, not just the last one.  The lemmas below do that, two and three coordinates at a
time, with ProtSat.Encode.lin_inj2 and ProtSat.Encode.lin_inj3. -/

/-- The program-counter code determines step, session and counter. -/
theorem vpc_inj_full {sh : Shape} {i q c i' q' c' : Nat} (hq : q < shS sh) (hq' : q' < shS sh)
    (hc : c < shPc sh) (hc' : c' < shPc sh)
    (h : vpc sh i q c = vpc sh i' q' c') : i = i' ∧ q = q' ∧ c = c' := by
  unfold vpc bsPc at h
  obtain ⟨h1, hc2⟩ := lin_inj2 (shPc_pos sh) hc hc' (Nat.add_left_cancel h)
  obtain ⟨h2, h3⟩ := lin_inj2 (shS_pos sh) hq hq' h1
  exact ⟨h2, h3, hc2⟩

/-- The store code determines step, session, slot and value. -/
theorem vst_inj_full {sh : Shape} {i q x u i' q' x' u' : Nat} (hq : q < shS sh)
    (hq' : q' < shS sh) (hx : x < shV sh) (hx' : x' < shV sh)
    (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vst sh i q x u = vst sh i' q' x' u') : i = i' ∧ q = q' ∧ x = x' ∧ u = u' := by
  unfold vst bsSt at h
  obtain ⟨h1, hu2⟩ := lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)
  obtain ⟨h2, h3, h4⟩ := lin_inj3 (shS_pos sh) (shV_pos sh) hq hq' hx hx' h1
  exact ⟨h2, h3, h4, hu2⟩

/-- The knowledge code determines step and value. -/
theorem vkn_inj_full {sh : Shape} {i u i' u' : Nat} (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vkn sh i u = vkn sh i' u') : i = i' ∧ u = u' := by
  unfold vkn bsKn at h
  exact lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)

/-- The event code determines step and alternative. -/
theorem vev_inj_full {sh : Shape} {i k i' k' : Nat} (hk : k < shEv sh) (hk' : k' < shEv sh)
    (h : vev sh i k = vev sh i' k') : i = i' ∧ k = k' := by
  unfold vev bsEv at h
  exact lin_inj2 (shEv_pos sh) hk hk' (Nat.add_left_cancel h)

/-- The delivery code determines step, session and value. -/
theorem vdl_inj_full {sh : Shape} {i q u i' q' u' : Nat} (hq : q < shS sh) (hq' : q' < shS sh)
    (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vdl sh i q u = vdl sh i' q' u') : i = i' ∧ q = q' ∧ u = u' := by
  unfold vdl bsDl at h
  obtain ⟨h1, hu2⟩ := lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)
  obtain ⟨h2, h3⟩ := lin_inj2 (shS_pos sh) hq hq' h1
  exact ⟨h2, h3, hu2⟩

/-- The freshness code determines step, session and nonce. -/
theorem vfr_inj_full {sh : Shape} {i q d i' q' d' : Nat} (hq : q < shS sh) (hq' : q' < shS sh)
    (hd : d < shD sh) (hd' : d' < shD sh)
    (h : vfr sh i q d = vfr sh i' q' d') : i = i' ∧ q = q' ∧ d = d' := by
  unfold vfr bsFr at h
  obtain ⟨h1, hd2⟩ := lin_inj2 (shD_pos sh) hd hd' (Nat.add_left_cancel h)
  obtain ⟨h2, h3⟩ := lin_inj2 (shS_pos sh) hq hq' h1
  exact ⟨h2, h3, hd2⟩

/-- The evaluation code determines step, session, table entry and value. -/
theorem vxe_inj_full {sh : Shape} {i q e u i' q' e' u' : Nat} (hq : q < shS sh)
    (hq' : q' < shS sh) (he : e < shE sh) (he' : e' < shE sh)
    (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vxe sh i q e u = vxe sh i' q' e' u') : i = i' ∧ q = q' ∧ e = e' ∧ u = u' := by
  unfold vxe bsXe at h
  obtain ⟨h1, hu2⟩ := lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)
  obtain ⟨h2, h3, h4⟩ := lin_inj3 (shS_pos sh) (shE_pos sh) hq hq' he he' h1
  exact ⟨h2, h3, h4, hu2⟩

/-- The publisher-auxiliary code determines step, session, counter and value. -/
theorem vpb_inj_full {sh : Shape} {i q c u i' q' c' u' : Nat} (hq : q < shS sh)
    (hq' : q' < shS sh) (hc : c < shPc sh) (hc' : c' < shPc sh)
    (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vpb sh i q c u = vpb sh i' q' c' u') : i = i' ∧ q = q' ∧ c = c' ∧ u = u' := by
  unfold vpb at h
  -- vpb is bsAfterAux + (A * shVal + u); right-associate so that the common prefix is a
  -- single syntactic argument of +, then cancel it.
  simp only [Nat.add_assoc] at h
  obtain ⟨h1, hu2⟩ := lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)
  obtain ⟨h2, h3, h4⟩ := lin_inj3 (shS_pos sh) (shPc_pos sh) hq hq' hc hc' h1
  exact ⟨h2, h3, h4, hu2⟩

/-- The leak-auxiliary code determines step, session, slot and value. -/
theorem vau_inj_full {sh : Shape} {i q x u i' q' x' u' : Nat} (hq : q < shS sh)
    (hq' : q' < shS sh) (hx : x < shV sh) (hx' : x' < shV sh)
    (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vau sh i q x u = vau sh i' q' x' u') : i = i' ∧ q = q' ∧ x = x' ∧ u = u' := by
  unfold vau bsAu at h
  simp only [Nat.add_assoc] at h
  obtain ⟨h1, hu2⟩ := lin_inj2 (shVal_pos sh) hu hu'
    (Nat.add_left_cancel (Nat.add_left_cancel h))
  obtain ⟨h2, h3, h4⟩ := lin_inj3 (shS_pos sh) (shV_pos sh) hq hq' hx hx' h1
  exact ⟨h2, h3, h4, hu2⟩

end ProtSat.Complete