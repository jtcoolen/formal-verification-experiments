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

/-! ### The readers: what the run says about each variable family

The assignment of specification 8B is the characteristic function of the run: a variable is
true exactly when the semantic fact it names holds in the run.  Each reader below states, for
one family, the index the run selects; all of them take the same four explicit parameters so
that the characterisation lemmas are uniform. -/

/-- The program counter of session q at step i, as the run records it. -/
def rdPc (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i q : Nat) : Nat :=
  pcOf (cfg i) q

/-- The value number held by slot x of session q at step i. -/
def rdSt (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i q x : Nat) : Nat :=
  uIdx sh (readVar x (storeOf (cfg i) q))

/-- The value number of table entry e in session q at step i. -/
def rdXe (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i q e : Nat) : Nat :=
  uIdx sh (Expr.eval (eAt P e) (storeOf (cfg i) q))

/-- The message the event delivers to session q at step i, as a value number: the delivered
message when the event acts on q, and unset otherwise. -/
def rdDl (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i q : Nat) : Nat :=
  uIdx sh (match ev i with | Ev.act q' m _ => if q' = q then some m else none | _ => none)

/-- The nonce the event lets session q generate at step i, as an index of the nonce domain;
out of range when the event does not act on q. -/
def rdFr (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i q : Nat) : Nat :=
  match ev i with
  | Ev.act q' _ d => if q' = q then ixOf d sh.D else shD sh
  | _ => shD sh

/-- Is the instance numbered n a universe instance concluding u whose premises are all in K? -/
def dedInstOk (sh : Shape) (K : List Term) (n u : Nat) : Bool :=
  match instAt sh n with
  | some ins =>
      decide (ins.concl = u) &&
        (ins.prem.all fun p => match valAt sh p with
          | some t => decide (t ∈ K)
          | none => false)
  | none => false

/-- The first universe deduction instance whose conclusion is the universe message numbered u
and whose premises are all known in K; 0 if there is none, which the boundedness hypothesis
rules out for a legal deduction step. -/
def dedIx (sh : Shape) (K : List Term) (u : Nat) : Nat :=
  match (List.range (nInst sh)).find? (fun n => dedInstOk sh K n u) with
  | some n => n
  | none => 0

/-- The event alternative taken at step i: 0 for idle, 1+q for a session action, and for a
deduction the number of the universe instance that produces the learned message. -/
def rdEv (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i : Nat) : Nat :=
  match e : ev i with
  | Ev.idle => 0
  | Ev.act q _ _ => 1 + q
  | Ev.ded t => 1 + shS sh + dedIx sh ((cfg i).kn) (uIdx sh (some t))

/-- The fifteen block tests of the characteristic assignment: each is a bounded search over one
family's own index ranges, pinning the variable by the injective positional code. -/
def asgPc (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shPc sh)).any fun c => v = vpc sh i q c && rdPc sh P cfg ev i q = c

def asgSt (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shV sh)).any fun x =>
        (List.range (shVal sh)).any fun u => v = vst sh i q x u && rdSt sh P cfg ev i q x = u

def knHolds (sh : Shape) (cfg : Nat -> Cfg) (i u : Nat) : Bool :=
  match valAt sh u with
  | some t => decide (t ∈ (cfg i).kn)
  | none => false

def asgKn (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shVal sh)).any fun u => v = vkn sh i u && knHolds sh cfg i u

def asgEv (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shEv sh)).any fun k => v = vev sh i k && rdEv sh P cfg ev i = k

def asgDl (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shVal sh)).any fun u => v = vdl sh i q u && rdDl sh P cfg ev i q = u

def asgFr (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shD sh)).any fun d => v = vfr sh i q d && rdFr sh P cfg ev i q = d

def asgXe (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shE sh)).any fun e =>
        (List.range (shVal sh)).any fun u => v = vxe sh i q e u && rdXe sh P cfg ev i q e = u

/-- Flag blocks: the flag j of a group is true when the chosen index is at or before j, which
is the meaning ProtSat.atMostOneSeq gives its auxiliary variables. -/
def asgApc (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shPc sh)).any fun j => v = apc sh i q j && rdPc sh P cfg ev i q <= j

def asgAst (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shV sh)).any fun x =>
        (List.range (shVal sh)).any fun j => v = ast sh i q x j && rdSt sh P cfg ev i q x <= j

def asgAxe (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shE sh)).any fun e =>
        (List.range (shVal sh)).any fun j => v = axe sh i q e j && rdXe sh P cfg ev i q e <= j

def asgAev (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shEv sh)).any fun j => v = aev sh i j && rdEv sh P cfg ev i <= j

def asgAdl (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shVal sh)).any fun j => v = adl sh i q j && rdDl sh P cfg ev i q <= j

def asgAfr (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shD sh)).any fun j => v = afr sh i q j && rdFr sh P cfg ev i q <= j

/-- The publisher conjunction: session q acts at step i with program counter c and the value it
sends is u. -/
def asgPb (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range sh.steps).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shPc sh)).any fun c =>
        (List.range (shVal sh)).any fun u =>
          v = vpb sh i q c u &&
            match ev i, P.actionAt q c with
            | Ev.act q' _ _, some (Action.send _ e) =>
                decide (q' = q && rdPc sh P cfg ev i q = c &&
                  rdXe sh P cfg ev i q (eIdx P e) = u)
            | _, _ => false

/-- The leak conjunction: session q holds the message numbered u at step i and the attacker
knows it. -/
def asgAu (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  (List.range (sh.steps + 1)).any fun i =>
    (List.range (shS sh)).any fun q =>
      (List.range (shV sh)).any fun x =>
        (List.range (shVal sh)).any fun u =>
          v = vau sh i q x u &&
            match valAt sh u with
            | some t => decide (rdSt sh P cfg ev i q x = u && t ∈ (cfg i).kn)
            | none => false

/-- **The characteristic assignment of the run** (specification 8B).  A variable is true
exactly when the fact it names holds in the run; the fifteen blocks are dispatched by the
layout order, so at most one test is ever applied and each test is a bounded search over that
family's own index ranges.  Everything is a closed computation on lists: no choice, no
partiality. -/
def assignOf (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) : Assignment := fun v =>
  if v < bsSt sh then asgPc sh P cfg ev v
  else if v < bsKn sh then asgSt sh P cfg ev v
  else if v < bsEv sh then asgKn sh P cfg ev v
  else if v < bsDl sh then asgEv sh P cfg ev v
  else if v < bsFr sh then asgDl sh P cfg ev v
  else if v < bsXe sh then asgFr sh P cfg ev v
  else if v < bsTotal sh then asgXe sh P cfg ev v
  else if v < bsAst sh then asgApc sh P cfg ev v
  else if v < bsAxe sh then asgAst sh P cfg ev v
  else if v < bsAev sh then asgAxe sh P cfg ev v
  else if v < bsAdl sh then asgAev sh P cfg ev v
  else if v < bsAfr sh then asgAdl sh P cfg ev v
  else if v < bsAfterAux sh then asgAfr sh P cfg ev v
  else if v < bsAu sh then asgPb sh P cfg ev v
  else asgAu sh P cfg ev v

/-! ### Block bounds for the auxiliary flag families

The cascade in ProtSat.Complete.assignOf dispatches on these inequalities: the code of an
in-range family member lies inside its own block, so exactly one of the fifteen tests is
applied and the other fourteen are never evaluated. -/

section AuxRanges
variable (sh : Shape)

/-- Each auxiliary block occupies its own interval: the code of an in-range member is at least
the block's base and less than the next block's base.  The proofs unfold only the code, the
block base and the block size, so the arithmetic stays local. -/
theorem apc_ge : bsApc sh ≤ apc sh i q j := by
  unfold apc bsApc
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem apc_lt_bsAst (i q j : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (hj : j < shPc sh) :
    apc sh i q j < bsAst sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shPc sh + j < (sh.steps + 1) * shS sh * shPc sh :=
    horner_lt h1 (shPc_pos sh) hj
  simp only [apc, bsAst, bsApc, szApc, Nat.add_assoc]
  exact Nat.add_lt_add_left h2 _

theorem ast_ge : bsAst sh ≤ ast sh i q x j := by
  unfold ast bsAst
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem ast_lt_bsAxe (i q x j : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh)
    (hj : j < shVal sh) : ast sh i q x j < bsAxe sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shV sh + x < (sh.steps + 1) * shS sh * shV sh :=
    horner_lt h1 (shV_pos sh) hx
  have h3 : ((i * shS sh + q) * shV sh + x) * shVal sh + j
      < (sh.steps + 1) * shS sh * shV sh * shVal sh := horner_lt h2 (shVal_pos sh) hj
  simp only [ast, bsAxe, bsAst, szAst, Nat.add_assoc]
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h3 _) _

theorem axe_ge : bsAxe sh ≤ axe sh i q e j := by
  unfold axe bsAxe
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem axe_lt_bsAev (i q e j : Nat) (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh)
    (hj : j < shVal sh) : axe sh i q e j < bsAev sh := by
  have h1 : i * shS sh + q < (sh.steps + 1) * shS sh := scale_lt hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shE sh + e < (sh.steps + 1) * shS sh * shE sh :=
    horner_lt h1 (shE_pos sh) he
  have h3 : ((i * shS sh + q) * shE sh + e) * shVal sh + j
      < (sh.steps + 1) * shS sh * shE sh * shVal sh := horner_lt h2 (shVal_pos sh) hj
  simp only [axe, bsAev, bsAxe, szAxe, Nat.add_assoc]
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h3 _) _

theorem aev_ge : bsAev sh ≤ aev sh i j := by
  unfold aev bsAev
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem aev_lt_bsAdl (i j : Nat) (hi : i < sh.steps) (hj : j < shEv sh) :
    aev sh i j < bsAdl sh := by
  have h1 : i * shEv sh + j < (sh.steps + 1) * shEv sh :=
    scale_lt (Nat.le_of_lt hi) (shEv_pos sh) hj
  simp only [aev, bsAdl, bsAev, szAev, Nat.add_assoc]
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h1 _) _

theorem adl_ge : bsAdl sh ≤ adl sh i q j := by
  unfold adl bsAdl
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem adl_lt_bsAfr (i q j : Nat) (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shVal sh) :
    adl sh i q j < bsAfr sh := by
  have h1 : i * shS sh + q < sh.steps * shS sh := scale_lt' hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shVal sh + j < sh.steps * shS sh * shVal sh :=
    horner_lt h1 (shVal_pos sh) hj
  simp only [adl, bsAfr, bsAdl, szAdl, Nat.add_assoc]
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h2 _) _

theorem afr_ge : bsAfr sh ≤ afr sh i q j := by
  unfold afr bsAfr
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem afr_lt_bsAfterAux (i q j : Nat) (hi : i < sh.steps) (hq : q < shS sh)
    (hj : j < shD sh) : afr sh i q j < bsAfterAux sh := by
  have h1 : i * shS sh + q < sh.steps * shS sh := scale_lt' hi (shS_pos sh) hq
  have h2 : (i * shS sh + q) * shD sh + j < sh.steps * shS sh * shD sh :=
    horner_lt h1 (shD_pos sh) hj
  simp only [afr, bsAfterAux, bsAfr, szAfr, Nat.add_assoc]
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h2 _) _

/-- The publisher block starts after every auxiliary block, and the leak block after it. -/
theorem bsAfterAux_le_vpb : bsAfterAux sh ≤ vpb sh i q c u := by
  unfold vpb
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem bsAu_le_vau : bsAu sh ≤ vau sh i q x u := by
  unfold vau bsAu
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
theorem vpb_lt_bsAu' (i q c u : Nat) (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh)
    (hu : u < shVal sh) : vpb sh i q c u < bsAu sh :=
  vpb_lt_bsAu sh i q c u hi hq hc hu

end AuxRanges

/-! ### The characterisation lemmas

For each family: the assignment applied to the code of an in-range fact is the truth value of
that fact in the run.  Two ingredients: the cascade dispatch (the block bounds above) and the
pinned search (the injectivity of the positional codes). -/

section Charac
variable (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev)

/-- The block bases are non-decreasing along the layout: the cascade never dispatches a code
to an earlier family test. -/
theorem bsSt_le_bsKn : bsSt sh ≤ bsKn sh := by
  unfold bsKn; exact Nat.le_add_right _ _
theorem bsKn_le_bsEv : bsKn sh ≤ bsEv sh := by
  unfold bsEv; exact Nat.le_add_right _ _
theorem bsEv_le_bsDl : bsEv sh ≤ bsDl sh := by
  unfold bsDl; exact Nat.le_add_right _ _
theorem bsDl_le_bsFr : bsDl sh ≤ bsFr sh := by
  unfold bsFr; exact Nat.le_add_right _ _
theorem bsFr_le_bsXe : bsFr sh ≤ bsXe sh := by
  unfold bsXe; exact Nat.le_add_right _ _
theorem bsXe_le_bsTotal : bsXe sh ≤ bsTotal sh := by
  unfold bsTotal; exact Nat.le_add_right _ _
theorem bsTotal_le_bsAst : bsTotal sh ≤ bsAst sh := by
  unfold bsAst bsApc; exact Nat.le_add_right _ _
theorem bsSt_le_bsEv : bsSt sh ≤ bsEv sh := Nat.le_trans (bsSt_le_bsKn sh) (bsKn_le_bsEv sh)
theorem bsSt_le_bsDl : bsSt sh ≤ bsDl sh := Nat.le_trans (bsSt_le_bsEv sh) (bsEv_le_bsDl sh)
theorem bsKn_le_bsDl : bsKn sh ≤ bsDl sh := Nat.le_trans (bsKn_le_bsEv sh) (bsEv_le_bsDl sh)
theorem bsSt_le_bsFr : bsSt sh ≤ bsFr sh := Nat.le_trans (bsSt_le_bsDl sh) (bsDl_le_bsFr sh)
theorem bsKn_le_bsFr : bsKn sh ≤ bsFr sh := Nat.le_trans (bsKn_le_bsDl sh) (bsDl_le_bsFr sh)
theorem bsEv_le_bsFr : bsEv sh ≤ bsFr sh := Nat.le_trans (bsEv_le_bsDl sh) (bsDl_le_bsFr sh)
theorem bsSt_le_bsXe : bsSt sh ≤ bsXe sh := Nat.le_trans (bsSt_le_bsFr sh) (bsFr_le_bsXe sh)
theorem bsKn_le_bsXe : bsKn sh ≤ bsXe sh := Nat.le_trans (bsKn_le_bsFr sh) (bsFr_le_bsXe sh)
theorem bsEv_le_bsXe : bsEv sh ≤ bsXe sh := Nat.le_trans (bsEv_le_bsFr sh) (bsFr_le_bsXe sh)
theorem bsDl_le_bsXe : bsDl sh ≤ bsXe sh := Nat.le_trans (bsDl_le_bsFr sh) (bsFr_le_bsXe sh)
theorem bsSt_le_bsTotal : bsSt sh ≤ bsTotal sh := Nat.le_trans (bsSt_le_bsXe sh) (bsXe_le_bsTotal sh)
theorem bsKn_le_bsTotal : bsKn sh ≤ bsTotal sh := Nat.le_trans (bsKn_le_bsXe sh) (bsXe_le_bsTotal sh)
theorem bsEv_le_bsTotal : bsEv sh ≤ bsTotal sh := Nat.le_trans (bsEv_le_bsXe sh) (bsXe_le_bsTotal sh)
theorem bsDl_le_bsTotal : bsDl sh ≤ bsTotal sh := Nat.le_trans (bsDl_le_bsXe sh) (bsXe_le_bsTotal sh)
theorem bsFr_le_bsTotal : bsFr sh ≤ bsTotal sh := Nat.le_trans (bsFr_le_bsXe sh) (bsXe_le_bsTotal sh)
theorem bsSt_le_bsAst : bsSt sh ≤ bsAst sh := Nat.le_trans (bsSt_le_bsTotal sh) (bsTotal_le_bsAst sh)
theorem bsKn_le_bsAst : bsKn sh ≤ bsAst sh := Nat.le_trans (bsKn_le_bsTotal sh) (bsTotal_le_bsAst sh)
theorem bsEv_le_bsAst : bsEv sh ≤ bsAst sh := Nat.le_trans (bsEv_le_bsTotal sh) (bsTotal_le_bsAst sh)
theorem bsDl_le_bsAst : bsDl sh ≤ bsAst sh := Nat.le_trans (bsDl_le_bsTotal sh) (bsTotal_le_bsAst sh)
theorem bsFr_le_bsAst : bsFr sh ≤ bsAst sh := Nat.le_trans (bsFr_le_bsTotal sh) (bsTotal_le_bsAst sh)
theorem bsXe_le_bsAst : bsXe sh ≤ bsAst sh := Nat.le_trans (bsXe_le_bsTotal sh) (bsTotal_le_bsAst sh)

/-- **The pinned search.**  For each family, the block test applied to the code of an
in-range fact reduces to the truth value of that fact: the positional code is injective, so
exactly one index tuple in the search can match the variable, and the search collapses. -/
theorem asgPc_val (hi : i ≤ sh.steps) (hq : q < shS sh) (hc : c < shPc sh) :
    asgPc sh P cfg ev (vpc sh i q c) = decide (rdPc sh P cfg ev i q = c) := by
  have hiff : (asgPc sh P cfg ev (vpc sh i q c) = true) <-> rdPc sh P cfg ev i q = c := by
    constructor
    · intro h
      rw [asgPc] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨c', hc', h4⟩ := h3
      rw [Bool.and_eq_true] at h4
      obtain ⟨heq, hrd⟩ := h4
      obtain ⟨rfl, rfl, rfl⟩ := vpc_inj_full hq (List.mem_range.mp hq') hc
        (List.mem_range.mp hc') (of_decide_eq_true heq)
      · exact of_decide_eq_true hrd
    · intro h
      rw [asgPc]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      simp [h]
  by_cases hd : rdPc sh P cfg ev i q = c
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgPc sh P cfg ev (vpc sh i q c)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgSt_val (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hu : u < shVal sh) :
    asgSt sh P cfg ev (vst sh i q x u) = decide (rdSt sh P cfg ev i q x = u) := by
  have hiff : (asgSt sh P cfg ev (vst sh i q x u) = true) <-> rdSt sh P cfg ev i q x = u := by
    constructor
    · intro h
      rw [asgSt] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨x', hx', h4⟩ := h3
      rw [List.any_eq_true] at h4
      obtain ⟨u', hu', h5⟩ := h4
      rw [Bool.and_eq_true] at h5
      obtain ⟨heq, hrd⟩ := h5
      obtain ⟨rfl, rfl, rfl, rfl⟩ := vst_inj_full hq (List.mem_range.mp hq') hx
        (List.mem_range.mp hx') hu (List.mem_range.mp hu') (of_decide_eq_true heq)
      · exact of_decide_eq_true hrd
    · intro h
      rw [asgSt]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
      refine List.any_eq_true.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
      simp [h]
  by_cases hd : rdSt sh P cfg ev i q x = u
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgSt sh P cfg ev (vst sh i q x u)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgKn_val (hi : i ≤ sh.steps) (hu : u < shVal sh) :
    asgKn sh P cfg ev (vkn sh i u) = knHolds sh cfg i u := by
  have hiff : (asgKn sh P cfg ev (vkn sh i u) = true) <-> knHolds sh cfg i u := by
    constructor
    · intro h
      rw [asgKn] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨u', hu', h3⟩ := h2
      rw [Bool.and_eq_true] at h3
      obtain ⟨heq, hmem⟩ := h3
      obtain ⟨rfl, rfl⟩ := vkn_inj_full hu (List.mem_range.mp hu') (of_decide_eq_true heq)
      · exact hmem
    · intro h
      rw [asgKn]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
      simp [h]
  by_cases hd : knHolds sh cfg i u
  · exact (hiff.mpr hd).trans hd.symm
  · cases h2 : asgKn sh P cfg ev (vkn sh i u)
    · cases h3 : knHolds sh cfg i u
      · rfl
      · exact absurd h3 hd
    · exact (hiff.mp h2).symm

theorem asgEv_val (hi : i < sh.steps) (hk : k < shEv sh) :
    asgEv sh P cfg ev (vev sh i k) = decide (rdEv sh P cfg ev i = k) := by
  have hiff : (asgEv sh P cfg ev (vev sh i k) = true) <-> rdEv sh P cfg ev i = k := by
    constructor
    · intro h
      rw [asgEv] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨k', hk', h3⟩ := h2
      rw [Bool.and_eq_true] at h3
      obtain ⟨heq, hrd⟩ := h3
      obtain ⟨rfl, rfl⟩ := vev_inj_full hk (List.mem_range.mp hk') (of_decide_eq_true heq)
      · exact of_decide_eq_true hrd
    · intro h
      rw [asgEv]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      refine List.any_eq_true.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
      simp [h]
  by_cases hd : rdEv sh P cfg ev i = k
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgEv sh P cfg ev (vev sh i k)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgDl_val (hi : i < sh.steps) (hq : q < shS sh) (hu : u < shVal sh) :
    asgDl sh P cfg ev (vdl sh i q u) = decide (rdDl sh P cfg ev i q = u) := by
  have hiff : (asgDl sh P cfg ev (vdl sh i q u) = true) <-> rdDl sh P cfg ev i q = u := by
    constructor
    · intro h
      rw [asgDl] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨u', hu', h4⟩ := h3
      rw [Bool.and_eq_true] at h4
      obtain ⟨heq, hrd⟩ := h4
      obtain ⟨rfl, rfl, rfl⟩ := vdl_inj_full hq (List.mem_range.mp hq') hu
        (List.mem_range.mp hu') (of_decide_eq_true heq)
      · exact of_decide_eq_true hrd
    · intro h
      rw [asgDl]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
      simp [h]
  by_cases hd : rdDl sh P cfg ev i q = u
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgDl sh P cfg ev (vdl sh i q u)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgFr_val (hi : i < sh.steps) (hq : q < shS sh) (hd : d < shD sh) :
    asgFr sh P cfg ev (vfr sh i q d) = decide (rdFr sh P cfg ev i q = d) := by
  have hiff : (asgFr sh P cfg ev (vfr sh i q d) = true) <-> rdFr sh P cfg ev i q = d := by
    constructor
    · intro h
      rw [asgFr] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨d', hd', h4⟩ := h3
      rw [Bool.and_eq_true] at h4
      obtain ⟨heq, hrd⟩ := h4
      obtain ⟨rfl, rfl, rfl⟩ := vfr_inj_full hq (List.mem_range.mp hq') hd
        (List.mem_range.mp hd') (of_decide_eq_true heq)
      · exact of_decide_eq_true hrd
    · intro h
      rw [asgFr]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨d, List.mem_range.mpr hd, ?_⟩
      simp [h]
  by_cases hd : rdFr sh P cfg ev i q = d
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgFr sh P cfg ev (vfr sh i q d)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgXe_val (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hu : u < shVal sh) :
    asgXe sh P cfg ev (vxe sh i q e u) = decide (rdXe sh P cfg ev i q e = u) := by
  have hiff : (asgXe sh P cfg ev (vxe sh i q e u) = true) <-> rdXe sh P cfg ev i q e = u := by
    constructor
    · intro h
      rw [asgXe] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨e', he', h4⟩ := h3
      rw [List.any_eq_true] at h4
      obtain ⟨u', hu', h5⟩ := h4
      rw [Bool.and_eq_true] at h5
      obtain ⟨heq, hrd⟩ := h5
      obtain ⟨rfl, rfl, rfl, rfl⟩ := vxe_inj_full hq (List.mem_range.mp hq') he
        (List.mem_range.mp he') hu (List.mem_range.mp hu') (of_decide_eq_true heq)
      · exact of_decide_eq_true hrd
    · intro h
      rw [asgXe]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨e, List.mem_range.mpr he, ?_⟩
      refine List.any_eq_true.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
      simp [h]
  by_cases hd : rdXe sh P cfg ev i q e = u
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgXe sh P cfg ev (vxe sh i q e u)
    · rfl
    · exact absurd (hiff.mp h2) hd

/-- The cascade dispatches an in-range code to its own family test: the code is at least
its own block's base (so every earlier test is refuted) and below the next block's base (so
its own test is chosen). -/
theorem asg_branch_pc (hi : i ≤ sh.steps) (hq : q < shS sh) (hc : c < shPc sh) :
    assignOf sh P cfg ev (vpc sh i q c) = asgPc sh P cfg ev (vpc sh i q c) := by
  have h : vpc sh i q c < bsSt sh := vpc_lt_bsSt sh i q c hi hq hc
  dsimp only [assignOf]
  rw [if_pos h]

theorem asg_branch_st (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vst sh i q x u) = asgSt sh P cfg ev (vst sh i q x u) := by
  have hge : bsSt sh ≤ vst sh i q x u := vst_ge sh i q x u
  have hlt : vst sh i q x u < bsKn sh := vst_lt_bsKn sh i q x u hi hq hx hu
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_kn (hi : i ≤ sh.steps) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vkn sh i u) = asgKn sh P cfg ev (vkn sh i u) := by
  have hge : bsKn sh ≤ vkn sh i u := vkn_ge sh i u
  have hlt : vkn sh i u < bsEv sh := vkn_lt_bsEv sh i u hi hu
  have hc : bsSt sh ≤ bsKn sh := bsSt_le_bsKn sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_ev (hi : i < sh.steps) (hk : k < shEv sh) :
    assignOf sh P cfg ev (vev sh i k) = asgEv sh P cfg ev (vev sh i k) := by
  have hge : bsEv sh ≤ vev sh i k := vev_ge sh i k
  have hlt : vev sh i k < bsDl sh := vev_lt_bsDl sh i k hi hk
  have hc1 : bsSt sh ≤ bsEv sh := bsSt_le_bsEv sh
  have hc2 : bsKn sh ≤ bsEv sh := bsKn_le_bsEv sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc1 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc2 hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_dl (hi : i < sh.steps) (hq : q < shS sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vdl sh i q u) = asgDl sh P cfg ev (vdl sh i q u) := by
  have hge : bsDl sh ≤ vdl sh i q u := vdl_ge sh i q u
  have hlt : vdl sh i q u < bsFr sh := vdl_lt_bsFr sh i q u hi hq hu
  have hc1 : bsSt sh ≤ bsDl sh := bsSt_le_bsDl sh
  have hc2 : bsKn sh ≤ bsDl sh := bsKn_le_bsDl sh
  have hc3 : bsEv sh ≤ bsDl sh := bsEv_le_bsDl sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc1 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc2 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc3 hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_fr (hi : i < sh.steps) (hq : q < shS sh) (hd : d < shD sh) :
    assignOf sh P cfg ev (vfr sh i q d) = asgFr sh P cfg ev (vfr sh i q d) := by
  have hge : bsFr sh ≤ vfr sh i q d := vfr_ge sh i q d
  have hlt : vfr sh i q d < bsXe sh := vfr_lt_bsXe sh i q d hi hq hd
  have hc1 : bsSt sh ≤ bsFr sh := bsSt_le_bsFr sh
  have hc2 : bsKn sh ≤ bsFr sh := bsKn_le_bsFr sh
  have hc3 : bsEv sh ≤ bsFr sh := bsEv_le_bsFr sh
  have hc4 : bsDl sh ≤ bsFr sh := bsDl_le_bsFr sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc1 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc2 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc3 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc4 hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_xe (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vxe sh i q e u) = asgXe sh P cfg ev (vxe sh i q e u) := by
  have hge : bsXe sh ≤ vxe sh i q e u := vxe_ge sh i q e u
  have hlt : vxe sh i q e u < bsTotal sh := vxe_lt_bsTotal sh i q e u hi hq he hu
  have hc1 : bsSt sh ≤ bsXe sh := bsSt_le_bsXe sh
  have hc2 : bsKn sh ≤ bsXe sh := bsKn_le_bsXe sh
  have hc3 : bsEv sh ≤ bsXe sh := bsEv_le_bsXe sh
  have hc4 : bsDl sh ≤ bsXe sh := bsDl_le_bsXe sh
  have hc5 : bsFr sh ≤ bsXe sh := bsFr_le_bsXe sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc1 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc2 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc3 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc4 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc5 hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_apc (hi : i ≤ sh.steps) (hq : q < shS sh) (hj : j < shPc sh) :
    assignOf sh P cfg ev (apc sh i q j) = asgApc sh P cfg ev (apc sh i q j) := by
  have hge : bsTotal sh ≤ apc sh i q j := apc_ge sh
  have hlt : apc sh i q j < bsAst sh := apc_lt_bsAst sh i q j hi hq hj
  have hc1 : bsSt sh ≤ bsTotal sh := bsSt_le_bsTotal sh
  have hc2 : bsKn sh ≤ bsTotal sh := bsKn_le_bsTotal sh
  have hc3 : bsEv sh ≤ bsTotal sh := bsEv_le_bsTotal sh
  have hc4 : bsDl sh ≤ bsTotal sh := bsDl_le_bsTotal sh
  have hc5 : bsFr sh ≤ bsTotal sh := bsFr_le_bsTotal sh
  have hc6 : bsXe sh ≤ bsTotal sh := bsXe_le_bsTotal sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc1 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc2 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc3 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc4 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc5 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc6 hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

theorem asg_branch_ast (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hj : j < shVal sh) :
    assignOf sh P cfg ev (ast sh i q x j) = asgAst sh P cfg ev (ast sh i q x j) := by
  have hge : bsAst sh ≤ ast sh i q x j := ast_ge sh
  have hlt : ast sh i q x j < bsAxe sh := ast_lt_bsAxe sh i q x j hi hq hx hj
  have hc1 : bsSt sh ≤ bsAst sh := bsSt_le_bsAst sh
  have hc2 : bsKn sh ≤ bsAst sh := bsKn_le_bsAst sh
  have hc3 : bsEv sh ≤ bsAst sh := bsEv_le_bsAst sh
  have hc4 : bsDl sh ≤ bsAst sh := bsDl_le_bsAst sh
  have hc5 : bsFr sh ≤ bsAst sh := bsFr_le_bsAst sh
  have hc6 : bsXe sh ≤ bsAst sh := bsXe_le_bsAst sh
  have hc7 : bsTotal sh ≤ bsAst sh := bsTotal_le_bsAst sh
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans hc1 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc2 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc3 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc4 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc5 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc6 hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans hc7 hge)), if_neg (Nat.not_lt_of_le hge), if_pos hlt]

/-- The full characterisation of the seven main families. -/
theorem assignOf_pc (hi : i ≤ sh.steps) (hq : q < shS sh) (hc : c < shPc sh) :
    assignOf sh P cfg ev (vpc sh i q c) = decide (rdPc sh P cfg ev i q = c) :=
  by rw [asg_branch_pc sh P cfg ev hi hq hc, asgPc_val sh P cfg ev hi hq hc]

theorem assignOf_st (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vst sh i q x u) = decide (rdSt sh P cfg ev i q x = u) :=
  by rw [asg_branch_st sh P cfg ev hi hq hx hu, asgSt_val sh P cfg ev hi hq hx hu]

theorem assignOf_kn (hi : i ≤ sh.steps) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vkn sh i u) = knHolds sh cfg i u :=
  by rw [asg_branch_kn sh P cfg ev hi hu, asgKn_val sh P cfg ev hi hu]

theorem assignOf_ev (hi : i < sh.steps) (hk : k < shEv sh) :
    assignOf sh P cfg ev (vev sh i k) = decide (rdEv sh P cfg ev i = k) :=
  by rw [asg_branch_ev sh P cfg ev hi hk, asgEv_val sh P cfg ev hi hk]

theorem assignOf_dl (hi : i < sh.steps) (hq : q < shS sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vdl sh i q u) = decide (rdDl sh P cfg ev i q = u) :=
  by rw [asg_branch_dl sh P cfg ev hi hq hu, asgDl_val sh P cfg ev hi hq hu]

theorem assignOf_fr (hi : i < sh.steps) (hq : q < shS sh) (hd : d < shD sh) :
    assignOf sh P cfg ev (vfr sh i q d) = decide (rdFr sh P cfg ev i q = d) :=
  by rw [asg_branch_fr sh P cfg ev hi hq hd, asgFr_val sh P cfg ev hi hq hd]

theorem assignOf_xe (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vxe sh i q e u) = decide (rdXe sh P cfg ev i q e = u) :=
  by rw [asg_branch_xe sh P cfg ev hi hq he hu, asgXe_val sh P cfg ev hi hq he hu]

end Charac




end ProtSat.Complete
