/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.GetD

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
Eight conditions, all of them instances of "the bounds can name what the run does":

1. every message the attacker ever knows is a universe message;
2. every value any session ever stores is a universe message;
3. every session that acts is one the shape instantiates, and both the message delivered to
   it and the nonce it generates belong to the shape;
4. every message the attacker learns in one step is in the universe;
5. every program counter stays below the shape's program-counter stride;
6. every store variable stays below the shape's variable stride;
7. **every protocol expression denotes a universe message, or nothing, in every session store
   of the run.**  This is what makes the Tseitin gates of clause group 4 exact: the value of a
   compound expression is decoded from the values of its children, and \`ProtSat.Encode.uIdx\`
   can only name a value the universe contains.  A finite universe is never closed under the
   protocol's own constructors, so this is a genuine hypothesis about the bounds and not a
   formality: it says the bounds are large enough for the messages the protocol *computes*,
   not only for the ones it exchanges.
8. the run has exactly the sessions the shape instantiates.

These are precisely the conditions under which a finite encoding can represent the run at all
- a run that leaves the universe has no finite name, and a run whose session index is not
instantiated has no event alternative. -/
def RunOK (sh : Shape) (P : Protocol) (cfg : Nat → Cfg) (ev : Nat → Ev) : Prop :=
  (∀ i t, t ∈ (cfg i).kn → t ∈ sh.U) ∧
  (∀ i q v, q < sh.nS1 → v ∈ storeVals (storeOf (cfg i) q) → v ∈ sh.U) ∧
  (∀ i q m d, ev i = Ev.act q m d → q < sh.nS1 ∧ m ∈ sh.U ∧ d ∈ sh.D) ∧
  (∀ i t, ev i = Ev.ded t → t ∈ sh.U) ∧
  (∀ i q, q < sh.nS1 → pcOf (cfg i) q < shPc sh) ∧
  (∀ i q x, q < sh.nS1 → x ∈ (storeOf (cfg i) q).map Prod.fst → x < shV sh) ∧
  (∀ i q e, e ∈ allExprs P → admissible sh (Expr.eval e (storeOf (cfg i) q)) = true) ∧
  (∀ i, (cfg i).sess.length = sh.nS1)

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

/-- The nonce the event lets session q generate at step i, as an index of the nonce domain.
When the event does not act on q the group is unconstrained - every clause that mentions it is
guarded by "q acts" - so the canonical choice is index 0. -/
def rdFr (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (i q : Nat) : Nat :=
  match ev i with
  | Ev.act q' _ d => if q' = q then ixOf d sh.D else 0
  | _ => 0

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




/-! ### Characterisation of the auxiliary flag and conjunction families -/

section CharacAux
variable (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev)

/-- The flag-block characterisations: the flag of position j is true exactly when the chosen
index is at or before j, which is the meaning ProtSat.atMostOneSeq gives its auxiliaries. -/
theorem asgApc_val (hi : i ≤ sh.steps) (hq : q < shS sh) (hj : j < shPc sh) :
    asgApc sh P cfg ev (apc sh i q j) = decide (rdPc sh P cfg ev i q <= j) := by
  have hiff : (asgApc sh P cfg ev (apc sh i q j) = true) <-> rdPc sh P cfg ev i q <= j := by
    constructor
    · intro h
      rw [asgApc] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨j', hj', h4⟩ := h3
      rw [Bool.and_eq_true] at h4
      have h0 := of_decide_eq_true h4.left
      unfold apc at h0
      rw [Nat.add_assoc, Nat.add_assoc] at h0
      obtain ⟨hA, hj2⟩ := lin_inj2 (shPc_pos sh) (by omega : j < shPc sh)
        (List.mem_range.mp hj') (Nat.add_left_cancel h0)
      obtain ⟨rfl, rfl⟩ := lin_inj2 (shS_pos sh) hq (List.mem_range.mp hq') hA
      subst hj2
      exact of_decide_eq_true h4.right
    · intro h
      rw [asgApc]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simp [h]
  by_cases hd : rdPc sh P cfg ev i q <= j
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgApc sh P cfg ev (apc sh i q j)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgAst_val (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hj : j < shVal sh) :
    asgAst sh P cfg ev (ast sh i q x j) = decide (rdSt sh P cfg ev i q x <= j) := by
  have hiff : (asgAst sh P cfg ev (ast sh i q x j) = true) <-> rdSt sh P cfg ev i q x <= j := by
    constructor
    · intro h
      rw [asgAst] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨x', hx', h4⟩ := h3
      rw [List.any_eq_true] at h4
      obtain ⟨j', hj', h5⟩ := h4
      rw [Bool.and_eq_true] at h5
      have h0 := of_decide_eq_true h5.left
      unfold ast at h0
      rw [Nat.add_assoc, Nat.add_assoc] at h0
      obtain ⟨hA, hj2⟩ := lin_inj2 (shVal_pos sh) (by omega : j < shVal sh)
        (List.mem_range.mp hj') (Nat.add_left_cancel h0)
      obtain ⟨h1, h2', h3'⟩ := lin_inj3 (shS_pos sh) (shV_pos sh) hq (List.mem_range.mp hq') hx
        (List.mem_range.mp hx') hA
      subst h1; subst h2'; subst h3'
      subst hj2
      exact of_decide_eq_true h5.right
    · intro h
      rw [asgAst]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simp [h]
  by_cases hd : rdSt sh P cfg ev i q x <= j
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgAst sh P cfg ev (ast sh i q x j)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgAxe_val (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hj : j < shVal sh) :
    asgAxe sh P cfg ev (axe sh i q e j) = decide (rdXe sh P cfg ev i q e <= j) := by
  have hiff : (asgAxe sh P cfg ev (axe sh i q e j) = true) <-> rdXe sh P cfg ev i q e <= j := by
    constructor
    · intro h
      rw [asgAxe] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨e', he', h4⟩ := h3
      rw [List.any_eq_true] at h4
      obtain ⟨j', hj', h5⟩ := h4
      rw [Bool.and_eq_true] at h5
      have h0 := of_decide_eq_true h5.left
      unfold axe at h0
      rw [Nat.add_assoc, Nat.add_assoc] at h0
      obtain ⟨hA, hj2⟩ := lin_inj2 (shVal_pos sh) (by omega : j < shVal sh)
        (List.mem_range.mp hj') (Nat.add_left_cancel h0)
      obtain ⟨h1, h2', h3'⟩ := lin_inj3 (shS_pos sh) (shE_pos sh) hq (List.mem_range.mp hq') he
        (List.mem_range.mp he') hA
      subst h1; subst h2'; subst h3'
      subst hj2
      exact of_decide_eq_true h5.right
    · intro h
      rw [asgAxe]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨e, List.mem_range.mpr he, ?_⟩
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simp [h]
  by_cases hd : rdXe sh P cfg ev i q e <= j
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgAxe sh P cfg ev (axe sh i q e j)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgAev_val (hi : i < sh.steps) (hj : j < shEv sh) :
    asgAev sh P cfg ev (aev sh i j) = decide (rdEv sh P cfg ev i <= j) := by
  have hiff : (asgAev sh P cfg ev (aev sh i j) = true) <-> rdEv sh P cfg ev i <= j := by
    constructor
    · intro h
      rw [asgAev] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨j', hj', h3⟩ := h2
      rw [Bool.and_eq_true] at h3
      -- aev is bsAev sh + i * shEv sh + j: right-associate so the block base is a single
      -- syntactic summand, cancel it, and invert the two-level code with lin_inj2.
      have h0 := of_decide_eq_true h3.left
      unfold aev at h0
      simp only [Nat.add_assoc] at h0
      obtain ⟨rfl, rfl⟩ := lin_inj2 (shEv_pos sh) hj (List.mem_range.mp hj')
        (Nat.add_left_cancel h0)
      exact of_decide_eq_true h3.right
    · intro h
      rw [asgAev]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simp [h]
  by_cases hd : rdEv sh P cfg ev i <= j
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgAev sh P cfg ev (aev sh i j)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgAdl_val (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shVal sh) :
    asgAdl sh P cfg ev (adl sh i q j) = decide (rdDl sh P cfg ev i q <= j) := by
  have hiff : (asgAdl sh P cfg ev (adl sh i q j) = true) <-> rdDl sh P cfg ev i q <= j := by
    constructor
    · intro h
      rw [asgAdl] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨j', hj', h4⟩ := h3
      rw [Bool.and_eq_true] at h4
      have h0 := of_decide_eq_true h4.left
      -- adl sh i q j = bsAdl sh + (i * shS sh + q) * shVal sh + j: the inner stride is the
      -- value-block stride shVal, NOT the program-counter stride.
      unfold adl at h0
      rw [Nat.add_assoc, Nat.add_assoc] at h0
      obtain ⟨hA, hj2⟩ := lin_inj2 (shVal_pos sh) hj (List.mem_range.mp hj')
        (Nat.add_left_cancel h0)
      obtain ⟨rfl, rfl⟩ := lin_inj2 (shS_pos sh) hq (List.mem_range.mp hq') hA
      subst hj2
      exact of_decide_eq_true h4.right
    · intro h
      rw [asgAdl]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simp [h]
  by_cases hd : rdDl sh P cfg ev i q <= j
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgAdl sh P cfg ev (adl sh i q j)
    · rfl
    · exact absurd (hiff.mp h2) hd

theorem asgAfr_val (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shD sh) :
    asgAfr sh P cfg ev (afr sh i q j) = decide (rdFr sh P cfg ev i q <= j) := by
  have hiff : (asgAfr sh P cfg ev (afr sh i q j) = true) <-> rdFr sh P cfg ev i q <= j := by
    constructor
    · intro h
      rw [asgAfr] at h
      rw [List.any_eq_true] at h
      obtain ⟨i', hi', h2⟩ := h
      rw [List.any_eq_true] at h2
      obtain ⟨q', hq', h3⟩ := h2
      rw [List.any_eq_true] at h3
      obtain ⟨j', hj', h4⟩ := h3
      rw [Bool.and_eq_true] at h4
      have h0 := of_decide_eq_true h4.left
      -- afr sh i q j = bsAfr sh + (i * shS sh + q) * shD sh + j: the inner stride is the
      -- nonce-domain size shD.
      unfold afr at h0
      rw [Nat.add_assoc, Nat.add_assoc] at h0
      obtain ⟨hA, hj2⟩ := lin_inj2 (shD_pos sh) hj (List.mem_range.mp hj')
        (Nat.add_left_cancel h0)
      obtain ⟨rfl, rfl⟩ := lin_inj2 (shS_pos sh) hq (List.mem_range.mp hq') hA
      subst hj2
      exact of_decide_eq_true h4.right
    · intro h
      rw [asgAfr]
      refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
      refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
      simp [h]
  by_cases hd : rdFr sh P cfg ev i q <= j
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    cases h2 : asgAfr sh P cfg ev (afr sh i q j)
    · rfl
    · exact absurd (hiff.mp h2) hd

end CharacAux


variable (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev)

/-! ### Small Boolean and list helpers -/

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · have hq : q := h.mp hp
    rw [decide_eq_true hp, decide_eq_true hq]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    rw [decide_eq_false hp, decide_eq_false hq]

theorem clause2_left (a : Assignment) (l₁ l₂ : Lit) (h : l₁.eval a = true) :
    Clause.eval a [l₁, l₂] = true := by
  simp [Clause.eval, List.any_cons, List.any_nil, h]

theorem clause2_right (a : Assignment) (l₁ l₂ : Lit) (h : l₂.eval a = true) :
    Clause.eval a [l₁, l₂] = true := by
  simp [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, h]

theorem getD_rangeMap (K i : Nat) (f : Nat -> BVar) (d : BVar) (hi : i < K) :
    ((List.range K).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem ixOf_lt [BEq α] [LawfulBEq α] : ∀ (l : List α) (a : α), a ∈ l → ixOf a l < l.length := by
  intro l
  induction l with
  | nil => intro a h; exact absurd h (by simp)
  | cons x xs ih =>
      intro a h
      by_cases hx : x == a
      · rw [ixOf, if_pos hx]
        exact Nat.succ_pos _
      · rw [ixOf, if_neg hx]
        rw [List.mem_cons] at h
        rcases h with heq | h
        · exact absurd heq (fun he => hx (by rw [he]; exact beq_self_eq_true x))
        · exact Nat.succ_lt_succ (ih a h)

/-! ### Inverting a transition of the operational semantics -/

theorem runOK_knU (h : RunOK sh P cfg ev) : ∀ i t, t ∈ (cfg i).kn → t ∈ sh.U := by
  rcases h with ⟨h1, _, _, _, _, _, _, _⟩; exact h1

theorem runOK_storeU (h : RunOK sh P cfg ev) : ∀ i q v, q < sh.nS1 →
    v ∈ storeVals (storeOf (cfg i) q) → v ∈ sh.U := by
  rcases h with ⟨_, h2, _, _, _, _, _, _⟩; exact h2

theorem runOK_act (h : RunOK sh P cfg ev) : ∀ i q m d, ev i = Ev.act q m d →
    q < sh.nS1 ∧ m ∈ sh.U ∧ d ∈ sh.D := by
  rcases h with ⟨_, _, h3, _, _, _, _, _⟩; exact h3

theorem runOK_dedU (h : RunOK sh P cfg ev) : ∀ i t, ev i = Ev.ded t → t ∈ sh.U := by
  rcases h with ⟨_, _, _, h4, _, _, _, _⟩; exact h4

theorem runOK_pc (h : RunOK sh P cfg ev) : ∀ i q, q < sh.nS1 → pcOf (cfg i) q < shPc sh := by
  rcases h with ⟨_, _, _, _, h5, _, _, _⟩; exact h5

theorem runOK_var (h : RunOK sh P cfg ev) : ∀ i q x, q < sh.nS1 →
    x ∈ (storeOf (cfg i) q).map Prod.fst → x < shV sh := by
  rcases h with ⟨_, _, _, _, _, h6, _, _⟩; exact h6

theorem runOK_expr (h : RunOK sh P cfg ev) : ∀ i q e, e ∈ allExprs P →
    admissible sh (Expr.eval e (storeOf (cfg i) q)) = true := by
  rcases h with ⟨_, _, _, _, _, _, h7, _⟩; exact h7

theorem runOK_sessLen (h : RunOK sh P cfg ev) : ∀ i, (cfg i).sess.length = sh.nS1 := by
  rcases h with ⟨_, _, _, _, _, _, _, h8⟩; exact h8

theorem Rel.noAct {P₁ : Protocol} {C C' : Cfg} {e : Ev} (h : Rel P₁ C e C') (q : Nat)
    (hq : ¬ ∃ (m : Term) (d : NonceName), e = Ev.act q m d) :
    pcOf C' q = pcOf C q ∧ storeOf C' q = storeOf C q ∧ C'.sess.length = C.sess.length := by
  cases e with
  | idle => cases h with | rIdle => exact ⟨rfl, rfl, rfl⟩
  | ded t => cases h with | rDed => exact ⟨rfl, rfl, rfl⟩
  | act q' m d =>
      have hne : q ≠ q' := fun he => hq ⟨m, d, by subst he; rfl⟩
      cases h with
      | rFresh =>
          exact ⟨pcOf_succStore_other C q' q _ _ hne, storeOf_succStore_other C q' q _ _ hne,
            sessLength_succStore C q' _ _⟩
      | rRecv =>
          exact ⟨pcOf_succStore_other C q' q _ _ hne, storeOf_succStore_other C q' q _ _ hne,
            sessLength_succStore C q' _ _⟩
      | rAssign =>
          exact ⟨pcOf_succStore_other C q' q _ _ hne, storeOf_succStore_other C q' q _ _ hne,
            sessLength_succStore C q' _ _⟩
      | rSend =>
          exact ⟨pcOf_succSend_other C q' q _ hne, storeOf_succSend_other C q' q _ hne,
            sessLength_succSend C q' _⟩
      | rCheck =>
          exact ⟨pcOf_succAdvance_other C q' q hne, storeOf_succAdvance_other C q' q hne,
            sessLength_succAdvance C q'⟩
      | rSecret =>
          exact ⟨pcOf_succAdvance_other C q' q hne, storeOf_succAdvance_other C q' q hne,
            sessLength_succAdvance C q'⟩
      | rClaim =>
          exact ⟨pcOf_succAdvance_other C q' q hne, storeOf_succAdvance_other C q' q hne,
            sessLength_succAdvance C q'⟩
      | rCommit =>
          exact ⟨pcOf_succAdvance_other C q' q hne, storeOf_succAdvance_other C q' q hne,
            sessLength_succAdvance C q'⟩

theorem Rel.act_pcOf {P₁ : Protocol} {C C' : Cfg} {q : Nat} {m : Term} {d : NonceName}
    (h : Rel P₁ C (Ev.act q m d) C') (hS : q < C.sess.length) : pcOf C' q = pcOf C q + 1 := by
  cases h with
  | rFresh => exact pcOf_succStore' C q _ _ hS
  | rRecv => exact pcOf_succStore' C q _ _ hS
  | rAssign => exact pcOf_succStore' C q _ _ hS
  | rSend => exact pcOf_succSend' C q _ hS
  | rCheck => exact pcOf_succAdvance' C q hS
  | rSecret => exact pcOf_succAdvance' C q hS
  | rClaim => exact pcOf_succAdvance' C q hS
  | rCommit => exact pcOf_succAdvance' C q hS

theorem Rel.kn_mono {P₁ : Protocol} {C C' : Cfg} {e : Ev} (h : Rel P₁ C e C') (t : Term)
    (ht : t ∈ C.kn) : t ∈ C'.kn := by
  cases h with
  | rIdle => exact ht
  | rDed => exact List.mem_append_left _ ht
  | rFresh => exact ht
  | rRecv => exact ht
  | rAssign => exact ht
  | rSend => exact List.mem_append_left _ ht
  | rCheck => exact ht
  | rSecret => exact ht
  | rClaim => exact ht
  | rCommit => exact ht

theorem Rel.kn_step {P₁ : Protocol} {C C' : Cfg} {e : Ev} (h : Rel P₁ C e C') :
    C'.kn = C.kn ∨
      (∃ (t : Term), e = Ev.ded t ∧ C'.kn = C.kn ++ [t]) ∨
      (∃ (q : Nat) (t m : Term) (d : NonceName) (a : Agent) (x : Expr),
          e = Ev.act q m d ∧ C'.kn = C.kn ++ [t] ∧
            P₁.actionAt q (pcOf C q) = some (Action.send a x) ∧
              Expr.eval x (storeOf C q) = some t) := by
  cases h with
  | rIdle => exact Or.inl rfl
  | rDed => exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | rFresh => exact Or.inl rfl
  | rRecv => exact Or.inl rfl
  | rAssign => exact Or.inl rfl
  | rSend =>
      exact Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl, rfl, by assumption, by assumption⟩)
  | rCheck => exact Or.inl rfl
  | rSecret => exact Or.inl rfl
  | rClaim => exact Or.inl rfl
  | rCommit => exact Or.inl rfl

theorem Rel.kn_new {P₁ : Protocol} {C C' : Cfg} {e : Ev} {u : Term} (h : Rel P₁ C e C')
    (hu : u ∈ C'.kn) (hun : u ∉ C.kn) :
    (e = Ev.ded u) ∨
      ∃ (q : Nat) (a : Agent) (x : Expr) (m : Term) (d : NonceName),
        e = Ev.act q m d ∧ P₁.actionAt q (pcOf C q) = some (Action.send a x) ∧
          Expr.eval x (storeOf C q) = some u := by
  rcases Rel.kn_step h with heq | ⟨t, het, hkn⟩ | ⟨q, t, m, d, a, x, het, hkn, hamt, heval⟩
  · rw [heq] at hu
    exact absurd hu hun
  · rw [hkn, List.mem_append] at hu
    rcases hu with h | h
    · exact absurd h hun
    · have htu : t = u := Eq.symm (by simpa using h)
      exact Or.inl (het.trans (congrArg Ev.ded htu))
  · rw [hkn, List.mem_append] at hu
    rcases hu with h | h
    · exact absurd h hun
    · have htu : t = u := Eq.symm (by simpa using h)
      exact Or.inr ⟨q, a, x, m, d, het, hamt, heval.trans (congrArg some htu)⟩

/-! ### The sequential at-most-one counter and the canonical flag assignment -/

/-- **The sequential counter is satisfied by the canonical flag assignment.**  Let vs be the
variables of a one-hot group and s its flag variables, and suppose the assignment sets exactly
one variable of vs - the one at position k - and sets flag j to true exactly when k <= j.
Then every clause of ProtSat.atMostOneSeq vs s is satisfied.

The index o is the position of the first element of vs inside the whole group: the recursion
of atMostOneSeq drops the head of the list, so the flags of a suffix must be measured against
the shifted position.  Without the offset, the suffix of a group whose selected index is 0
would be asked for flags that are all true while its own selected index does not exist. -/
theorem atMostOneSeq_sat_from : ∀ (vs : List BVar) (s : Nat -> BVar) (a : Assignment)
    (k o : Nat) (d : BVar),
    (∀ i, i < vs.length → a (vs.getD i d) = decide (i + o = k)) →
    (∀ j, j < vs.length → a (s j) = decide (k ≤ j + o)) →
    ∀ cl ∈ atMostOneSeq vs s, Clause.eval a cl = true := by
  intro vs
  induction vs with
  | nil => intro s a k o d _ _ cl hcl; exact absurd hcl (by simp [atMostOneSeq_nil])
  | cons x rest ih =>
      intro s a k o d hvars hflags cl hcl
      cases rest with
      | nil => exact absurd hcl (by simp [atMostOneSeq_single])
      | cons y rest' =>
          cases rest' with
          | nil =>
              rw [atMostOneSeq_two] at hcl
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
              rcases hcl with rfl | rfl
              · by_cases hx : a x = true
                · have h1 : a x = decide (0 + o = k) := hvars 0 (by simp)
                  have hk : 0 + o = k := of_decide_eq_true (by rw [← h1]; exact hx)
                  refine clause2_right a (neg x) (pos (s 0)) ?_
                  rw [pos_eval, hflags 0 (by simp)]
                  exact decide_eq_true (by omega)
                · exact clause2_left a (neg x) (pos (s 0)) (by simp [neg_eval, hx])
              · by_cases hy : a y = true
                · have h1 : a y = decide (1 + o = k) := hvars 1 (by simp)
                  have hk : 1 + o = k := of_decide_eq_true (by rw [← h1]; exact hy)
                  refine clause2_right a (neg y) (neg (s 0)) ?_
                  rw [neg_eval, hflags 0 (by simp), decide_eq_false (by omega)]
                  rfl
                · exact clause2_left a (neg y) (neg (s 0)) (by simp [neg_eval, hy])
          | cons w rest'' =>
              rw [atMostOneSeq_three] at hcl
              simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hcl
              rcases hcl with rfl | rfl | rfl | htail
              · by_cases hx : a x = true
                · have h1 : a x = decide (0 + o = k) := hvars 0 (by simp)
                  have hk : 0 + o = k := of_decide_eq_true (by rw [← h1]; exact hx)
                  refine clause2_right a (neg x) (pos (s 0)) ?_
                  rw [pos_eval, hflags 0 (by simp)]
                  exact decide_eq_true (by omega)
                · exact clause2_left a (neg x) (pos (s 0)) (by simp [neg_eval, hx])
              · by_cases hy : a y = true
                · have h1 : a y = decide (1 + o = k) := hvars 1 (by simp)
                  have hk : 1 + o = k := of_decide_eq_true (by rw [← h1]; exact hy)
                  refine clause2_right a (neg y) (neg (s 0)) ?_
                  rw [neg_eval, hflags 0 (by simp), decide_eq_false (by omega)]
                  rfl
                · exact clause2_left a (neg y) (neg (s 0)) (by simp [neg_eval, hy])
              · by_cases hs : a (s 0) = true
                · have h0 : a (s 0) = decide (k ≤ 0 + o) := hflags 0 (by simp)
                  have hle : k ≤ 1 + o :=
                    Nat.le_trans (of_decide_eq_true (by rw [← h0]; exact hs)) (by omega)
                  refine clause2_right a (neg (s 0)) (pos (s 1)) ?_
                  rw [pos_eval, hflags 1 (by simp)]
                  exact decide_eq_true hle
                · exact clause2_left a (neg (s 0)) (pos (s 1)) (by simp [neg_eval, hs])
              · refine ih (fun j => s (j + 1)) a k (o + 1) d ?_ ?_ cl htail
                · intro i hi
                  have h9 : i + 1 < (x :: y :: w :: rest'').length := by
                    show i + 1 < (y :: w :: rest'').length + 1
                    exact Nat.succ_lt_succ hi
                  have h1 : a ((x :: y :: w :: rest'').getD (i + 1) d) =
                      decide ((i + 1) + o = k) := hvars (i + 1) h9
                  have h2 : (x :: y :: w :: rest'').getD (i + 1) d =
                      (y :: w :: rest'').getD i d := rfl
                  rw [h2] at h1
                  exact h1.trans (decide_congr (by omega))
                · intro j hj
                  have h9 : j + 1 < (x :: y :: w :: rest'').length := by
                    show j + 1 < (y :: w :: rest'').length + 1
                    exact Nat.succ_lt_succ hj
                  have h1 : a (s (j + 1)) = decide (k ≤ (j + 1) + o) := hflags (j + 1) h9
                  exact h1.trans (decide_congr (by omega))

/-- **A range group is one-hot in the canonical assignment.**  If the assignment sets exactly
the variable of index k in the group and gives the flags the prefix predicate, the group's
one-hot clauses - at-least-one plus the sequential counter - are satisfied. -/
theorem Oh.sat_range {o : Oh Nat} {a : Assignment} {k K : Nat}
    (hvals : o.vals = List.range K) (hk : k < K)
    (hvars : ∀ c, c < K → a (o.varOf c) = decide (c = k))
    (hflags : ∀ j, j < K → a (o.auxOf j) = decide (k ≤ j)) :
    Sat a o.clauses := by
  intro cl hcl
  have hlen : ((List.range K).map o.varOf).length = K := by
    rw [List.length_map, List.length_range]
  rw [Oh.clauses, hvals] at hcl
  simp only [List.mem_append] at hcl
  rcases hcl with h1 | h2
  · refine (sat_atLeastOne.mpr ⟨o.varOf k,
        List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩,
        by rw [hvars k hk]; exact decide_eq_true (Eq.refl k)⟩) cl h1
  · refine atMostOneSeq_sat_from ((List.range K).map o.varOf) o.auxOf a k 0 (o.auxOf 0) ?_ ?_
      cl h2
    · intro i hi
      have hi' : i < K := by rw [← hlen]; exact hi
      rw [getD_rangeMap K i o.varOf (o.auxOf 0) hi']
      exact hvars i hi'
    · intro j hj
      have hj' : j < K := by rw [← hlen]; exact hj
      exact hflags j hj'

/-- The universe of a shape is subterm-closed when every subterm of every universe message is
again a universe message.  This is the property that makes the enumeration of attacker rule
instances complete: the premises of a rule whose conclusion the universe contains are subterms
of it, so they too have names.  ProtSat.Bounded.univ is built subterm-closed on purpose; the
analyser checks the condition on the shape it is about to encode. -/
def univSub (sh : Shape) : Prop := ∀ t ∈ sh.U, ∀ u ∈ subtermsL t, u ∈ sh.U

/-! ### Completeness of the deduction-instance enumeration -/

/-- Subterm memberships the instance enumeration needs. -/
theorem subtermsL_pair1 {x y : Term} : x ∈ subtermsL (Term.pair x y) :=
  List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (mem_subtermsL x))))
theorem subtermsL_pair2 {x y : Term} : y ∈ subtermsL (Term.pair x y) :=
  List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (mem_subtermsL y))))
theorem subtermsL_encS1 {m : Term} {k : Key} : m ∈ subtermsL (Term.encS m k) :=
  List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (mem_subtermsL m))))
theorem subtermsL_encS2 {m : Term} {k : Key} : Term.key k ∈ subtermsL (Term.encS m k) :=
  List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.Mem.head _))))
theorem subtermsL_encA1 {m : Term} {a : Agent} : m ∈ subtermsL (Term.encA m a) :=
  List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (mem_subtermsL m))))
theorem subtermsL_hash1 {m : Term} : m ∈ subtermsL (Term.hash m) :=
  List.mem_cons.mpr (Or.inr (mem_subtermsL m))

/-- The universe index of a member of the universe. -/
theorem tIx_some {sh : Shape} {x : Term} (hx : x ∈ sh.U) : tIx sh x = some (ixOf x sh.U) := by
  unfold tIx
  rw [if_pos hx]

/-- Premise obligations of the enumerated instances, one lemma per arity. -/
theorem prem_ok0 {sh : Shape} {K : List Term} :
    ∀ p ∈ ([] : List Nat), ∃ v, valAt sh p = some v ∧ v ∈ K := by
  intro p hp; exact absurd hp (by simp)

theorem prem_ok1 {sh : Shape} {K : List Term} {a : Nat} {v : Term}
    (ha : valAt sh a = some v) (hv : v ∈ K) :
    ∀ p ∈ [a], ∃ v, valAt sh p = some v ∧ v ∈ K := by
  intro p hp
  rcases List.mem_singleton.mp hp with rfl
  exact ⟨v, ha, hv⟩

theorem prem_ok2 {sh : Shape} {K : List Term} {a b : Nat} {v w : Term}
    (ha : valAt sh a = some v) (hv : v ∈ K) (hb : valAt sh b = some w) (hw : w ∈ K) :
    ∀ p ∈ [a, b], ∃ x, valAt sh p = some x ∧ x ∈ K := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨v, ha, hv⟩
  · rcases List.mem_singleton.mp hp with rfl
    exact ⟨w, hb, hw⟩

/-- Every one-step deduction of a universe message is represented by one of the enumerated
instances: the instance's conclusion is the number of the message, and each of its premises is
the number of a message the attacker already knows. -/
theorem dedInstsOf_complete {sh : Shape} (hsub : univSub sh) {K : List Term} {t : Term}
    (hKU : ∀ x, x ∈ K → x ∈ sh.U) (ht : t ∈ sh.U) (h : OneStep K t) :
    ∃ ins ∈ dedInstsOf sh (uIdx sh (some t)),
      (∀ p ∈ ins.prem, ∃ v, valAt sh p = some v ∧ v ∈ K) ∧ ins.concl = uIdx sh (some t) := by
  have hu : valAt sh (uIdx sh (some t)) = some t := valAt_uIdx_some sh ht
  have hU : rget sh.U (uIdx sh (some t)) = some t := hu
  cases h with
  | known hk =>
      unfold dedInstsOf
      rw [hU]
      dsimp only
      refine ⟨_, List.Mem.head _, ?_, rfl⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨t, hu, hk⟩
      · exact absurd hp (by simp)
  | agent =>
      rename_i a
      unfold dedInstsOf
      rw [hU]
      dsimp only
      exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.Mem.head _)))), prem_ok0, rfl⟩
  | pub =>
      rename_i a
      unfold dedInstsOf
      rw [hU]
      dsimp only
      exact ⟨_, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.Mem.head _)))), prem_ok0, rfl⟩
  | pairI hx hy =>
      rename_i x y
      have hxU : x ∈ sh.U := hsub _ ht _ subtermsL_pair1
      have hyU : y ∈ sh.U := hsub _ ht _ subtermsL_pair2
      unfold dedInstsOf
      rw [hU]
      dsimp only
      rw [tIx_some hxU, tIx_some hyU]
      dsimp only
      refine ⟨_, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.Mem.head _)))), ?_, rfl⟩
      refine prem_ok2 (tIx_valAt (tIx_some hxU)) hx (tIx_valAt (tIx_some hyU)) hy
  | fstE hp =>
      rename_i y
      have hpU : Term.pair t y ∈ sh.U := hKU _ hp
      have hmem : ({concl := uIdx sh (some t), prem := [ixOf (Term.pair t y) sh.U]} : DedInst) ∈ dedInstsOf sh (uIdx sh (some t)) := by
        unfold dedInstsOf
        rw [hU]
        dsimp only
        exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨Term.pair t y, hpU, by simp⟩)
      refine ⟨_, hmem, ?_, rfl⟩
      refine prem_ok1 (rget_ixOf sh.U _ hpU) hp
  | sndE hp =>
      rename_i x
      have hpU : Term.pair x t ∈ sh.U := hKU _ hp
      have hmem : ({concl := uIdx sh (some t), prem := [ixOf (Term.pair x t) sh.U]} : DedInst) ∈ dedInstsOf sh (uIdx sh (some t)) := by
        unfold dedInstsOf
        rw [hU]
        dsimp only
        exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨Term.pair x t, hpU, by simp⟩)
      refine ⟨_, hmem, ?_, rfl⟩
      refine prem_ok1 (rget_ixOf sh.U _ hpU) hp
  | encSI hm hk =>
      rename_i m k
      have hmU : m ∈ sh.U := hsub _ ht _ subtermsL_encS1
      have hkU : Term.key k ∈ sh.U := hsub _ ht _ subtermsL_encS2
      unfold dedInstsOf
      rw [hU]
      dsimp only
      rw [tIx_some hmU, tIx_some hkU]
      dsimp only
      refine ⟨_, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.Mem.head _)))), ?_, rfl⟩
      refine prem_ok2 (tIx_valAt (tIx_some hmU)) hm (tIx_valAt (tIx_some hkU)) hk
  | encSD hp hk =>
      rename_i k
      have hpU : Term.encS t k ∈ sh.U := hKU _ hp
      have hkU : Term.key k ∈ sh.U := hKU _ hk
      have hmem : ({concl := uIdx sh (some t), prem := [ixOf (Term.encS t k) sh.U, ixOf (Term.key k) sh.U]} : DedInst) ∈ dedInstsOf sh (uIdx sh (some t)) := by
        unfold dedInstsOf
        rw [hU]
        dsimp only
        exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨Term.encS t k, hpU, by simp [tIx_some hkU]⟩)
      refine ⟨_, hmem, ?_, rfl⟩
      refine prem_ok2 (rget_ixOf sh.U _ hpU) hp (tIx_valAt (tIx_some hkU)) hk
  | encAI hm =>
      rename_i m a
      have hmU : m ∈ sh.U := hsub _ ht _ subtermsL_encA1
      unfold dedInstsOf
      rw [hU]
      dsimp only
      rw [tIx_some hmU]
      dsimp only
      refine ⟨_, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.Mem.head _)))), ?_, rfl⟩
      refine prem_ok1 (tIx_valAt (tIx_some hmU)) hm
  | encAD hp hk =>
      rename_i a
      have hpU : Term.encA t a ∈ sh.U := hKU _ hp
      have hkU : Term.key (Key.priv a) ∈ sh.U := hKU _ hk
      have hmem : ({concl := uIdx sh (some t), prem := [ixOf (Term.encA t a) sh.U, ixOf (Term.key (Key.priv a)) sh.U]} : DedInst) ∈ dedInstsOf sh (uIdx sh (some t)) := by
        unfold dedInstsOf
        rw [hU]
        dsimp only
        exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨Term.encA t a, hpU, by simp [tIx_some hkU]⟩)
      refine ⟨_, hmem, ?_, rfl⟩
      refine prem_ok2 (rget_ixOf sh.U _ hpU) hp (tIx_valAt (tIx_some hkU)) hk
  | hashI hm =>
      rename_i m
      have hmU : m ∈ sh.U := hsub _ ht _ subtermsL_hash1
      unfold dedInstsOf
      rw [hU]
      dsimp only
      rw [tIx_some hmU]
      dsimp only
      refine ⟨_, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.Mem.head _)))), ?_, rfl⟩
      refine prem_ok1 (tIx_valAt (tIx_some hmU)) hm

/-- If some position of a list satisfies a Boolean test, the first such position does. -/
theorem find?_some_of_exists : ∀ (l : List Nat) (f : Nat -> Bool),
    (∃ n, n ∈ l ∧ f n = true) -> ∃ n, n ∈ l ∧ l.find? f = some n ∧ f n = true := by
  intro l
  induction l with
  | nil => intro f h; exact absurd h (by simp)
  | cons x xs ih =>
      intro f h
      by_cases hx : f x = true
      · exact ⟨x, List.Mem.head _, by simp only [List.find?, hx, reduceIte], hx⟩
      · obtain ⟨n, hn, hf⟩ := h
        rw [List.mem_cons] at hn
        rcases hn with heq | hn
        · exact absurd heq (fun he => hx (he ▸ hf))
        · obtain ⟨n, hn', heq, hon⟩ := ih f ⟨n, hn, hf⟩
          exact ⟨n, List.Mem.tail _ hn', by simp only [List.find?, hx, reduceIte]; exact heq, hon⟩

/-- The index chosen by ProtSat.Complete.dedIx names an instance that really applies. -/
theorem dedIx_spec {sh : Shape} {K : List Term} {u : Nat}
    (h : ∃ n, n < nInst sh ∧ dedInstOk sh K n u = true) :
    dedIx sh K u < nInst sh ∧ dedInstOk sh K (dedIx sh K u) u = true := by
  obtain ⟨n, hn, hon⟩ := h
  obtain ⟨m, hm, heq, hom⟩ :=
    find?_some_of_exists (List.range (nInst sh)) (fun k => dedInstOk sh K k u)
      ⟨n, List.mem_range.mpr hn, hon⟩
  have h1 : dedIx sh K u = m := by
    unfold dedIx
    rw [heq]
  refine ⟨by rw [h1]; exact List.mem_range.mp hm, by rw [h1]; exact hom⟩

/-- **Every one-step deduction of a universe message has an enumerated instance.** -/
theorem dedIx_exists {sh : Shape} (hsub : univSub sh) {K : List Term} {t : Term}
    (hKU : ∀ x, x ∈ K → x ∈ sh.U) (ht : t ∈ sh.U) (h : OneStep K t) :
    ∃ n, n < nInst sh ∧ dedInstOk sh K n (uIdx sh (some t)) = true := by
  obtain ⟨ins, hins, hprem, hconcl⟩ := dedInstsOf_complete hsub hKU ht h
  have hlen : (uIdx sh (some t)) < sh.U.length := by
    have h2 : valAt sh (uIdx sh (some t)) = some t := valAt_uIdx_some sh ht
    by_contra e
    have h3 : valAt sh (uIdx sh (some t)) = none := rget_oob_ge sh.U _ (by omega)
    rw [h3] at h2; simp at h2
  have hmem : ins ∈ dedInsts sh :=
    List.mem_flatMap.mpr ⟨uIdx sh (some t), List.mem_range.mpr hlen, hins⟩
  obtain ⟨n, hn, hget⟩ := mem_rget (dedInsts sh) ins hmem
  refine ⟨n, hn, ?_⟩
  unfold dedInstOk instAt
  rw [hget]
  dsimp only
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hconcl, List.all_eq_true.mpr ?_⟩
  intro p hp
  obtain ⟨v, hv, hk⟩ := hprem p hp
  rw [hv]
  exact decide_eq_true hk

/-! ### The readers are in range -/

/-- The program counter the run records is a legal index of the program-counter group. -/
theorem rdPc_lt (hok : RunOK sh P cfg ev) (hq : q < shS sh) :
    rdPc sh P cfg ev i q < shPc sh := by
  by_cases hq' : q < sh.nS1
  · show pcOf (cfg i) q < shPc sh
    exact runOK_pc sh P cfg ev hok i q hq'
  · have hlen : (cfg i).sess.length = sh.nS1 := runOK_sessLen sh P cfg ev hok i
    have hnone : sessAt (cfg i) q = none := by
      unfold sessAt
      exact rget_oob_ge (cfg i).sess q (by omega)
    show pcOf (cfg i) q < shPc sh
    rw [pcOf, hnone]
    exact shPc_pos sh

theorem rdSt_lt : rdSt sh P cfg ev i q x < shVal sh := uIdx_lt' sh _
theorem rdXe_lt : rdXe sh P cfg ev i q e < shVal sh := uIdx_lt' sh _
theorem rdDl_lt : rdDl sh P cfg ev i q < shVal sh := uIdx_lt' sh _

/-- The nonce index the run records is a legal index of the nonce group. -/
theorem rdFr_lt (hok : RunOK sh P cfg ev) (hq : q < shS sh) :
    rdFr sh P cfg ev i q < shD sh := by
  cases h : ev i with
  | idle =>
      have h1 : rdFr sh P cfg ev i q = 0 := by simp [rdFr, h]
      rw [h1]
      exact Nat.succ_pos _
  | ded t =>
      have h1 : rdFr sh P cfg ev i q = 0 := by simp [rdFr, h]
      rw [h1]
      exact Nat.succ_pos _
  | act q' m d =>
      by_cases hq : q' = q
      · have hd : d ∈ sh.D := (runOK_act sh P cfg ev hok i q' m d h).2.2
        have h1 : rdFr sh P cfg ev i q = ixOf d sh.D := by unfold rdFr; rw [h]; exact if_pos hq
        rw [h1]
        have hs : shD sh = sh.D.length + 1 := rfl
        rw [hs]
        exact Nat.lt_succ_of_lt (ixOf_lt sh.D d hd)
      · have h1 : rdFr sh P cfg ev i q = 0 := by unfold rdFr; rw [h]; exact if_neg hq
        rw [h1]
        exact Nat.succ_pos _

/-- The deduction part of a legal step is a one-step deduction of its conclusion. -/
theorem Rel.ded_oneStep {P₁ : Protocol} {C C' : Cfg} {t : Term} (h : Rel P₁ C (Ev.ded t) C') :
    OneStep C.kn t := by
  cases h with
  | rDed hstep => exact hstep

theorem rdEv_lt (hok : RunOK sh P cfg ev) (hsub : univSub sh) (i : Nat)
    (hrel : Rel P (cfg i) (ev i) (cfg (i + 1))) : rdEv sh P cfg ev i < shEv sh := by
  have hs : shEv sh = 1 + shS sh + nInst sh := rfl
  cases h : ev i with
  | idle =>
      have h1 : rdEv sh P cfg ev i = 0 := by unfold rdEv; rw [h]
      rw [h1]
      exact shEv_pos sh
  | act q m d =>
      have hq : q < shS sh := by
        have h2 := (runOK_act sh P cfg ev hok i q m d h).1
        have hs2 : shS sh = sh.nS1 + 1 := rfl
        rw [hs2]
        omega
      have h1 : rdEv sh P cfg ev i = 1 + q := by unfold rdEv; rw [h]
      rw [h1, hs]
      omega
  | ded t =>
      have ht : t ∈ sh.U := runOK_dedU sh P cfg ev hok i t h
      have hone : OneStep (cfg i).kn t := Rel.ded_oneStep (by rw [h] at hrel; exact hrel)
      obtain ⟨n, hn, hon⟩ := dedIx_exists hsub (runOK_knU sh P cfg ev hok i) ht hone
      have hix : dedIx sh ((cfg i).kn) (uIdx sh (some t)) < nInst sh :=
        (dedIx_spec ⟨n, hn, hon⟩).1
      have h1 : rdEv sh P cfg ev i = 1 + shS sh + dedIx sh ((cfg i).kn) (uIdx sh (some t)) := by
        unfold rdEv
        rw [h]
      rw [h1, hs]
      omega

/-! ### The cascade dispatches every family to its own test -/

theorem bsApc_le_bsAst (sh : Shape) : bsApc sh ≤ bsAst sh := Nat.le_add_right _ _
theorem bsAst_le_bsAxe (sh : Shape) : bsAst sh ≤ bsAxe sh := Nat.le_add_right _ _
theorem bsAxe_le_bsAev (sh : Shape) : bsAxe sh ≤ bsAev sh := Nat.le_add_right _ _
theorem bsAev_le_bsAdl (sh : Shape) : bsAev sh ≤ bsAdl sh := Nat.le_add_right _ _
theorem bsAdl_le_bsAfr (sh : Shape) : bsAdl sh ≤ bsAfr sh := Nat.le_add_right _ _
theorem bsAfr_le_bsAfterAux (sh : Shape) : bsAfr sh ≤ bsAfterAux sh := Nat.le_add_right _ _
theorem bsAfterAux_le_bsAu (sh : Shape) : bsAfterAux sh ≤ bsAu sh := Nat.le_add_right _ _
theorem bsTotal_le_bsAxe (sh : Shape) : bsTotal sh ≤ bsAxe sh :=
  Nat.le_trans (bsTotal_le_bsAst sh) (bsAst_le_bsAxe sh)
theorem bsTotal_le_bsAev (sh : Shape) : bsTotal sh ≤ bsAev sh :=
  Nat.le_trans (bsTotal_le_bsAxe sh) (bsAxe_le_bsAev sh)
theorem bsTotal_le_bsAdl (sh : Shape) : bsTotal sh ≤ bsAdl sh :=
  Nat.le_trans (bsTotal_le_bsAev sh) (bsAev_le_bsAdl sh)
theorem bsTotal_le_bsAfr (sh : Shape) : bsTotal sh ≤ bsAfr sh :=
  Nat.le_trans (bsTotal_le_bsAdl sh) (bsAdl_le_bsAfr sh)
theorem bsTotal_le_bsAfterAux (sh : Shape) : bsTotal sh ≤ bsAfterAux sh :=
  Nat.le_trans (bsTotal_le_bsAfr sh) (bsAfr_le_bsAfterAux sh)
theorem bsAst_le_bsAev (sh : Shape) : bsAst sh ≤ bsAev sh :=
  Nat.le_trans (bsAst_le_bsAxe sh) (bsAxe_le_bsAev sh)
theorem bsAst_le_bsAdl (sh : Shape) : bsAst sh ≤ bsAdl sh :=
  Nat.le_trans (bsAst_le_bsAev sh) (bsAev_le_bsAdl sh)
theorem bsAst_le_bsAfr (sh : Shape) : bsAst sh ≤ bsAfr sh :=
  Nat.le_trans (bsAst_le_bsAdl sh) (bsAdl_le_bsAfr sh)
theorem bsAst_le_bsAfterAux (sh : Shape) : bsAst sh ≤ bsAfterAux sh :=
  Nat.le_trans (bsAst_le_bsAfr sh) (bsAfr_le_bsAfterAux sh)
theorem bsAxe_le_bsAdl (sh : Shape) : bsAxe sh ≤ bsAdl sh :=
  Nat.le_trans (bsAxe_le_bsAev sh) (bsAev_le_bsAdl sh)
theorem bsAxe_le_bsAfr (sh : Shape) : bsAxe sh ≤ bsAfr sh :=
  Nat.le_trans (bsAxe_le_bsAdl sh) (bsAdl_le_bsAfr sh)
theorem bsAxe_le_bsAfterAux (sh : Shape) : bsAxe sh ≤ bsAfterAux sh :=
  Nat.le_trans (bsAxe_le_bsAfr sh) (bsAfr_le_bsAfterAux sh)
theorem bsAev_le_bsAfr (sh : Shape) : bsAev sh ≤ bsAfr sh :=
  Nat.le_trans (bsAev_le_bsAdl sh) (bsAdl_le_bsAfr sh)
theorem bsAev_le_bsAfterAux (sh : Shape) : bsAev sh ≤ bsAfterAux sh :=
  Nat.le_trans (bsAev_le_bsAfr sh) (bsAfr_le_bsAfterAux sh)
theorem bsAdl_le_bsAfterAux (sh : Shape) : bsAdl sh ≤ bsAfterAux sh :=
  Nat.le_trans (bsAdl_le_bsAfr sh) (bsAfr_le_bsAfterAux sh)

/-- Everything at or above the auxiliary blocks skips the seven main tests of the cascade. -/
theorem assignOf_ge_bsTotal (v : BVar) (hv : bsTotal sh ≤ v) :
    assignOf sh P cfg ev v =
      if v < bsAst sh then asgApc sh P cfg ev v
      else if v < bsAxe sh then asgAst sh P cfg ev v
      else if v < bsAev sh then asgAxe sh P cfg ev v
      else if v < bsAdl sh then asgAev sh P cfg ev v
      else if v < bsAfr sh then asgAdl sh P cfg ev v
      else if v < bsAfterAux sh then asgAfr sh P cfg ev v
      else if v < bsAu sh then asgPb sh P cfg ev v
      else asgAu sh P cfg ev v := by
  dsimp only [assignOf]
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans (bsSt_le_bsTotal sh) hv)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsKn_le_bsTotal sh) hv)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsEv_le_bsTotal sh) hv)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsDl_le_bsTotal sh) hv)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsFr_le_bsTotal sh) hv)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsXe_le_bsTotal sh) hv)),
    if_neg (Nat.not_lt_of_le hv)]

theorem assignOf_apc (hi : i ≤ sh.steps) (hq : q < shS sh) (hj : j < shPc sh) :
    assignOf sh P cfg ev (apc sh i q j) = decide (rdPc sh P cfg ev i q ≤ j) :=
  by rw [asg_branch_apc sh P cfg ev hi hq hj, asgApc_val sh P cfg ev hi hq hj]

theorem assignOf_ast (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hj : j < shVal sh) :
    assignOf sh P cfg ev (ast sh i q x j) = decide (rdSt sh P cfg ev i q x ≤ j) :=
  by rw [asg_branch_ast sh P cfg ev hi hq hx hj, asgAst_val sh P cfg ev hi hq hx hj]

theorem assignOf_axe (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hj : j < shVal sh) :
    assignOf sh P cfg ev (axe sh i q e j) = decide (rdXe sh P cfg ev i q e ≤ j) := by
  have hge : bsAxe sh ≤ axe sh i q e j := axe_ge sh
  rw [assignOf_ge_bsTotal sh P cfg ev _ (Nat.le_trans (bsTotal_le_bsAxe sh) hge),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAst_le_bsAxe sh) hge)),
    if_neg (Nat.not_lt_of_le hge),
    if_pos (axe_lt_bsAev sh i q e j hi hq he hj),
    asgAxe_val sh P cfg ev hi hq he hj]

theorem assignOf_aev (hi : i < sh.steps) (hj : j < shEv sh) :
    assignOf sh P cfg ev (aev sh i j) = decide (rdEv sh P cfg ev i ≤ j) := by
  have hge : bsAev sh ≤ aev sh i j := aev_ge sh
  rw [assignOf_ge_bsTotal sh P cfg ev _ (Nat.le_trans (bsTotal_le_bsAev sh) hge),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAst_le_bsAev sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAxe_le_bsAev sh) hge)),
    if_neg (Nat.not_lt_of_le hge),
    if_pos (aev_lt_bsAdl sh i j hi hj),
    asgAev_val sh P cfg ev hi hj]

theorem assignOf_adl (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shVal sh) :
    assignOf sh P cfg ev (adl sh i q j) = decide (rdDl sh P cfg ev i q ≤ j) := by
  have hge : bsAdl sh ≤ adl sh i q j := adl_ge sh
  rw [assignOf_ge_bsTotal sh P cfg ev _ (Nat.le_trans (bsTotal_le_bsAdl sh) hge),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAst_le_bsAdl sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAxe_le_bsAdl sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAev_le_bsAdl sh) hge)),
    if_neg (Nat.not_lt_of_le hge),
    if_pos (adl_lt_bsAfr sh i q j hi hq hj),
    asgAdl_val sh P cfg ev hi hq hj]

theorem assignOf_afr (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shD sh) :
    assignOf sh P cfg ev (afr sh i q j) = decide (rdFr sh P cfg ev i q ≤ j) := by
  have hge : bsAfr sh ≤ afr sh i q j := afr_ge sh
  rw [assignOf_ge_bsTotal sh P cfg ev _ (Nat.le_trans (bsTotal_le_bsAfr sh) hge),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAst_le_bsAfr sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAxe_le_bsAfr sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAev_le_bsAfr sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAdl_le_bsAfr sh) hge)),
    if_neg (Nat.not_lt_of_le hge),
    if_pos (afr_lt_bsAfterAux sh i q j hi hq hj),
    asgAfr_val sh P cfg ev hi hq hj]

theorem assignOf_vpb (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vpb sh i q c u) = asgPb sh P cfg ev (vpb sh i q c u) := by
  have hge : bsAfterAux sh ≤ vpb sh i q c u := bsAfterAux_le_vpb sh
  rw [assignOf_ge_bsTotal sh P cfg ev _ (Nat.le_trans (bsTotal_le_bsAfterAux sh) hge),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAst_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAxe_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAev_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAdl_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAfr_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le hge),
    if_pos (vpb_lt_bsAu sh i q c u hi hq hc hu)]

theorem assignOf_vau (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hu : u < shVal sh) :
    assignOf sh P cfg ev (vau sh i q x u) = asgAu sh P cfg ev (vau sh i q x u) := by
  have hge : bsAfterAux sh ≤ vau sh i q x u :=
    Nat.le_trans (bsAfterAux_le_bsAu sh) (bsAu_le_vau sh)
  rw [assignOf_ge_bsTotal sh P cfg ev _ (Nat.le_trans (bsTotal_le_bsAfterAux sh) hge),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAst_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAxe_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAev_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAdl_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (bsAfr_le_bsAfterAux sh) hge)),
    if_neg (Nat.not_lt_of_le hge),
    if_neg (Nat.not_lt_of_le (bsAu_le_vau sh))]

/-- Symmetry of a decided equality. -/
theorem decide_symm {m n : Nat} : decide (m = n) = decide (n = m) :=
  decide_congr ⟨Eq.symm, Eq.symm⟩

/-! ### The six one-hot groups are satisfied -/

theorem sat_pcOh (hok : RunOK sh P cfg ev) (hi : i ≤ sh.steps) (hq : q < shS sh) :
    Sat (assignOf sh P cfg ev) ((pcOh sh i q).clauses) :=
  Oh.sat_range (o := pcOh sh i q) (a := assignOf sh P cfg ev) (k := rdPc sh P cfg ev i q)
    (K := shPc sh) rfl (rdPc_lt sh P cfg ev hok hq)
    (fun c hc => (assignOf_pc sh P cfg ev hi hq hc).trans decide_symm)
    (fun j hj => assignOf_apc sh P cfg ev hi hq hj)

theorem sat_stOh (hok : RunOK sh P cfg ev) (hi : i ≤ sh.steps) (hq : q < shS sh)
    (hx : x < shV sh) :
    Sat (assignOf sh P cfg ev) ((stOh sh i q x).clauses) :=
  Oh.sat_range (o := stOh sh i q x) (a := assignOf sh P cfg ev) (k := rdSt sh P cfg ev i q x)
    (K := shVal sh) rfl (rdSt_lt sh P cfg ev)
    (fun u hu => (assignOf_st sh P cfg ev hi hq hx hu).trans decide_symm)
    (fun j hj => assignOf_ast sh P cfg ev hi hq hx hj)

theorem sat_xeOh (hok : RunOK sh P cfg ev) (hi : i ≤ sh.steps) (hq : q < shS sh)
    (he : e < shE sh) :
    Sat (assignOf sh P cfg ev) ((xeOh sh i q e).clauses) :=
  Oh.sat_range (o := xeOh sh i q e) (a := assignOf sh P cfg ev) (k := rdXe sh P cfg ev i q e)
    (K := shVal sh) rfl (rdXe_lt sh P cfg ev)
    (fun u hu => (assignOf_xe sh P cfg ev hi hq he hu).trans decide_symm)
    (fun j hj => assignOf_axe sh P cfg ev hi hq he hj)

theorem sat_evOh (hok : RunOK sh P cfg ev) (hsub : univSub sh) (hi : i < sh.steps)
    (hrel : Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) ((evOh sh i).clauses) :=
  Oh.sat_range (o := evOh sh i) (a := assignOf sh P cfg ev) (k := rdEv sh P cfg ev i)
    (K := shEv sh) rfl (rdEv_lt sh P cfg ev hok hsub i hrel)
    (fun k hk => (assignOf_ev sh P cfg ev hi hk).trans decide_symm)
    (fun j hj => assignOf_aev sh P cfg ev hi hj)

theorem sat_dlOh (hok : RunOK sh P cfg ev) (hi : i < sh.steps) (hq : q < shS sh) :
    Sat (assignOf sh P cfg ev) ((dlOh sh i q).clauses) :=
  Oh.sat_range (o := dlOh sh i q) (a := assignOf sh P cfg ev) (k := rdDl sh P cfg ev i q)
    (K := shVal sh) rfl (rdDl_lt sh P cfg ev)
    (fun u hu => (assignOf_dl sh P cfg ev hi hq hu).trans decide_symm)
    (fun j hj => assignOf_adl sh P cfg ev hi hq hj)

theorem sat_frOh (hok : RunOK sh P cfg ev) (hi : i < sh.steps) (hq : q < shS sh) :
    Sat (assignOf sh P cfg ev) ((frOh sh i q).clauses) :=
  Oh.sat_range (o := frOh sh i q) (a := assignOf sh P cfg ev) (k := rdFr sh P cfg ev i q)
    (K := shD sh) rfl (rdFr_lt sh P cfg ev hok hq)
    (fun d hd => (assignOf_fr sh P cfg ev hi hq hd).trans decide_symm)
    (fun j hj => assignOf_afr sh P cfg ev hi hq hj)

/-- A clause of a concatenation of clause lists is a clause of one of them. -/
theorem sat_flatMap_id {L : List (List Clause)} {a : Assignment}
    (h : ∀ l ∈ L, ∀ cl ∈ l, Clause.eval a cl = true) :
    ∀ cl ∈ L.flatMap id, Clause.eval a cl = true := by
  intro cl hcl
  obtain ⟨g, hg, hgeq⟩ := List.mem_flatMap.mp hcl
  have h2 : cl ∈ g := by simpa using hgeq
  exact h g hg cl h2

/-- **Clause group 1 (one-hot).**  Every variable family of the encoding selects exactly one
alternative in the characteristic assignment. -/
theorem sat_oneHot (hok : RunOK sh P cfg ev) (hsub : univSub sh)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (oneHotClauses sh P) := by
  intro cl hcl
  rw [oneHotClauses, cnfOf] at hcl
  refine sat_flatMap_id ?_ cl hcl
  intro g hg cl' hcl'
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl'
    obtain ⟨q, hq, h3⟩ := List.mem_flatMap.mp h2
    have hi' : i ≤ sh.steps := Nat.le_of_lt_succ (by simpa using hi)
    have hq' : q < shS sh := by simpa using hq
    exact (sat_pcOh sh P cfg ev hok hi' hq') cl' h3
  · obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl'
    obtain ⟨q, hq, h3⟩ := List.mem_flatMap.mp h2
    obtain ⟨x, hx, h4⟩ := List.mem_flatMap.mp h3
    have hi' : i ≤ sh.steps := Nat.le_of_lt_succ (by simpa using hi)
    have hq' : q < shS sh := by simpa using hq
    have hx' : x < shV sh := by simpa using hx
    exact (sat_stOh sh P cfg ev hok hi' hq' hx') cl' h4
  · obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl'
    obtain ⟨q, hq, h3⟩ := List.mem_flatMap.mp h2
    obtain ⟨e, he, h4⟩ := List.mem_flatMap.mp h3
    have hi' : i ≤ sh.steps := Nat.le_of_lt_succ (by simpa using hi)
    have hq' : q < shS sh := by simpa using hq
    have he' : e < shE sh := by simpa using he
    exact (sat_xeOh sh P cfg ev hok hi' hq' he') cl' h4
  · obtain ⟨i, hi, h3⟩ := List.mem_flatMap.mp hcl'
    have hi' : i < sh.steps := by simpa using hi
    exact (sat_evOh sh P cfg ev hok hsub hi' (hrel i)) cl' h3
  · obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl'
    obtain ⟨q, hq, h3⟩ := List.mem_flatMap.mp h2
    have hi' : i < sh.steps := by simpa using hi
    have hq' : q < shS sh := by simpa using hq
    exact (sat_dlOh sh P cfg ev hok hi' hq') cl' h3
  · obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl'
    obtain ⟨q, hq, h3⟩ := List.mem_flatMap.mp h2
    have hi' : i < sh.steps := by simpa using hi
    have hq' : q < shS sh := by simpa using hq
    exact (sat_frOh sh P cfg ev hok hi' hq') cl' h3

variable (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev)

/-- A three-literal clause is satisfied when any one of its literals is true. -/
theorem clause3_left (a : Assignment) (l₁ l₂ l₃ : Lit) (h : l₁.eval a = true) :
    Clause.eval a [l₁, l₂, l₃] = true := by
  simp [Clause.eval, List.any_cons, List.any_nil, h]

theorem clause3_mid (a : Assignment) (l₁ l₂ l₃ : Lit) (h : l₂.eval a = true) :
    Clause.eval a [l₁, l₂, l₃] = true := by
  simp [Clause.eval, List.any_cons, List.any_nil, h]

theorem clause3_right (a : Assignment) (l₁ l₂ l₃ : Lit) (h : l₃.eval a = true) :
    Clause.eval a [l₁, l₂, l₃] = true := by
  simp [Clause.eval, List.any_cons, List.any_nil, h]

/-- A one-literal clause is satisfied when its literal is true. -/
theorem clause1 (a : Assignment) (l : Lit) (h : l.eval a = true) :
    Clause.eval a [l] = true := by
  simp [Clause.eval, List.any_cons, List.any_nil, h]

/-- Splitting a membership in a three-fold concatenation. -/
theorem sat_cnfOf3 {A B C : List Clause} {a : Assignment}
    (hA : ∀ cl ∈ A, Clause.eval a cl = true) (hB : ∀ cl ∈ B, Clause.eval a cl = true)
    (hC : ∀ cl ∈ C, Clause.eval a cl = true) :
    ∀ cl ∈ A ++ B ++ C, Clause.eval a cl = true := by
  intro cl hcl
  rcases List.mem_append.mp hcl with h | h
  · rcases List.mem_append.mp h with h | h
    · exact hA cl h
    · exact hB cl h
  · exact hC cl h

/-- Every Boolean is true or false, as an equation disjunction usable by rcases. -/
theorem bool_eq_cases (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-! ### Relating the event reader to the events themselves -/

/-- If the event at step i acts on session q, the recorded alternative is 1 + q. -/
theorem rdEv_act (h : ev i = Ev.act q m d) : rdEv sh P cfg ev i = 1 + q := by
  unfold rdEv
  rw [h]

/-- Converse: an event alternative of the form 1 + q with q a session index means the event
acts on q. -/
theorem rdEv_act_of_lt (hq : q < shS sh) (h : rdEv sh P cfg ev i = 1 + q) :
    ∃ m d, ev i = Ev.act q m d := by
  cases e : ev i with
  | idle =>
      have h1 : rdEv sh P cfg ev i = 0 := by unfold rdEv; rw [e]
      omega
  | ded t =>
      have h1 : rdEv sh P cfg ev i = 1 + shS sh + dedIx sh ((cfg i).kn) (uIdx sh (some t)) := by
        unfold rdEv
        rw [e]
      have h2 : shS sh ≤ q := by omega
      omega
  | act q' m' d' =>
      have h1 : rdEv sh P cfg ev i = 1 + q' := by unfold rdEv; rw [e]
      have : q' = q := by omega
      subst this
      exact ⟨m', d', rfl⟩

/-- The event acts on q exactly when the recorded alternative is 1 + q. -/
theorem evActs (hq : q < shS sh) :
    (∃ m d, ev i = Ev.act q m d) ↔ rdEv sh P cfg ev i = 1 + q :=
  ⟨fun ⟨m, d, h⟩ => rdEv_act sh P cfg ev h, rdEv_act_of_lt sh P cfg ev hq⟩

/-- The characteristic assignment's value on the 'q acts' literal. -/
theorem assignOf_evAct (hi : i < sh.steps) (hq : q < shS sh) :
    assignOf sh P cfg ev (evAct sh i q) = decide (rdEv sh P cfg ev i = 1 + q) :=
  assignOf_ev sh P cfg ev hi (by
    have : shEv sh = 1 + shS sh + nInst sh := rfl
    omega)

/-! ### Clause group 2: the initial configuration -/

theorem rget_map {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    rget (l.map f) i = (rget l i).map f := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons x xs ih => intro i; cases i <;> simp [rget, ih]

theorem init_pcOf_zero (hcfg0 : cfg 0 = initCfg P) (q : Nat) : pcOf (cfg 0) q = 0 := by
  rw [hcfg0]
  unfold pcOf sessAt initCfg
  rw [rget_map]
  cases rget P.sessions q with
  | none => rfl
  | some s => rfl

theorem init_readVar_none (hcfg0 : cfg 0 = initCfg P) (q x : Nat) :
    readVar x (storeOf (cfg 0) q) = none := by
  rw [hcfg0]
  unfold storeOf sessAt initCfg readVar Expr.lookup
  rw [rget_map]
  cases rget P.sessions q with
  | none => rfl
  | some s => rfl

/-- **Clause group 2 (initial state).**  Step 0 of the characteristic assignment is
ProtSat.initCfg: every program counter is 0, every store slot is unset, and the attacker holds
exactly the initial knowledge of ProtSat.Protocol.initKn. -/
theorem sat_init (hok : RunOK sh P cfg ev) (hcfg0 : cfg 0 = initCfg P) :
    Sat (assignOf sh P cfg ev) (initClauses sh P) := by
  refine fun cl hcl => sat_cnfOf3 ?_ ?_ ?_ cl hcl
  · intro cl hcl
    simp only [eachSess, List.mem_flatMap, List.mem_range] at hcl
    obtain ⟨q, hq, h2⟩ := hcl
    rw [initPcClauses, List.mem_map] at h2
    obtain ⟨c, hc, heq⟩ := h2
    subst heq
    split
    · rename_i hc0
      subst hc0
      have hv : assignOf sh P cfg ev (vpc sh 0 q 0) = true := by
        rw [assignOf_pc sh P cfg ev (Nat.zero_le _) (by simpa using hq) (by simpa using hc),
          show rdPc sh P cfg ev 0 q = pcOf (cfg 0) q from rfl, init_pcOf_zero P cfg hcfg0 q]
        exact decide_eq_true rfl
      exact clause1 _ _ (by simp [pos_eval, hv])
    · rename_i hc0
      have hv : assignOf sh P cfg ev (vpc sh 0 q c) = false := by
        rw [assignOf_pc sh P cfg ev (Nat.zero_le _) (by simpa using hq) (by simpa using hc),
          show rdPc sh P cfg ev 0 q = pcOf (cfg 0) q from rfl, init_pcOf_zero P cfg hcfg0 q]
        exact decide_eq_false (by intro h; omega)
      exact clause1 _ _ (by simp [neg_eval, hv])
  · intro cl hcl
    simp only [eachSess, eachVar, List.mem_flatMap, List.mem_range] at hcl
    obtain ⟨q, hq, x, hx, h2⟩ := hcl
    rw [initStClauses, List.mem_map] at h2
    obtain ⟨u, hu, heq⟩ := h2
    subst heq
    have hrd : rdSt sh P cfg ev 0 q x = sh.U.length := by
      unfold rdSt
      rw [init_readVar_none P cfg hcfg0 q x]
      rfl
    split
    · rename_i hu0
      subst hu0
      have hv : assignOf sh P cfg ev (vst sh 0 q x sh.U.length) = true := by
        rw [assignOf_st sh P cfg ev (Nat.zero_le _) (by simpa using hq) (by simpa using hx)
            (by simpa using hu), hrd]
        exact decide_eq_true rfl
      exact clause1 _ _ (by simp [pos_eval, hv])
    · rename_i hu0
      have hv : assignOf sh P cfg ev (vst sh 0 q x u) = false := by
        rw [assignOf_st sh P cfg ev (Nat.zero_le _) (by simpa using hq) (by simpa using hx)
            (by simpa using hu), hrd]
        exact decide_eq_false (fun he => hu0 he.symm)
      exact clause1 _ _ (by simp [neg_eval, hv])
  · intro cl hcl
    rw [initKnClauses, List.mem_map] at hcl
    obtain ⟨u, hu, heq⟩ := hcl
    subst heq
    have hkn : assignOf sh P cfg ev (vkn sh 0 u) = knHolds sh cfg 0 u :=
      assignOf_kn sh P cfg ev (Nat.zero_le _) (Nat.lt_succ_of_lt (by simpa using hu))
    have hkn0 : (cfg 0).kn = P.initKn := by rw [hcfg0]; rfl
    have h2 : knHolds sh cfg 0 u = initKnHolds sh P u := by
      unfold knHolds initKnHolds
      rw [hkn0]
      cases h : valAt sh u <;> rfl
    split
    · rename_i hh
      exact clause1 _ _ (by simp [pos_eval, hkn, h2, hh])
    · rename_i hh
      exact clause1 _ _ (by simp [pos_eval, hkn, h2, hh])


end ProtSat.Complete
