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

/-- Does the action at session q, program counter c read the delivered message? Exactly the
receive action: of the eight action kinds only recv uses the m field of Ev.act q m d, so only
there does the encoding need a name for it. -/
def readsDelivery (P : Protocol) (q c : Nat) : Prop :=
  ∃ a x, P.actionAt q c = some (Action.recv a x)

/-- Does the action at session q, program counter c read the nonce choice? Exactly the fresh
action: only fresh uses the d field, and the operational rule already demands d ∈ P.nonceDomain
there. -/
def readsNonce (P : Protocol) (q c : Nat) : Prop :=
  ∃ x N, P.actionAt q c = some (Action.fresh x N)

/-- **The run stays inside the shape** (the general form, stated for an arbitrary shape).
Twelve conditions, all of them instances of "the bounds can name what the run does":

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
8. the run has exactly the sessions the shape instantiates;
9. the shape's store-slot stride covers every variable the protocol reads - otherwise the
   store group a variable leaf of an evaluation gate refers to would not exist;
10. the shape's expression stride covers the protocol's expression table - otherwise the
   value group of an evaluation gate would not exist.
11. every variable an action writes has a store slot in the shape;
12. every position that has an action leaves room for the successor program counter.

At the shape of the analysis, conditions 9 to 12 are theorems about the protocol
(ProtSat.Encoding.lt_shV_of_mem, ProtSat.Encoding.eIdx_lt, ProtSat.Encoding.lt_shV_of_written,
ProtSat.Encoding.lt_shPc_succ), not hypotheses.

These are precisely the conditions under which a finite encoding can represent the run at all
- a run that leaves the universe has no finite name, and a run whose session index is not
instantiated has no event alternative. -/
structure RunOK (sh : Shape) (P : Protocol) (cfg : Nat → Cfg) (ev : Nat → Ev) : Prop where
  /-- 1. -/
  knU : ∀ i t, t ∈ (cfg i).kn → t ∈ sh.U
  /-- 2. -/
  storeU : ∀ i q v, q < sh.nS1 → v ∈ storeVals (storeOf (cfg i) q) → v ∈ sh.U
  /-- 3. The acting session is an instantiated one, and the two event fields are bounded *where
  they are read*: only a receive uses the delivered message and only a generation uses the nonce
  choice, so the other six action rules are not asked to name a value they ignore. Unlike the
  unconditional demand it replaces, this one follows from the public bound
  (ProtSat.BoundedExec.actM_of_recv, actD_of_fresh). -/
  actB : ∀ i q m d, ev i = Ev.act q m d → q < sh.nS1 ∧
    (readsDelivery P q (pcOf (cfg i) q) -> m ∈ sh.U) ∧
    (readsNonce P q (pcOf (cfg i) q) -> d ∈ sh.D)
  /-- 4. -/
  dedU : ∀ i t, ev i = Ev.ded t → t ∈ sh.U
  /-- 5. -/
  pcB : ∀ i q, q < sh.nS1 → pcOf (cfg i) q < shPc sh
  /-- 6. -/
  varB : ∀ i q x, q < sh.nS1 → x ∈ (storeOf (cfg i) q).map Prod.fst → x < shV sh
  /-- 7. -/
  exprB : ∀ i q e, e ∈ allExprs P → admissible sh (Expr.eval e (storeOf (cfg i) q)) = true
  /-- 8. -/
  sessLen : ∀ i, (cfg i).sess.length = sh.nS1
  /-- 9. -/
  varsB : ∀ E ∈ allExprs P, ∀ x ∈ Expr.vars E, x < shV sh
  /-- 10. -/
  eIdxB : ∀ E ∈ allExprs P, eIdx P E < shE sh
  /-- 11. every variable an action writes has a store slot in the shape. -/
  writtenB : ∀ q c act, P.actionAt q c = some act → ∀ x ∈ act.written, x < shV sh
  /-- 12. a position with an action leaves room for the successor program counter. -/
  pcActB : ∀ q c, P.actionAt q c ≠ none → c + 1 < shPc sh

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

/-- The twelve boundedness conditions, as named projections.  They are kept as lemmas so that
a proof says which bound it is using. -/
theorem runOK_knU (h : RunOK sh P cfg ev) : ∀ i t, t ∈ (cfg i).kn → t ∈ sh.U := h.knU

theorem runOK_storeU (h : RunOK sh P cfg ev) : ∀ i q v, q < sh.nS1 →
    v ∈ storeVals (storeOf (cfg i) q) → v ∈ sh.U := h.storeU

theorem runOK_act (h : RunOK sh P cfg ev) : ∀ i q m d, ev i = Ev.act q m d →
    q < sh.nS1 ∧ (readsDelivery P q (pcOf (cfg i) q) -> m ∈ sh.U) ∧
      (readsNonce P q (pcOf (cfg i) q) -> d ∈ sh.D) := h.actB

/-- The delivered message is a universe message when the action reads it. -/
theorem runOK_act_mU (h : RunOK sh P cfg ev) {i q : Nat} {m : Term} {d : NonceName}
    (he : ev i = Ev.act q m d) (hr : readsDelivery P q (pcOf (cfg i) q)) : m ∈ sh.U :=
  (h.actB i q m d he).2.1 hr

/-- The nonce choice is in the domain when the action reads it. -/
theorem runOK_act_dD (h : RunOK sh P cfg ev) {i q : Nat} {m : Term} {d : NonceName}
    (he : ev i = Ev.act q m d) (hr : readsNonce P q (pcOf (cfg i) q)) : d ∈ sh.D :=
  (h.actB i q m d he).2.2 hr

theorem runOK_dedU (h : RunOK sh P cfg ev) : ∀ i t, ev i = Ev.ded t → t ∈ sh.U := h.dedU

theorem runOK_pc (h : RunOK sh P cfg ev) : ∀ i q, q < sh.nS1 → pcOf (cfg i) q < shPc sh := h.pcB

theorem runOK_var (h : RunOK sh P cfg ev) : ∀ i q x, q < sh.nS1 →
    x ∈ (storeOf (cfg i) q).map Prod.fst → x < shV sh := h.varB

theorem runOK_expr (h : RunOK sh P cfg ev) : ∀ i q e, e ∈ allExprs P →
    admissible sh (Expr.eval e (storeOf (cfg i) q)) = true := h.exprB

theorem runOK_sessLen (h : RunOK sh P cfg ev) : ∀ i, (cfg i).sess.length = sh.nS1 := h.sessLen

/-- The shape's store-slot stride covers every variable the protocol reads; this is what the
variable leaf of an evaluation gate needs. -/
theorem runOK_vars (h : RunOK sh P cfg ev) :
    ∀ E ∈ allExprs P, ∀ x ∈ Expr.vars E, x < shV sh := h.varsB

/-- The shape's expression stride covers the protocol's expression table; this is what the
value group of an evaluation gate needs. -/
theorem runOK_eIdx (h : RunOK sh P cfg ev) : ∀ E ∈ allExprs P, eIdx P E < shE sh := h.eIdxB

/-- Every variable an action writes has a store slot in the shape. -/
theorem runOK_written (h : RunOK sh P cfg ev) : ∀ q c act, P.actionAt q c = some act →
    ∀ x ∈ act.written, x < shV sh := h.writtenB

/-- A position that has an action leaves room for the successor program counter. -/
theorem runOK_pcAct (h : RunOK sh P cfg ev) : ∀ q c, P.actionAt q c ≠ none →
    c + 1 < shPc sh := h.pcActB

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
of it, so they too have names.  ProtSat.Bounded.univ is built subterm-closed on purpose, and
ProtSat.Complete.univSub_shapeOf below proves it - so the condition is a theorem of the
construction, not a hypothesis a query has to arrange. -/
def univSub (sh : Shape) : Prop := ∀ t ∈ sh.U, ∀ u ∈ subtermsL t, u ∈ sh.U

/-! ### The universe is subterm-closed by construction

`univSub` used to be carried as a hypothesis by `encoding_complete` and by every bridge that
consumes it, each of them discharging it by `decide` on a concrete protocol - which proved the
fact about an example and said nothing about the construction. But the construction **is** the
reason it is true. `Bounded.univ` is built as

    (closeOne P.agents (domainKeys P.agents))^[B.rounds] (subtermClosureL (seeds P)) |>.eraseDups

whose base is subterm-closed by `Bounded.subtermClosureL_closed`, whose seeds already contain
every agent and every domain key, and whose one round only ever builds `pair x y`, `encS m k`,
`encA m a` and `hash m` out of messages the round already has - so the subterms of anything it
adds were already present. The lemmas below turn that into `univSub_shapeOf`, and `hsub` is
gone from every signature downstream. -/

/-- A list of messages is **subterm-closed** when it contains the subterms of each of its members.
`univSub` is this predicate read at a shape's universe. -/
def SubtermClosed (L : List Term) : Prop := ∀ t ∈ L, ∀ u ∈ subtermsL t, u ∈ L

/-- The subterm closure of any seed list is subterm-closed: that is what `subtermClosureL` is for. -/
theorem subtermClosureL_SubtermClosed (S : List Term) : SubtermClosed (subtermClosureL S) := by
  intro t ht u hu
  exact subtermClosureL_closed ht hu

/-- A message of the base list survives every closure round: `closeOne` never removes anything. -/
theorem mem_iterate_closeOne {ag : List Agent} {ks : List Key} {U : List Term} (t : Term)
    (ht : t ∈ U) : ∀ n, t ∈ ((fun W => closeOne ag ks W)^[n] U) := by
  intro n
  induction n with
  | zero => exact ht
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact mem_closeOne ih

theorem mem_closeOne_pair {ag : List Agent} {ks : List Key} {U : List Term} {x y : Term}
    (hx : x ∈ U) (hy : y ∈ U) : Term.pair x y ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, y, hy, rfl⟩)))

theorem mem_closeOne_encS {ag : List Agent} {ks : List Key} {U : List Term} {m : Term} {k : Key}
    (hm : m ∈ U) (hk : k ∈ ks) : Term.encS m k ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨m, hm, k, hk, rfl⟩))

theorem mem_closeOne_encA {ag : List Agent} {ks : List Key} {U : List Term} {m : Term} {a : Agent}
    (hm : m ∈ U) (ha : a ∈ ag) : Term.encA m a ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨m, hm, a, ha, rfl⟩)

theorem mem_closeOne_hash {ag : List Agent} {ks : List Key} {U : List Term} {m : Term}
    (hm : m ∈ U) : Term.hash m ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inr ⟨m, hm, rfl⟩

/-- **One closure round adds nothing whose subterms were not already present.** Each generated
message is built from a base message, so its parts are base messages or their subterms; the agents
and keys it may mention are in the base by hypothesis. -/
theorem subtermsL_subset_closeOne {ag : List Agent} {ks : List Key} {U : List Term}
    (hU : SubtermClosed U) (hag : ∀ a ∈ ag, Term.agent a ∈ U)
    (hks : ∀ k ∈ ks, Term.key k ∈ U) {t : Term} (ht : t ∈ closeOne ag ks U) :
    subtermsL t ⊆ closeOne ag ks U := by
  have hUin : ∀ s, s ∈ U -> s ∈ closeOne ag ks U := fun s hs => mem_closeOne hs
  have hsubU : ∀ s, s ∈ U -> subtermsL s ⊆ closeOne ag ks U := fun s hs u hu =>
    mem_closeOne (hU s hs u hu)
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map] at ht
  intro u hu
  rcases ht with (((hU' | ⟨x, hx, y, hy, rfl⟩) | ⟨m, hm, k, hk, rfl⟩) | ⟨m, hm, a, ha, rfl⟩)
    | ⟨m, hm, rfl⟩
  · exact hsubU t hU' hu
  · have hmem : u ∈ Term.pair x y :: subtermsL x ++ subtermsL y := hu
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with (rfl | hz) | hz
    · exact mem_closeOne_pair hx hy
    · exact hsubU x hx hz
    · exact hsubU y hy hz
  · have hmem : u ∈ Term.encS m k :: subtermsL m ++ [Term.key k] := hu
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with (rfl | hz) | (rfl | hnil)
    · exact mem_closeOne_encS hm hk
    · exact hsubU m hm hz
    · exact hUin _ (hks k hk)
    · cases hnil
  · have hmem : u ∈ Term.encA m a :: subtermsL m ++ [Term.agent a] := hu
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with (rfl | hz) | (rfl | hnil)
    · exact mem_closeOne_encA hm ha
    · exact hsubU m hm hz
    · exact hUin _ (hag a ha)
    · cases hnil
  · have hmem : u ∈ Term.hash m :: subtermsL m := hu
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hz
    · exact mem_closeOne_hash hm
    · exact hsubU m hm hz

/-- **One closure round preserves subterm-closure**, provided the agents and keys it closes under
are already present - which they are, because the seeds put them in the base. -/
theorem SubtermClosed.mono_closeOne {ag : List Agent} {ks : List Key} {U : List Term}
    (hU : SubtermClosed U) (hag : ∀ a ∈ ag, Term.agent a ∈ U)
    (hks : ∀ k ∈ ks, Term.key k ∈ U) : SubtermClosed (closeOne ag ks U) := fun t ht u hu =>
  subtermsL_subset_closeOne hU hag hks ht hu

/-- Subterm-closure survives every number of closure rounds. -/
theorem SubtermClosed.iterate {ag : List Agent} {ks : List Key} {U : List Term}
    (hU : SubtermClosed U) (hag : ∀ a ∈ ag, Term.agent a ∈ U)
    (hks : ∀ k ∈ ks, Term.key k ∈ U) :
    ∀ n, SubtermClosed ((fun W => closeOne ag ks W)^[n] U) := by
  intro n
  induction n with
  | zero => exact hU
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ih.mono_closeOne ?_ ?_
      · intro a ha
        exact mem_iterate_closeOne _ (hag a ha) n
      · intro k hk
        exact mem_iterate_closeOne _ (hks k hk) n

/-- Removing duplicates preserves subterm-closure. -/
theorem SubtermClosed.eraseDups {U : List Term} (h : SubtermClosed U) :
    SubtermClosed U.eraseDups := by
  intro t ht u hu
  apply List.mem_eraseDups.mpr
  exact h t (List.mem_eraseDups.mp ht) u hu

/-- **The universe of a protocol under any bounds is subterm-closed.** The base is the subterm
closure of the seeds, the seeds already contain every agent and every domain key, and each round
only builds messages out of parts it already had. -/
theorem univ_SubtermClosed (P : Protocol) (B : Bounds) : SubtermClosed (univ P B) := by
  have hbase : SubtermClosed (subtermClosureL (seeds P)) := subtermClosureL_SubtermClosed _
  have hag : ∀ a ∈ P.agents, Term.agent a ∈ subtermClosureL (seeds P) := by
    intro a ha
    exact mem_subtermClosureL (mem_seeds_agent ha)
  have hks : ∀ k ∈ domainKeys P.agents, Term.key k ∈ subtermClosureL (seeds P) := by
    intro k hk
    refine mem_subtermClosureL ?_
    show Term.key k ∈ seeds P
    simp only [seeds, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩)))
  have hI := hbase.iterate hag hks
  have huniv : univ P B =
      ((fun W => closeOne P.agents (domainKeys P.agents) W)^[B.rounds]
        (subtermClosureL (seeds P))).eraseDups := rfl
  rw [huniv]
  exact (hI B.rounds).eraseDups

/-- **`univSub` is a theorem of the construction, not a hypothesis about the query.** Every subterm
of every universe message is itself a universe message, for every protocol and every bounds. -/
theorem univSub_shapeOf (P : Protocol) (B : Bounds) : univSub (shapeOf P B) := by
  intro t ht u hu
  exact univ_SubtermClosed P B t ht u hu

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
      · have h1 : rdFr sh P cfg ev i q = ixOf d sh.D := by unfold rdFr; rw [h]; exact if_pos hq
        rw [h1]
        have hs : shD sh = sh.D.length + 1 := rfl
        rw [hs]
        exact Nat.lt_of_le_of_lt (ixOf_le sh.D d) (Nat.lt_succ_self _)
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


/-- **Clause group 3 (frame conditions).**  Knowledge never shrinks, and a session that does
not act keeps its program counter and its whole store: both are instances of the frame lemmas
of ProtSat.Operational, which the characteristic assignment reads directly. -/
theorem sat_frame (hok : RunOK sh P cfg ev)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (frameClauses sh) := by
  intro cl hcl
  simp only [frameClauses, cnfOf, eachStep, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, hcl'⟩ := hcl
  rw [List.mem_append] at hcl'
  rcases hcl' with hkn | hsess
  · -- knowledge monotonicity
    simp only [frameKnClauses, mapMsg, List.mem_range] at hkn
    rw [List.mem_map] at hkn
    obtain ⟨u, hu, heq⟩ := hkn
    subst heq
    have hu' : u < shVal sh := by
      have hs : shVal sh = sh.U.length + 1 := rfl
      rw [hs]
      exact Nat.lt_succ_of_lt (by simpa using hu)
    have hc1 : assignOf sh P cfg ev (vkn sh i u) = knHolds sh cfg i u :=
      assignOf_kn sh P cfg ev (Nat.le_of_lt hi) hu'
    have hc2 : assignOf sh P cfg ev (vkn sh (i + 1) u) = knHolds sh cfg (i + 1) u :=
      assignOf_kn sh P cfg ev (Nat.succ_le_of_lt hi) hu'
    rcases bool_eq_cases (assignOf sh P cfg ev (vkn sh i u)) with h1 | h1
    · have hk : knHolds sh cfg i u = true := by rw [← hc1]; exact h1
      have hk2 : knHolds sh cfg (i + 1) u = true := by
        cases h : valAt sh u with
        | none => simp [knHolds, h] at hk
        | some t =>
            have hmem : t ∈ (cfg (i + 1)).kn :=
              Rel.kn_mono (hrel i) t (by simpa [knHolds, h] using hk)
            simpa [knHolds, h] using hmem
      exact clause2_right _ _ _ (by rw [pos_eval, hc2]; exact hk2)
    · exact clause2_left _ _ _ (by simp [neg_eval, h1])
  · simp only [eachSess, List.mem_flatMap, List.mem_range] at hsess
    obtain ⟨q, hq, hcl''⟩ := hsess
    rw [frameSessClauses, List.mem_append] at hcl''
    rcases hcl'' with hpc | hst
    · rw [List.mem_map] at hpc
      obtain ⟨c, hc, heq⟩ := hpc
      subst heq
      rcases bool_eq_cases (assignOf sh P cfg ev (evAct sh i q)) with hact | hact
      · exact clause3_left _ _ _ _ (by rw [pos_eval, hact])
      · have hne : ¬ ∃ m d, ev i = Ev.act q m d := by
          intro ex
          obtain ⟨m, d, hex⟩ := ex
          have h4 : rdEv sh P cfg ev i = 1 + q := rdEv_act sh P cfg ev hex
          have h5 : assignOf sh P cfg ev (evAct sh i q)
              = decide (rdEv sh P cfg ev i = 1 + q) := assignOf_evAct sh P cfg ev hi hq
          rw [h5, h4] at hact
          exact by simpa using hact
        obtain ⟨hpc', _, _⟩ := Rel.noAct (hrel i) q hne
        rcases bool_eq_cases (assignOf sh P cfg ev (vpc sh i q c)) with h2 | h2
        · have h9 : rdPc sh P cfg ev (i + 1) q = c := by
            show pcOf (cfg (i + 1)) q = c
            rw [hpc']
            have h2'' : decide (rdPc sh P cfg ev i q = c) = true := by
              rw [← assignOf_pc sh P cfg ev (Nat.le_of_lt hi) hq (by simpa using hc)]
              exact h2
            exact of_decide_eq_true h2''
          exact clause3_right _ _ _ _ (by
            rw [pos_eval, assignOf_pc sh P cfg ev (Nat.succ_le_of_lt hi) hq (by simpa using hc)]
            exact decide_eq_true h9)
        · exact clause3_mid _ _ _ _ (by simp [neg_eval, h2])
    · obtain ⟨x, hx, h3⟩ := List.mem_flatMap.mp hst
      simp only [mapVal, List.mem_range] at h3
      rw [List.mem_map] at h3
      obtain ⟨u, hu, heq⟩ := h3
      subst heq
      rcases bool_eq_cases (assignOf sh P cfg ev (evAct sh i q)) with hact | hact
      · exact clause3_left _ _ _ _ (by rw [pos_eval, hact])
      · have hne : ¬ ∃ m d, ev i = Ev.act q m d := by
          intro ex
          obtain ⟨m, d, hex⟩ := ex
          have h4 : rdEv sh P cfg ev i = 1 + q := rdEv_act sh P cfg ev hex
          have h5 : assignOf sh P cfg ev (evAct sh i q)
              = decide (rdEv sh P cfg ev i = 1 + q) := assignOf_evAct sh P cfg ev hi hq
          rw [h5, h4] at hact
          exact by simpa using hact
        obtain ⟨_, hst', _⟩ := Rel.noAct (hrel i) q hne
        rcases bool_eq_cases (assignOf sh P cfg ev (vst sh i q x u)) with h2 | h2
        · have h9 : rdSt sh P cfg ev (i + 1) q x = u := by
            show uIdx sh (readVar x (storeOf (cfg (i + 1)) q)) = u
            rw [hst']
            have h2'' : decide (rdSt sh P cfg ev i q x = u) = true := by
              rw [← assignOf_st sh P cfg ev (Nat.le_of_lt hi) hq (by simpa using hx)
                (by simpa using hu)]
              exact h2
            exact of_decide_eq_true h2''
          exact clause3_right _ _ _ _ (by
            rw [pos_eval, assignOf_st sh P cfg ev (Nat.succ_le_of_lt hi) hq (by simpa using hx)
              (by simpa using hu)]
            exact decide_eq_true h9)
        · exact clause3_mid _ _ _ _ (by simp [neg_eval, h2])

/-- The value number of an expression-table entry, stated at the expression itself. -/
theorem rdXe_eIdx {E : Expr} (hE : E ∈ allExprs P) :
    rdXe sh P cfg ev i q (eIdx P E) = uIdx sh (Expr.eval E (storeOf (cfg i) q)) := by
  unfold rdXe
  rw [eAt_eIdx hE]

/-- Under the characteristic assignment the value group of a table entry decodes to the value
the run computes for that entry. -/
theorem decode_rdXe (hok : RunOK sh P cfg ev) (hi : i ≤ sh.steps) (hq : q < shS sh)
    (he : e < shE sh) :
    (xeOh sh i q e).decode (assignOf sh P cfg ev) = some (rdXe sh P cfg ev i q e) :=
  Oh.decode_of_true (sat_xeOh sh P cfg ev hok hi hq he)
    (List.mem_range.mpr (rdXe_lt sh P cfg ev))
    (show assignOf sh P cfg ev (vxe sh i q e (rdXe sh P cfg ev i q e)) = true from
      ((assignOf_xe sh P cfg ev hi hq he (rdXe_lt sh P cfg ev)).trans
        (decide_eq_true rfl)))

/-- Under the characteristic assignment the store group of a slot decodes to the value the
run holds in that slot. -/
theorem decode_rdSt (hok : RunOK sh P cfg ev) (hi : i ≤ sh.steps) (hq : q < shS sh)
    (hx : x < shV sh) :
    (stOh sh i q x).decode (assignOf sh P cfg ev) = some (rdSt sh P cfg ev i q x) :=
  Oh.decode_of_true (sat_stOh sh P cfg ev hok hi hq hx)
    (List.mem_range.mpr (rdSt_lt sh P cfg ev))
    (show assignOf sh P cfg ev (vst sh i q x (rdSt sh P cfg ev i q x)) = true from
      ((assignOf_st sh P cfg ev hi hq hx (rdSt_lt sh P cfg ev)).trans
        (decide_eq_true rfl)))

/-! ### The three shapes of an evaluation gate -/

/-- A unary step: the value of the parent is the unary step applied to the value of the child. -/
theorem rdXe_unary (hok : RunOK sh P cfg ev) {E c : Expr} (hE : E ∈ allExprs P)
    (hchild : Expr.child1 E = some c) :
    rdXe sh P cfg ev i q (eIdx P E) = f1 sh E (rdXe sh P cfg ev i q (eIdx P c)) := by
  have hc : c ∈ allExprs P := mem_allExprs_child1 hE hchild
  rw [rdXe_eIdx sh P cfg ev hE, rdXe_eIdx sh P cfg ev hc, f1]
  rw [Expr.eval_child1 hchild]
  rw [admissible_valAt_uIdx _ (runOK_expr sh P cfg ev hok i q c hc)]

/-- A binary step: the value of the parent is the binary step applied to the values of its two
children. -/
theorem rdXe_binary (hok : RunOK sh P cfg ev) {E a b : Expr} (hE : E ∈ allExprs P)
    (hchild : Expr.child2 E = some (a, b)) :
    rdXe sh P cfg ev i q (eIdx P E)
      = f2 sh E (rdXe sh P cfg ev i q (eIdx P a)) (rdXe sh P cfg ev i q (eIdx P b)) := by
  obtain ⟨ha, hb⟩ := mem_allExprs_child2 hE hchild
  rw [rdXe_eIdx sh P cfg ev hE, rdXe_eIdx sh P cfg ev ha, rdXe_eIdx sh P cfg ev hb, f2]
  rw [Expr.eval_child2 hchild]
  rw [admissible_valAt_uIdx _ (runOK_expr sh P cfg ev hok i q a ha),
      admissible_valAt_uIdx _ (runOK_expr sh P cfg ev hok i q b hb)]

/-- A leaf that reads the store: the value of the entry is the value of the slot. -/
theorem rdXe_var {E : Expr} (hE : E ∈ allExprs P) (hx : E = Expr.var x) :
    rdXe sh P cfg ev i q (eIdx P E) = rdSt sh P cfg ev i q x := by
  rw [rdXe_eIdx sh P cfg ev hE, hx]
  unfold rdSt
  rfl

/-- An expression with no children and no store read is a constant of the DSL. -/
theorem eval_eq_constVal (E : Expr) (s : List (Var × Term))
    (h1 : Expr.child1 E = none) (h2 : Expr.child2 E = none)
    (hv : ∀ x, E ≠ Expr.var x) : Expr.eval E s = Expr.constVal E := by
  cases E with
  | agent A | nonce N | shrk a b | pubk a | privk a => rfl
  | var x => exact absurd rfl (hv x)
  | pair a b | encS a b | decS a b => exact absurd h2 (by simp [Expr.child2])
  | encA a b | hash a | fst a | snd a | decA a b => exact absurd h1 (by simp [Expr.child1])

/-- A constant leaf: the value of the entry is the message it denotes. -/
theorem rdXe_const {E : Expr} (hE : E ∈ allExprs P)
    (h1 : Expr.child1 E = none) (h2 : Expr.child2 E = none)
    (hv : ∀ x, E ≠ Expr.var x) :
    rdXe sh P cfg ev i q (eIdx P E) = uIdx sh (Expr.constVal E) := by
  rw [rdXe_eIdx sh P cfg ev hE, eval_eq_constVal E (storeOf (cfg i) q) h1 h2 hv]

/-- The gate of a constant leaf is the single clause pinning the entry to its message. -/
theorem evalLeafGate_const {E : Expr} (h1 : Expr.child1 E = none) (h2 : Expr.child2 E = none)
    (hv : ∀ x, E ≠ Expr.var x) :
    evalLeafGate sh P i q e E =
      [[pos (vxe sh i q e (uIdx sh (Expr.constVal E)))]] := by
  cases E with
  | var x => exact absurd rfl (hv x)
  | agent A | nonce N | shrk a b | pubk a | privk a => rfl
  | pair a b | encS a b | decS a b => exact absurd h2 (by simp [Expr.child2])
  | encA a b | hash a | fst a | snd a | decA a b => exact absurd h1 (by simp [Expr.child1])

/-- **Clause group 4 (Tseitin evaluation gates).**  The expression table of the encoding is a
circuit: every entry is either a constant of the DSL, a read of a store slot, or one
constructor/destructor step applied to the entries of its children, and the clauses of
ProtSat.evalGate are exactly the definitional (Tseitin) clauses of that circuit, generated by
the guarded forward families of ProtSat.OneHot.

The characteristic assignment records for entry `e` the value `rdXe e = uIdx (eval e (store of
the run))`.  The three shapes of a gate are satisfied because that record obeys the same
equations as the semantics:

* a unary entry: `rdXe E = f1 E (rdXe c)` - ProtSat.Expr.eval_child1 plus the seventh
  component of RunOK, which says the intermediate value is a universe message and so can be
  named by `uIdx`;
* a binary entry: `rdXe E = f2 E (rdXe ca) (rdXe cb)` - ProtSat.Expr.eval_child2, likewise;
* a leaf: a variable entry repeats its store slot (the ninth component of RunOK makes sure the
  store group exists), and a constant entry is pinned to the message it denotes.

Each case is then one application of the corresponding completeness theorem
(ProtSat.OneHot.fwdClausesOn_complete, ProtSat.OneHot.fwd2ClausesOn_complete), which is the
"if the recorded values respect the gate, the gate's clauses are satisfied" direction of the
Tseitin translation. -/
theorem sat_eval (hok : RunOK sh P cfg ev) :
    Sat (assignOf sh P cfg ev) (evalClauses sh P) := by
  intro cl hcl
  simp only [evalClauses, cnfOf, eachStep1, eachSess, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, h2⟩ := hcl
  obtain ⟨q, hq, h3⟩ := h2
  rw [evalClausesAt] at h3
  obtain ⟨E, hE, h4⟩ := List.mem_flatMap.mp h3
  have hi' : i ≤ sh.steps := Nat.le_of_lt_succ (by simpa using hi)
  have hq' : q < shS sh := by simpa using hq
  have heE : eIdx P E < shE sh := runOK_eIdx sh P cfg ev hok E hE
  cases h : Expr.child1 E with
  | some c =>
    -- unary gate
    rw [evalGate, h] at h4
    have hc : c ∈ allExprs P := mem_allExprs_child1 hE h
    have hce : eIdx P c < shE sh := runOK_eIdx sh P cfg ev hok c hc
    have hsat : Sat (assignOf sh P cfg ev)
        (fwdClausesOn [] (xeOh sh i q (eIdx P c))
          (fun u => pos (vxe sh i q (eIdx P E) (f1 sh E u)))) := by
      refine fwdClausesOn_complete (sat_xeOh sh P cfg ev hok hi' hq' hce) ?_
      intro u hu hd
      have hdx := decode_rdXe sh P cfg ev hok hi' hq' hce
      have : u = rdXe sh P cfg ev i q (eIdx P c) := Option.some.inj (hd.symm.trans hdx)
      subst this
      have hgoal : assignOf sh P cfg ev (vxe sh i q (eIdx P E) (f1 sh E (rdXe sh P cfg ev i q (eIdx P c))))
          = decide (rdXe sh P cfg ev i q (eIdx P E) = f1 sh E (rdXe sh P cfg ev i q (eIdx P c))) :=
        assignOf_xe sh P cfg ev hi' hq' heE (uIdx_lt' sh _)
      rw [pos_eval, hgoal, rdXe_unary sh P cfg ev hok hE h]
      exact decide_eq_true rfl
    exact hsat cl h4
  | none =>
  cases h2 : Expr.child2 E with
  | some ab =>
    obtain ⟨ca, cb⟩ := ab
    -- binary gate
    rw [evalGate, h, h2] at h4
    obtain ⟨ha, hb⟩ := mem_allExprs_child2 hE h2
    have hae : eIdx P ca < shE sh := runOK_eIdx sh P cfg ev hok ca ha
    have hbe : eIdx P cb < shE sh := runOK_eIdx sh P cfg ev hok cb hb
    have hsat : Sat (assignOf sh P cfg ev)
        (fwd2ClausesOn [] (xeOh sh i q (eIdx P ca)) (xeOh sh i q (eIdx P cb))
          (fun u v => pos (vxe sh i q (eIdx P E) (f2 sh E u v)))) := by
      refine fwd2ClausesOn_complete (sat_xeOh sh P cfg ev hok hi' hq' hae)
        (sat_xeOh sh P cfg ev hok hi' hq' hbe) ?_
      intro u hu v hv hd hd'
      have hdx := decode_rdXe sh P cfg ev hok hi' hq' hae
      have hdy := decode_rdXe sh P cfg ev hok hi' hq' hbe
      have : u = rdXe sh P cfg ev i q (eIdx P ca) := Option.some.inj (hd.symm.trans hdx)
      have : v = rdXe sh P cfg ev i q (eIdx P cb) := Option.some.inj (hd'.symm.trans hdy)
      subst this
      subst this
      have hgoal : assignOf sh P cfg ev
            (vxe sh i q (eIdx P E)
              (f2 sh E (rdXe sh P cfg ev i q (eIdx P ca)) (rdXe sh P cfg ev i q (eIdx P cb))))
          = decide (rdXe sh P cfg ev i q (eIdx P E)
              = f2 sh E (rdXe sh P cfg ev i q (eIdx P ca)) (rdXe sh P cfg ev i q (eIdx P cb))) :=
        assignOf_xe sh P cfg ev hi' hq' heE (uIdx_lt' sh _)
      rw [pos_eval, hgoal, rdXe_binary sh P cfg ev hok hE h2]
      exact decide_eq_true rfl
    exact hsat cl h4
  | none =>
    -- leaf
    rw [evalGate, h, h2] at h4
    by_cases hxv : ∃ x, E = Expr.var x
    · obtain ⟨x, rfl⟩ := hxv
      have hx : x < shV sh :=
        runOK_vars sh P cfg ev hok (Expr.var x) hE x (by simp [Expr.vars])
      have hsat : Sat (assignOf sh P cfg ev)
          (fwdClausesOn [] (stOh sh i q x)
            (fun u => pos (vxe sh i q (eIdx P (Expr.var x)) u))) := by
        refine fwdClausesOn_complete (sat_stOh sh P cfg ev hok hi' hq' hx) ?_
        intro u hu hd
        have hdx := decode_rdSt sh P cfg ev hok hi' hq' hx
        have : u = rdSt sh P cfg ev i q x := Option.some.inj (hd.symm.trans hdx)
        subst this
        have hgoal : assignOf sh P cfg ev
              (vxe sh i q (eIdx P (Expr.var x)) (rdSt sh P cfg ev i q x))
            = decide (rdXe sh P cfg ev i q (eIdx P (Expr.var x)) = rdSt sh P cfg ev i q x) :=
          assignOf_xe sh P cfg ev hi' hq' heE (uIdx_lt' sh _)
        rw [pos_eval, hgoal, rdXe_var sh P cfg ev hE rfl]
        exact decide_eq_true rfl
      exact hsat cl h4
    · -- constant leaf
      have hv : ∀ y, E ≠ Expr.var y := by
        intro y hy
        exact hxv ⟨y, hy⟩
      rw [evalLeafGate_const sh P (i := i) (q := q) (e := eIdx P E) h h2 hv] at h4
      simp only [List.mem_singleton] at h4
      subst h4
      have hgoal : assignOf sh P cfg ev (vxe sh i q (eIdx P E) (uIdx sh (Expr.constVal E)))
          = decide (rdXe sh P cfg ev i q (eIdx P E) = uIdx sh (Expr.constVal E)) :=
        assignOf_xe sh P cfg ev hi' hq' heE (uIdx_lt' sh _)
      exact clause1 _ _ (by
        rw [pos_eval, hgoal, rdXe_const sh P cfg ev hE h h2 hv]
        exact decide_eq_true rfl)

/-- A satisfied prefix satisfies the whole clause. -/
theorem clause_eval_append_left_true (a : Assignment) (g t : List Lit)
    (h : Clause.eval a g = true) : Clause.eval a (g ++ t) = true := by
  rw [clause_eval_any] at *
  obtain ⟨l, hl, he⟩ := h
  exact ⟨l, List.mem_append_left t hl, he⟩

/-- **The act guard.**  The two guard literals of ProtSat.actGuard are false exactly when the
run really has session q acting while its program counter is c. -/
theorem actGuard_false (hok : RunOK sh P cfg ev) (hi : i < sh.steps) (hq : q < shS sh)
    (hc : c < shPc sh) :
    Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c) = false <->
      (∃ m d, ev i = Ev.act q m d) ∧ rdPc sh P cfg ev i q = c := by
  have h1 : (assignOf sh P cfg ev (evAct sh i q) = true) <-> ∃ m d, ev i = Ev.act q m d := by
    rw [assignOf_evAct sh P cfg ev hi hq]
    refine ⟨fun h => (evActs sh P cfg ev hq).mpr (of_decide_eq_true h),
      fun h => decide_eq_true ((evActs sh P cfg ev hq).mp h)⟩
  have h2 : (assignOf sh P cfg ev (vpc sh i q c) = true) <-> rdPc sh P cfg ev i q = c := by
    rw [assignOf_pc sh P cfg ev (Nat.le_of_lt hi) hq hc]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  have hbase : Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c) = false <->
      assignOf sh P cfg ev (evAct sh i q) = true ∧
        assignOf sh P cfg ev (vpc sh i q c) = true := by
    unfold actGuard
    rcases bool_eq_cases (assignOf sh P cfg ev (evAct sh i q)) with hx | hx
    · rcases bool_eq_cases (assignOf sh P cfg ev (vpc sh i q c)) with hy | hy
      · simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hx, hy]
      · simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hx, hy]
    · rcases bool_eq_cases (assignOf sh P cfg ev (vpc sh i q c)) with hy | hy
      · simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hx, hy]
      · simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hx, hy]
  rw [hbase, h1, h2]

/-- **Inversion of an acting transition.**  A step in which session q acts is one of the eight
session rules of ProtSat.Rel, and each of them is driven by the action it finds at q's program
counter.  The action is left implicit in each alternative so that a consumer can match it
against its own action without naming the constructor's implicit parameters. -/
theorem Rel.act_shapes {P₁ : Protocol} {C C' : Cfg} {q : Nat} {m : Term} {d : NonceName}
    (h : Rel P₁ C (Ev.act q m d) C') :
    (∃ (x : Nat) (N : NonceName), P₁.actionAt q (pcOf C q) = some (Action.fresh x N) ∧
        C' = succStore C q x (Term.nonce d)) ∨
    (∃ (x : Nat) (a : Agent), P₁.actionAt q (pcOf C q) = some (Action.recv a x) ∧ m ∈ C.kn ∧
        C' = succStore C q x m) ∨
    (∃ (x : Nat) (e : Expr) (t : Term), P₁.actionAt q (pcOf C q) = some (Action.assign x e) ∧
        Expr.eval e (storeOf C q) = some t ∧ C' = succStore C q x t) ∨
    (∃ (a : Agent) (e : Expr) (t : Term), P₁.actionAt q (pcOf C q) = some (Action.send a e) ∧
        Expr.eval e (storeOf C q) = some t ∧ C' = succSend C q t) ∨
    (∃ (e₁ e₂ : Expr) (v : Term), P₁.actionAt q (pcOf C q) = some (Action.check e₁ e₂) ∧
        Expr.eval e₁ (storeOf C q) = some v ∧ Expr.eval e₂ (storeOf C q) = some v ∧
          C' = succAdvance C q) ∨
    (∃ (e : Expr), P₁.actionAt q (pcOf C q) = some (Action.secret e) ∧ C' = succAdvance C q) ∨
    (∃ (tag : Tag) (peer v : Expr),
        P₁.actionAt q (pcOf C q) = some (Action.claim tag peer v) ∧ C' = succAdvance C q) ∨
    (∃ (tag : Tag) (peer v : Expr),
        P₁.actionAt q (pcOf C q) = some (Action.commit tag peer v) ∧ C' = succAdvance C q) := by
  cases h with
  | rFresh hq _ _ => exact Or.inl ⟨_, _, hq, rfl⟩
  | rRecv hq hkn => exact Or.inr (Or.inl ⟨_, _, hq, hkn, rfl⟩)
  | rAssign hq heval => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, hq, heval, rfl⟩))
  | rSend hq heval => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, hq, heval, rfl⟩)))
  | rCheck hq h₁ h₂ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, hq, h₁, h₂, rfl⟩))))
  | rSecret hq => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hq, rfl⟩)))))
  | rClaim hq =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, hq, rfl⟩))))))
  | rCommit hq =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, hq, rfl⟩))))))

/-- In an acting step every slot of the acting session that the action does not write keeps its
value: this is the semantic content of the keep clauses of ProtSat.stepKeepClauses. -/
theorem Rel.act_keep {P₁ : Protocol} {C C' : Cfg} {q : Nat} {m : Term} {d : NonceName}
    {act : Action} {y : Nat} (h : Rel P₁ C (Ev.act q m d) C')
    (hamt : P₁.actionAt q (pcOf C q) = some act) (hy : writtenVar act ≠ some y) :
    readVar y (storeOf C' q) = readVar y (storeOf C q) := by
  rcases Rel.act_shapes h with ⟨x, N, hq, hC⟩ | ⟨x, a, hq, _, hC⟩ | ⟨x, e, t, hq, _, hC⟩
    | ⟨a, e, t, hq, _, hC⟩ | ⟨e₁, e₂, v, hq, _, _, hC⟩ | ⟨e, hq, hC⟩ | ⟨tag, peer, v, hq, hC⟩
    | ⟨tag, peer, v, hq, hC⟩
  · have hmatch : Action.fresh x N = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    have hxy : x ≠ y := fun hxy => hy (by subst hxy; rfl)
    rw [hC]
    exact readVar_succStore_other C q x y (Term.nonce d) hxy
  · have hmatch : Action.recv a x = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    have hxy : x ≠ y := fun hxy => hy (by subst hxy; rfl)
    rw [hC]
    exact readVar_succStore_other C q x y m hxy
  · have hmatch : Action.assign x e = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    have hxy : x ≠ y := fun hxy => hy (by subst hxy; rfl)
    rw [hC]
    exact readVar_succStore_other C q x y t hxy
  · have hmatch : Action.send a e = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    rw [hC]
    exact congrArg (readVar y) (storeOf_succAdvance C q q)
  · have hmatch : Action.check e₁ e₂ = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    rw [hC]
    exact congrArg (readVar y) (storeOf_succAdvance C q q)
  · rw [hC]
    exact congrArg (readVar y) (storeOf_succAdvance C q q)
  · rw [hC]
    exact congrArg (readVar y) (storeOf_succAdvance C q q)
  · rw [hC]
    exact congrArg (readVar y) (storeOf_succAdvance C q q)

/-- **What an acting step does**, as a function of the action it performs: the written slot and
its new value, the message the attacker learns from a send, and the equality a test requires.
Declared as a function of the action so that a proof can case on the action shape. -/
def ActData (P₁ : Protocol) (C C' : Cfg) (q : Nat) (m : Term) (d : NonceName) (act : Action) : Prop :=
  match act with
  | Action.fresh x N => readVar x (storeOf C' q) = some (Term.nonce d)
  | Action.recv a x => readVar x (storeOf C' q) = some m ∧ m ∈ C.kn
  | Action.assign x e =>
      ∃ t, Expr.eval e (storeOf C q) = some t ∧ readVar x (storeOf C' q) = some t
  | Action.send a e => ∃ t, Expr.eval e (storeOf C q) = some t ∧ C'.kn = C.kn ++ [t]
  | Action.check e₁ e₂ =>
      ∃ v, Expr.eval e₁ (storeOf C q) = some v ∧ Expr.eval e₂ (storeOf C q) = some v
  | _ => True

/-- The action of an acting step determines the successor configuration exactly as the step
clauses require. -/
theorem Rel.act_data {P₁ : Protocol} {C C' : Cfg} {q : Nat} {m : Term} {d : NonceName}
    {act : Action} (h : Rel P₁ C (Ev.act q m d) C') (hS : q < C.sess.length)
    (hamt : P₁.actionAt q (pcOf C q) = some act) : ActData P₁ C C' q m d act := by
  obtain ⟨st, hst⟩ := sessAt_lt hS
  rcases Rel.act_shapes h with ⟨x, N, hq, hC⟩ | ⟨x, a, hq, hkn, hC⟩ | ⟨x, e, t, hq, heval, hC⟩
    | ⟨a, e, t, hq, heval, hC⟩ | ⟨e₁, e₂, v, hq, h₁, h₂, hC⟩ | ⟨e, hq, hC⟩
    | ⟨tag, peer, v, hq, hC⟩ | ⟨tag, peer, v, hq, hC⟩
  · have hmatch : Action.fresh x N = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    rw [hC]
    simp only [ActData]
    exact readVar_succStore C q x (Term.nonce d) st hst
  · have hmatch : Action.recv a x = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    rw [hC]
    simp only [ActData]
    exact ⟨readVar_succStore C q x m st hst, hkn⟩
  · have hmatch : Action.assign x e = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    rw [hC]
    simp only [ActData]
    exact ⟨t, heval, readVar_succStore C q x t st hst⟩
  · have hmatch : Action.send a e = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    simp only [ActData]
    exact ⟨t, heval, by rw [hC]; rfl⟩
  · have hmatch : Action.check e₁ e₂ = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    simp only [ActData]
    exact ⟨v, h₁, h₂⟩
  · have hmatch : Action.secret e = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    simp only [ActData]
  · have hmatch : Action.claim tag peer v = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    simp only [ActData]
  · have hmatch : Action.commit tag peer v = act := Option.some.inj (hq.symm.trans hamt)
    subst hmatch
    simp only [ActData]

/-- The guard of a step clause: if the session does not act, or not at this counter, the clause
is satisfied whatever its tail is. -/
theorem step_guard (tail : List Lit)
    (h : assignOf sh P cfg ev (evAct sh i q) = false ∨
         assignOf sh P cfg ev (vpc sh i q c) = false) :
    Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c ++ tail) = true := by
  rcases h with h | h
  · exact clause_eval_holds (neg (evAct sh i q)) (List.mem_append_left _ (List.Mem.head _))
      (by simp [neg_eval, h])
  · exact clause_eval_holds (neg (vpc sh i q c))
      (List.mem_append_left _ (List.Mem.tail _ (List.Mem.head _))) (by simp [neg_eval, h])

/-- The acting case of a step clause: when both guard literals are true the run really has
session q acting at step i with program counter c. -/
theorem step_act (hok : RunOK sh P cfg ev) (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1)))
    (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh)
    (hact : assignOf sh P cfg ev (evAct sh i q) = true)
    (hpc : assignOf sh P cfg ev (vpc sh i q c) = true) :
    (∃ m d, ev i = Ev.act q m d) ∧ rdPc sh P cfg ev i q = c := by
  have h1 : ∃ m d, ev i = Ev.act q m d := by
    rw [assignOf_evAct sh P cfg ev hi hq] at hact
    exact (evActs sh P cfg ev hq).mpr (of_decide_eq_true hact)
  have h2 : rdPc sh P cfg ev i q = c := by
    rw [assignOf_pc sh P cfg ev (Nat.le_of_lt hi) hq hc] at hpc
    exact of_decide_eq_true hpc
  exact ⟨h1, h2⟩

/-- A satisfied tail satisfies the whole clause. -/
theorem clause_eval_append_right_true (a : Assignment) (g t : List Lit)
    (h : Clause.eval a t = true) : Clause.eval a (g ++ t) = true := by
  rw [clause_eval_any] at *
  obtain ⟨l, hl, he⟩ := h
  exact ⟨l, List.mem_append_right g hl, he⟩

/-- An acting transition has an action at the acting session's program counter. -/
theorem Rel.act_ne_none {P₁ : Protocol} {C C' : Cfg} {q : Nat} {m : Term} {d : NonceName}
    (h : Rel P₁ C (Ev.act q m d) C') : P₁.actionAt q (pcOf C q) ≠ none := by
  rcases Rel.act_shapes h with ⟨x, N, hq, _⟩ | ⟨x, a, hq, _, _⟩ | ⟨x, e, t, hq, _, _⟩
    | ⟨a, e, t, hq, _, _⟩ | ⟨e₁, e₂, v, hq, _, _, _⟩ | ⟨e, hq, _⟩ | ⟨tag, peer, v, hq, _⟩
    | ⟨tag, peer, v, hq, _⟩
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)
  · exact fun he => absurd (hq.symm.trans he) (by simp)

/-- **Every step clause carries the act guard of its position as a prefix.** -/
theorem actGuard_prefix_stepClausesAt (cl : Clause) (hcl : cl ∈ stepClausesAt sh P i q c) :
    ∃ tail, cl = actGuard sh i q c ++ tail := by
  cases h : P.actionAt q c with
  | some act =>
    rw [stepClausesAt_some sh P i q c act h] at hcl
    rw [List.mem_append] at hcl
    rcases hcl with h1 | hact2
    · rw [List.mem_append] at h1
      rcases h1 with hadv | hkeep
      · rw [List.mem_singleton] at hadv
        subst hadv
        exact ⟨[pos (vpc sh (i + 1) q (c + 1))], rfl⟩
      · rw [stepKeepClauses, List.mem_flatMap] at hkeep
        obtain ⟨y, hy, h5⟩ := hkeep
        by_cases hwy : writtenVar act = some y
        · rw [if_pos hwy] at h5
          exact absurd h5 (by simp)
        · rw [if_neg hwy, keepVarClauses, mapVal, List.mem_map] at h5
          obtain ⟨u, hu, heq⟩ := h5
          subst heq
          exact ⟨[neg (vst sh i q y u), pos (vst sh (i + 1) q y u)], rfl⟩
    · cases act with
        | fresh x N =>
            rw [actionClauses] at hact2
            rw [List.mem_append] at hact2
            rcases hact2 with hfresh | hdummy
            · rw [List.mem_flatMap] at hfresh
              obtain ⟨dn, hd, h5⟩ := hfresh
              rw [freshStepClauses] at h5
              cases h5' : rget sh.D dn with
              | none =>
                  rw [h5'] at h5
                  simp only [List.mem_singleton] at h5
                  subst h5
                  exact ⟨[neg (vfr sh i q dn)], rfl⟩
              | some N' =>
                  rw [h5'] at h5
                  simp only [List.mem_singleton] at h5
                  subst h5
                  exact ⟨[neg (vfr sh i q dn),
                    pos (vst sh (i + 1) q x (uIdx sh (some (Term.nonce N'))))], rfl⟩
            · simp only [List.mem_singleton] at hdummy
              subst hdummy
              exact ⟨[neg (vfr sh i q (shD sh - 1))], rfl⟩
        | send a e =>
            rw [actionClauses] at hact2
            rw [List.mem_append] at hact2
            rcases hact2 with hreal | hpub
            · simp only [List.mem_singleton] at hreal
              subst hreal
              exact ⟨[neg (vxe sh i q (eIdx P e) (sh.U.length))], rfl⟩
            · rw [mapMsg, List.mem_map] at hpub
              obtain ⟨u, hu, heq⟩ := hpub
              subst heq
              exact ⟨[neg (vxe sh i q (eIdx P e) u), pos (vkn sh (i + 1) u)], rfl⟩
        | recv a x =>
            rw [actionClauses] at hact2
            rw [eachVal, List.mem_flatMap] at hact2
            obtain ⟨u, hu, h5⟩ := hact2
            by_cases hut : u < sh.U.length
            · rw [if_pos hut] at h5
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at h5
              rcases h5 with hst | hkn
              · subst hst
                exact ⟨[neg (vdl sh i q u), pos (vst sh (i + 1) q x u)], rfl⟩
              · subst hkn
                exact ⟨[neg (vdl sh i q u), pos (vkn sh i u)], rfl⟩
            · rw [if_neg hut, List.mem_singleton] at h5
              subst h5
              exact ⟨[neg (vdl sh i q u)], rfl⟩
        | assign x e =>
            rw [actionClauses] at hact2
            rw [eachVal, List.mem_flatMap] at hact2
            obtain ⟨u, hu, h5⟩ := hact2
            by_cases hut : u < sh.U.length
            · rw [if_pos hut, List.mem_singleton] at h5
              subst h5
              exact ⟨[neg (vxe sh i q (eIdx P e) u), pos (vst sh (i + 1) q x u)], rfl⟩
            · rw [if_neg hut, List.mem_singleton] at h5
              subst h5
              exact ⟨[neg (vxe sh i q (eIdx P e) u)], rfl⟩
        | check e₁ e₂ =>
            rw [actionClauses] at hact2
            rw [List.mem_append] at hact2
            rcases hact2 with hreal | hrest
            · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hreal
              rcases hreal with h1 | h2
              · subst h1
                exact ⟨[neg (vxe sh i q (eIdx P e₁) (sh.U.length))], rfl⟩
              · subst h2
                exact ⟨[neg (vxe sh i q (eIdx P e₂) (sh.U.length))], rfl⟩
            · rw [eachVal, List.mem_flatMap] at hrest
              obtain ⟨u, hu, h5⟩ := hrest
              obtain ⟨v, hv, hif⟩ := List.mem_filterMap.mp h5
              by_cases hut : u == v
              · rw [if_pos hut] at hif
                exact absurd hif (by simp)
              · rw [if_neg hut] at hif
                have heq : checkEqClause sh i q c (eIdx P e₁) (eIdx P e₂) u v = cl :=
                  Option.some.inj hif
                subst heq
                exact ⟨[neg (vxe sh i q (eIdx P e₁) u), neg (vxe sh i q (eIdx P e₂) v)], rfl⟩
        | secret _ | claim _ _ _ | commit _ _ _ =>
            simp only [actionClauses] at hact2
            exact absurd hact2 (by simp)
  | none =>
    rw [stepClausesAt, h] at hcl
    simp only [List.mem_singleton] at hcl
    subst hcl
    exact ⟨[], by rw [List.append_nil]⟩

/-- Reading past the end of a list gives none only out of range. -/
theorem rget_none_length {α : Type} : ∀ (l : List α) (i : Nat), rget l i = none -> l.length ≤ i := by
  intro l
  induction l with
  | nil => intro i _; exact Nat.zero_le _
  | cons x xs ih =>
      intro i h
      cases i with
      | zero => exact absurd h (by simp [rget])
      | succ i =>
          have h2 : rget xs i = none := by simpa [rget] using h
          have hlen := ih i h2
          have hl : (x :: xs).length = xs.length + 1 := rfl
          omega

/-- The index of a universe message is a genuine position in the universe. -/
theorem uIdx_some_lt (sh : Shape) {t : Term} (ht : t ∈ sh.U) : uIdx sh (some t) < sh.U.length := by
  show (if t ∈ sh.U then ixOf t sh.U else sh.U.length) < sh.U.length
  rw [if_pos ht]
  exact ixOf_lt sh.U t ht

/-- The unset index is a legal value index. -/
theorem len_lt_shVal (sh : Shape) : sh.U.length < shVal sh := Nat.lt_succ_self _

/-- A negated literal is true when the assignment sets its variable to false. -/
theorem neg_lit (a : Assignment) (v : BVar) (h : a v = false) : Lit.eval a (neg v) = true := by
  simp [neg_eval, h]

/-- **Clause group 5 (step conditions), acting case.** -/
theorem stepClausesAt_act_sat (hok : RunOK sh P cfg ev)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1)))
    (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh)
    (hg : Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c) = false)
    (cl : Clause) (hcl : cl ∈ stepClausesAt sh P i q c) :
    Clause.eval (assignOf sh P cfg ev) cl = true := by
  obtain ⟨⟨m, d, hevm⟩, hpcd⟩ := (actGuard_false sh P cfg ev hok hi hq hc).mp hg
  have hS : q < (cfg i).sess.length := by
    rw [runOK_sessLen sh P cfg ev hok i]
    exact (runOK_act sh P cfg ev hok i q m d hevm).1
  have hrel' : Rel P (cfg i) (Ev.act q m d) (cfg (i + 1)) := by rw [← hevm]; exact hrel i
  have hpcq : pcOf (cfg i) q = c := hpcd
  have hrdFr : rdFr sh P cfg ev i q = ixOf d sh.D := by simp [rdFr, hevm]
  have hrdDl : rdDl sh P cfg ev i q = uIdx sh (some m) := by simp [rdDl, hevm]
  cases h : P.actionAt q c with
  | none =>
      have hne : P.actionAt q (pcOf (cfg i) q) ≠ none := Rel.act_ne_none hrel'
      have he : P.actionAt q (pcOf (cfg i) q) = none := by rw [hpcq]; exact h
      exact absurd he hne
  | some act =>
      have hamt : P.actionAt q (pcOf (cfg i) q) = some act := by rw [hpcq]; exact h
      have hdata := Rel.act_data hrel' hS hamt
      rw [stepClausesAt_some sh P i q c act h] at hcl
      rw [List.mem_append] at hcl
      rcases hcl with h1 | hact2
      · rw [List.mem_append] at h1
        rcases h1 with hadv | hkeep
        · -- the advance clause
          rw [List.mem_singleton] at hadv
          subst hadv
          have hc1 : c + 1 < shPc sh :=
            runOK_pcAct sh P cfg ev hok q c
              (fun he => absurd (h.symm.trans he) (Option.some_ne_none act))
          have hpc1 : pcOf (cfg (i + 1)) q = c + 1 := by
            rw [Rel.act_pcOf hrel' hS, hpcq]
          rw [advClause]
          refine clause_eval_append_right_true _ _ _ (clause1 _ _ (by
            rw [pos_eval, assignOf_pc sh P cfg ev (Nat.succ_le_of_lt hi) hq hc1]
            exact decide_eq_true hpc1))
        · -- the keep clauses
          rw [stepKeepClauses, List.mem_flatMap] at hkeep
          obtain ⟨y, hy, h5⟩ := hkeep
          have hyV : y < shV sh := List.mem_range.mp hy
          by_cases hwy : writtenVar act = some y
          · rw [if_pos hwy] at h5
            exact absurd h5 (by simp)
          · rw [if_neg hwy, keepVarClauses, mapVal, List.mem_map] at h5
            obtain ⟨u, hu, heq⟩ := h5
            have huV : u < shVal sh := List.mem_range.mp hu
            subst heq
            rw [keepClause]
            refine clause_eval_append_right_true _ _ _ ?_
            rcases bool_eq_cases (assignOf sh P cfg ev (vst sh i q y u)) with hst | hst
            · have hrd : rdSt sh P cfg ev i q y = u := by
                rw [assignOf_st sh P cfg ev (Nat.le_of_lt hi) hq hyV huV] at hst
                exact of_decide_eq_true hst
              have hkeep' : readVar y (storeOf (cfg (i + 1)) q) = readVar y (storeOf (cfg i) q) :=
                Rel.act_keep hrel' hamt hwy
              have hrd' : rdSt sh P cfg ev (i + 1) q y = u := by
                show uIdx sh (readVar y (storeOf (cfg (i + 1)) q)) = u
                rw [hkeep']
                exact hrd
              exact clause2_right _ _ _ (by
                rw [pos_eval, assignOf_st sh P cfg ev (Nat.succ_le_of_lt hi) hq hyV huV]
                exact decide_eq_true hrd')
            · exact clause2_left _ _ _ (by simp [neg_eval, hst])
      · cases act with
        | fresh x N =>
            have hxV : x < shV sh :=
              runOK_written sh P cfg ev hok q c (Action.fresh x N) h x (by simp [Action.written])
            have hwr : readVar x (storeOf (cfg (i + 1)) q) = some (Term.nonce d) := hdata
            rw [actionClauses, List.mem_append] at hact2
            rcases hact2 with hfresh | hdummy
            · rw [List.mem_flatMap] at hfresh
              obtain ⟨dn, hd, h5⟩ := hfresh
              have hd' : dn < shD sh := List.mem_range.mp hd
              rw [freshStepClauses] at h5
              cases h5' : rget sh.D dn with
              | none =>
                  rw [h5'] at h5
                  simp only [List.mem_singleton] at h5
                  subst h5
                  have hlen : sh.D.length ≤ dn := rget_none_length sh.D dn h5'
                  have hlt : rdFr sh P cfg ev i q < sh.D.length := by
                    rw [hrdFr]
                    exact ixOf_lt sh.D d (runOK_act_dD sh P cfg ev hok hevm ⟨x, N, by rw [hpcq]; exact h⟩)
                  have hne : rdFr sh P cfg ev i q ≠ dn := by
                    intro he
                    omega
                  have hv : assignOf sh P cfg ev (vfr sh i q dn) = false := by
                    rw [assignOf_fr sh P cfg ev hi hq hd']
                    exact decide_eq_false hne
                  refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
              | some N' =>
                  rw [h5'] at h5
                  simp only [List.mem_singleton] at h5
                  subst h5
                  refine clause_eval_append_right_true _ _ _ ?_
                  rcases bool_eq_cases (assignOf sh P cfg ev (vfr sh i q dn)) with hf | hf
                  · have hdn : d = N' := by
                      have h1 : rdFr sh P cfg ev i q = dn := by
                        rw [assignOf_fr sh P cfg ev hi hq hd'] at hf
                        exact of_decide_eq_true hf
                      have h2 : rget sh.D (ixOf d sh.D) = some N' := by
                        rw [← h1] at h5'
                        rw [hrdFr] at h5'
                        exact h5'
                      rw [rget_ixOf sh.D d (runOK_act_dD sh P cfg ev hok hevm ⟨x, N, by rw [hpcq]; exact h⟩)] at h2
                      exact Option.some.inj h2
                    have hrd' : rdSt sh P cfg ev (i + 1) q x = uIdx sh (some (Term.nonce N')) := by
                      show uIdx sh (readVar x (storeOf (cfg (i + 1)) q)) = _
                      rw [hwr, hdn]
                    exact clause2_right _ _ _ (by
                      rw [pos_eval,
                        assignOf_st sh P cfg ev (Nat.succ_le_of_lt hi) hq hxV (uIdx_lt' sh _)]
                      exact decide_eq_true hrd')
                  · exact clause2_left _ _ _ (by simp [neg_eval, hf])
            · simp only [List.mem_singleton] at hdummy
              subst hdummy
              have hlt : rdFr sh P cfg ev i q < sh.D.length := by
                rw [hrdFr]
                exact ixOf_lt sh.D d (runOK_act_dD sh P cfg ev hok hevm ⟨x, N, by rw [hpcq]; exact h⟩)
              have hne : rdFr sh P cfg ev i q ≠ shD sh - 1 := by
                intro he
                have h2 : shD sh = sh.D.length + 1 := rfl
                rw [h2] at he
                omega
              have hv : assignOf sh P cfg ev (vfr sh i q (shD sh - 1)) = false := by
                rw [assignOf_fr sh P cfg ev hi hq (Nat.sub_lt (shD_pos sh) (by omega))]
                exact decide_eq_false hne
              refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
        | send a e =>
            have hmemE : e ∈ allExprs P := mem_allExprs_send h
            have heE : eIdx P e < shE sh := runOK_eIdx sh P cfg ev hok e hmemE
            have hdata' : ∃ t, Expr.eval e (storeOf (cfg i) q) = some t ∧
                (cfg (i + 1)).kn = (cfg i).kn ++ [t] := hdata
            obtain ⟨t, heval, hkn⟩ := hdata'
            have htU : t ∈ sh.U := by
              have ad := runOK_expr sh P cfg ev hok i q e hmemE
              rw [heval] at ad
              simpa [admissible] using ad
            have hrd : rdXe sh P cfg ev i q (eIdx P e) = uIdx sh (some t) := by
              rw [rdXe_eIdx sh P cfg ev hmemE, heval]
            rw [actionClauses, List.mem_append] at hact2
            rcases hact2 with hreal | hpub
            · simp only [List.mem_singleton] at hreal
              subst hreal
              have hlt : rdXe sh P cfg ev i q (eIdx P e) < sh.U.length := by
                rw [hrd]
                exact uIdx_some_lt sh htU
              have hne : rdXe sh P cfg ev i q (eIdx P e) ≠ sh.U.length := by
                intro he
                omega
              have hv : assignOf sh P cfg ev (vxe sh i q (eIdx P e) sh.U.length) = false := by
                rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq heE (len_lt_shVal sh)]
                exact decide_eq_false hne
              refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
            · rw [mapMsg, List.mem_map] at hpub
              obtain ⟨u, hu, heq⟩ := hpub
              have huV : u < shVal sh := Nat.lt_succ_of_lt (List.mem_range.mp hu)
              subst heq
              rw [sendPublishClause]
              refine clause_eval_append_right_true _ _ _ ?_
              rcases bool_eq_cases (assignOf sh P cfg ev (vxe sh i q (eIdx P e) u)) with hxe | hxe
              · have hu' : uIdx sh (some t) = u := by
                  have h3 : rdXe sh P cfg ev i q (eIdx P e) = u := by
                    rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq heE huV] at hxe
                    exact of_decide_eq_true hxe
                  rw [hrd] at h3
                  exact h3
                have hval : valAt sh u = some t := by
                  rw [← hu']
                  exact valAt_uIdx_some sh htU
                refine clause2_right _ _ _ (by
                  rw [pos_eval, assignOf_kn sh P cfg ev (Nat.succ_le_of_lt hi) huV]
                  rw [knHolds, hval, hkn]
                  exact decide_eq_true (by simp))
              · exact clause2_left _ _ _ (by simp [neg_eval, hxe])
        | recv a x =>
            have hxV : x < shV sh :=
              runOK_written sh P cfg ev hok q c (Action.recv a x) h x (by simp [Action.written])
            have hdata' : readVar x (storeOf (cfg (i + 1)) q) = some m ∧ m ∈ (cfg i).kn := hdata
            obtain ⟨hwr, hmem⟩ := hdata'
            rw [actionClauses, eachVal, List.mem_flatMap] at hact2
            obtain ⟨u, hu, h5⟩ := hact2
            have huV : u < shVal sh := List.mem_range.mp hu
            have hdl (hd : assignOf sh P cfg ev (vdl sh i q u) = true) : uIdx sh (some m) = u := by
              have h3 : rdDl sh P cfg ev i q = u := by
                rw [assignOf_dl sh P cfg ev hi hq huV] at hd
                exact of_decide_eq_true hd
              rw [hrdDl] at h3
              exact h3
            by_cases hut : u < sh.U.length
            · rw [if_pos hut] at h5
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at h5
              rcases h5 with hst | hkn
              · subst hst
                rw [recvStoreClause]
                refine clause_eval_append_right_true _ _ _ ?_
                rcases bool_eq_cases (assignOf sh P cfg ev (vdl sh i q u)) with hd | hd
                · have hrd' : rdSt sh P cfg ev (i + 1) q x = u := by
                    show uIdx sh (readVar x (storeOf (cfg (i + 1)) q)) = u
                    rw [hwr, hdl hd]
                  exact clause2_right _ _ _ (by
                    rw [pos_eval, assignOf_st sh P cfg ev (Nat.succ_le_of_lt hi) hq hxV huV]
                    exact decide_eq_true hrd')
                · exact clause2_left _ _ _ (by simp [neg_eval, hd])
              · subst hkn
                rw [recvKnowClause]
                refine clause_eval_append_right_true _ _ _ ?_
                rcases bool_eq_cases (assignOf sh P cfg ev (vdl sh i q u)) with hd | hd
                · have hval : valAt sh u = some m := by
                    rw [← hdl hd]
                    exact valAt_uIdx_some sh (runOK_act_mU sh P cfg ev hok hevm ⟨a, x, by rw [hpcq]; exact h⟩)
                  refine clause2_right _ _ _ (by
                    rw [pos_eval, assignOf_kn sh P cfg ev (Nat.le_of_lt hi) huV]
                    rw [knHolds, hval]
                    exact decide_eq_true hmem)
                · exact clause2_left _ _ _ (by simp [neg_eval, hd])
            · rw [if_neg hut, List.mem_singleton] at h5
              subst h5
              rw [recvRealClause]
              have hlt : rdDl sh P cfg ev i q < sh.U.length := by
                rw [hrdDl]
                exact uIdx_some_lt sh (runOK_act_mU sh P cfg ev hok hevm ⟨a, x, by rw [hpcq]; exact h⟩)
              have hne : rdDl sh P cfg ev i q ≠ sh.U.length := by
                intro he
                omega
              have hsl : shVal sh = sh.U.length + 1 := rfl
              rw [hsl] at huV
              have hu_eq : u = sh.U.length := by omega
              subst hu_eq
              have hv : assignOf sh P cfg ev (vdl sh i q sh.U.length) = false := by
                rw [assignOf_dl sh P cfg ev hi hq (len_lt_shVal sh)]
                exact decide_eq_false hne
              refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
        | assign x e =>
            have hxV : x < shV sh :=
              runOK_written sh P cfg ev hok q c (Action.assign x e) h x (by simp [Action.written])
            have hmemE : e ∈ allExprs P := mem_allExprs_assign h
            have heE : eIdx P e < shE sh := runOK_eIdx sh P cfg ev hok e hmemE
            have hdata' : ∃ t, Expr.eval e (storeOf (cfg i) q) = some t ∧
                readVar x (storeOf (cfg (i + 1)) q) = some t := hdata
            obtain ⟨t, heval, hwr⟩ := hdata'
            have htU : t ∈ sh.U := by
              have ad := runOK_expr sh P cfg ev hok i q e hmemE
              rw [heval] at ad
              simpa [admissible] using ad
            have hrd : rdXe sh P cfg ev i q (eIdx P e) = uIdx sh (some t) := by
              rw [rdXe_eIdx sh P cfg ev hmemE, heval]
            rw [actionClauses, eachVal, List.mem_flatMap] at hact2
            obtain ⟨u, hu, h5⟩ := hact2
            have huV : u < shVal sh := List.mem_range.mp hu
            by_cases hut : u < sh.U.length
            · rw [if_pos hut, List.mem_singleton] at h5
              subst h5
              rw [assignClause]
              refine clause_eval_append_right_true _ _ _ ?_
              rcases bool_eq_cases (assignOf sh P cfg ev (vxe sh i q (eIdx P e) u)) with hxe | hxe
              · have hu' : uIdx sh (some t) = u := by
                  have h3 : rdXe sh P cfg ev i q (eIdx P e) = u := by
                    rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq heE huV] at hxe
                    exact of_decide_eq_true hxe
                  rw [hrd] at h3
                  exact h3
                have hrd' : rdSt sh P cfg ev (i + 1) q x = u := by
                  show uIdx sh (readVar x (storeOf (cfg (i + 1)) q)) = u
                  rw [hwr, hu']
                exact clause2_right _ _ _ (by
                  rw [pos_eval, assignOf_st sh P cfg ev (Nat.succ_le_of_lt hi) hq hxV huV]
                  exact decide_eq_true hrd')
              · exact clause2_left _ _ _ (by simp [neg_eval, hxe])
            · rw [if_neg hut, List.mem_singleton] at h5
              subst h5
              have hsl : shVal sh = sh.U.length + 1 := rfl
              rw [hsl] at huV
              have hu_eq : u = sh.U.length := by omega
              subst hu_eq
              rw [assignRealClause]
              have hlt : rdXe sh P cfg ev i q (eIdx P e) < sh.U.length := by
                rw [hrd]
                exact uIdx_some_lt sh htU
              have hne : rdXe sh P cfg ev i q (eIdx P e) ≠ sh.U.length := by
                intro he
                omega
              have hv : assignOf sh P cfg ev (vxe sh i q (eIdx P e) sh.U.length) = false := by
                rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq heE (len_lt_shVal sh)]
                exact decide_eq_false hne
              refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
        | check e₁ e₂ =>
            obtain ⟨hm₁, hm₂⟩ := mem_allExprs_check h
            have he₁ : eIdx P e₁ < shE sh := runOK_eIdx sh P cfg ev hok e₁ hm₁
            have he₂ : eIdx P e₂ < shE sh := runOK_eIdx sh P cfg ev hok e₂ hm₂
            have hdata' : ∃ v, Expr.eval e₁ (storeOf (cfg i) q) = some v ∧
                Expr.eval e₂ (storeOf (cfg i) q) = some v := hdata
            obtain ⟨v, hv₁, hv₂⟩ := hdata'
            have hvU : v ∈ sh.U := by
              have ad := runOK_expr sh P cfg ev hok i q e₁ hm₁
              rw [hv₁] at ad
              simpa [admissible] using ad
            have hrd₁ : rdXe sh P cfg ev i q (eIdx P e₁) = uIdx sh (some v) := by
              rw [rdXe_eIdx sh P cfg ev hm₁, hv₁]
            have hrd₂ : rdXe sh P cfg ev i q (eIdx P e₂) = uIdx sh (some v) := by
              rw [rdXe_eIdx sh P cfg ev hm₂, hv₂]
            rw [actionClauses, List.mem_append] at hact2
            rcases hact2 with hreal | hrest
            · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hreal
              rcases hreal with h1 | h2
              · subst h1
                rw [checkRealClause]
                have hlt : rdXe sh P cfg ev i q (eIdx P e₁) < sh.U.length := by
                  rw [hrd₁]
                  exact uIdx_some_lt sh hvU
                have hne : rdXe sh P cfg ev i q (eIdx P e₁) ≠ sh.U.length := by
                  intro he
                  omega
                have hv : assignOf sh P cfg ev (vxe sh i q (eIdx P e₁) sh.U.length) = false := by
                  rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq he₁ (len_lt_shVal sh)]
                  exact decide_eq_false hne
                refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
              · subst h2
                rw [checkRealClause]
                have hlt : rdXe sh P cfg ev i q (eIdx P e₂) < sh.U.length := by
                  rw [hrd₂]
                  exact uIdx_some_lt sh hvU
                have hne : rdXe sh P cfg ev i q (eIdx P e₂) ≠ sh.U.length := by
                  intro he
                  omega
                have hv : assignOf sh P cfg ev (vxe sh i q (eIdx P e₂) sh.U.length) = false := by
                  rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq he₂ (len_lt_shVal sh)]
                  exact decide_eq_false hne
                refine clause_eval_append_right_true _ _ _ (clause1 _ _ (neg_lit _ _ hv))
            · rw [eachVal, List.mem_flatMap] at hrest
              obtain ⟨u, hu, h5⟩ := hrest
              have huV : u < shVal sh := List.mem_range.mp hu
              obtain ⟨w, hw, hif⟩ := List.mem_filterMap.mp h5
              by_cases hut : u == w
              · rw [if_pos hut] at hif
                exact absurd hif (by simp)
              · rw [if_neg hut] at hif
                have heq : checkEqClause sh i q c (eIdx P e₁) (eIdx P e₂) u w = cl :=
                  Option.some.inj hif
                subst heq
                rw [checkEqClause]
                refine clause_eval_append_right_true _ _ _ ?_
                rcases bool_eq_cases (assignOf sh P cfg ev (vxe sh i q (eIdx P e₁) u)) with h1 | h1
                · rcases bool_eq_cases (assignOf sh P cfg ev (vxe sh i q (eIdx P e₂) w)) with h2 | h2
                  · have hwV : w < shVal sh := List.mem_range.mp hw
                    have hu₁ : uIdx sh (some v) = u := by
                      have h3 : rdXe sh P cfg ev i q (eIdx P e₁) = u := by
                        rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq he₁ huV] at h1
                        exact of_decide_eq_true h1
                      rw [hrd₁] at h3
                      exact h3
                    have hw₁ : uIdx sh (some v) = w := by
                      have h3 : rdXe sh P cfg ev i q (eIdx P e₂) = w := by
                        rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq he₂ hwV] at h2
                        exact of_decide_eq_true h2
                      rw [hrd₂] at h3
                      exact h3
                    have hthis : u = w := hu₁.symm.trans hw₁
                    have hbeq : u == w := by simpa using hthis
                    exact absurd hbeq hut
                  · exact clause2_right _ _ _ (by simp [neg_eval, h2])
                · exact clause2_left _ _ _ (by simp [neg_eval, h1])
        | secret _ | claim _ _ _ | commit _ _ _ =>
            simp only [actionClauses] at hact2
            exact absurd hact2 (by simp)

/-- **Clause group 5 (step conditions).**  Every step clause is satisfied: either the guard
literal is true - the session does not act, or not at that program counter - or the session
really acts there, and then the successor configuration is the one ProtSat.Rel prescribes for
the action at that position, which is what ProtSat.stepClausesAt sh P i q c demands. -/
theorem sat_step (hok : RunOK sh P cfg ev)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (stepClauses sh P) := by
  intro cl hcl
  simp only [stepClauses, cnfOf, eachStep, eachSess, eachPc, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, h2⟩ := hcl
  obtain ⟨q, hq, h3⟩ := h2
  obtain ⟨c, hc, h4⟩ := h3
  have hi' : i < sh.steps := by simpa using hi
  have hq' : q < shS sh := by simpa using hq
  have hc' : c < shPc sh := by simpa using hc
  rcases bool_eq_cases (Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c)) with hg | hg
  · obtain ⟨tail, htail⟩ := actGuard_prefix_stepClausesAt sh P cl h4
    rw [htail]
    exact clause_eval_append_left_true _ _ _ hg
  · exact stepClausesAt_act_sat sh P cfg ev hok hrel hi' hq' hc' hg cl h4

/-- The deduction step's successor knowledge. -/
theorem Rel.ded_kn {P₁ : Protocol} {C C' : Cfg} {t : Term} (h : Rel P₁ C (Ev.ded t) C') :
    C'.kn = C.kn ++ [t] := by
  cases h with
  | rDed => rfl

/-- If the event alternative of a deduction instance is selected, the event is a deduction step
and the instance is the one the completeness of the instance enumeration found for it. -/
theorem dedEv_of_evDed (hok : RunOK sh P cfg ev) (hi : i < sh.steps) (hn : n < nInst sh)
    (hd : assignOf sh P cfg ev (evDed sh i n) = true) :
    ∃ t, ev i = Ev.ded t ∧ dedIx sh ((cfg i).kn) (uIdx sh (some t)) = n := by
  have hsev : shEv sh = 1 + shS sh + nInst sh := rfl
  have hk : 1 + shS sh + n < shEv sh := by rw [hsev]; omega
  have h2 : rdEv sh P cfg ev i = 1 + shS sh + n := by
    rw [evDed] at hd
    rw [assignOf_ev sh P cfg ev hi hk] at hd
    exact of_decide_eq_true hd
  cases h : ev i with
  | idle =>
      have h3 : rdEv sh P cfg ev i = 0 := by unfold rdEv; rw [h]
      omega
  | act q m d =>
      have h3 : rdEv sh P cfg ev i = 1 + q := by unfold rdEv; rw [h]
      have hqa : q < sh.nS1 := (runOK_act sh P cfg ev hok i q m d h).1
      have hq : q < shS sh := by rw [shS]; omega
      omega
  | ded t =>
      have h3 : rdEv sh P cfg ev i = 1 + shS sh + dedIx sh ((cfg i).kn) (uIdx sh (some t)) := by
        unfold rdEv
        rw [h]
      have h4 : dedIx sh ((cfg i).kn) (uIdx sh (some t)) = n := by omega
      exact ⟨t, rfl, h4⟩

/-- The publisher conjunction is true exactly when its three parts are. -/
theorem assignOf_vpb_iff (hok : RunOK sh P cfg ev) (hi : i < sh.steps) (hq : q < shS sh)
    (hc : c < shPc sh) (hu : u < shVal sh) {a : Agent} {e : Expr}
    (hact : P.actionAt q c = some (Action.send a e)) :
    (assignOf sh P cfg ev (vpb sh i q c u) = true) <->
      (assignOf sh P cfg ev (evAct sh i q) = true ∧
       assignOf sh P cfg ev (vpc sh i q c) = true ∧
       assignOf sh P cfg ev (vxe sh i q (eIdx P e) u) = true) := by
  have heE : eIdx P e < shE sh := runOK_eIdx sh P cfg ev hok e (mem_allExprs_send hact)
  have h1iff : (assignOf sh P cfg ev (evAct sh i q) = true) <-> ∃ m d, ev i = Ev.act q m d := by
    rw [assignOf_evAct sh P cfg ev hi hq]
    refine ⟨fun h => (evActs sh P cfg ev hq).mpr (of_decide_eq_true h),
      fun h => decide_eq_true ((evActs sh P cfg ev hq).mp h)⟩
  have h2iff : (assignOf sh P cfg ev (vpc sh i q c) = true) <->
      rdPc sh P cfg ev i q = c := by
    rw [assignOf_pc sh P cfg ev (Nat.le_of_lt hi) hq hc]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  have h3iff : (assignOf sh P cfg ev (vxe sh i q (eIdx P e) u) = true) <->
      rdXe sh P cfg ev i q (eIdx P e) = u := by
    rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi) hq heE hu]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  rw [assignOf_vpb sh P cfg ev hi hq hc hu]
  constructor
  · intro h
    rw [asgPb] at h
    rw [List.any_eq_true] at h
    obtain ⟨i', hi', h2⟩ := h
    rw [List.any_eq_true] at h2
    obtain ⟨q', hq', h3⟩ := h2
    rw [List.any_eq_true] at h3
    obtain ⟨c', hc', h4⟩ := h3
    rw [List.any_eq_true] at h4
    obtain ⟨u', hu', h5⟩ := h4
    rw [Bool.and_eq_true] at h5
    obtain ⟨heq, hrd⟩ := h5
    obtain ⟨rfl, rfl, rfl, rfl⟩ := vpb_inj_full hq (List.mem_range.mp hq') hc
      (List.mem_range.mp hc') hu (List.mem_range.mp hu') (of_decide_eq_true heq)
    cases h6 : ev i with
    | act q' m' d' =>
        simp only [h6, hact, Bool.and_eq_true, decide_eq_true_eq] at hrd
        obtain ⟨⟨h1, h2'⟩, h3'⟩ := hrd
        subst h1
        exact ⟨h1iff.mpr ⟨m', d', h6⟩, h2iff.mpr h2', h3iff.mpr h3'⟩
    | idle =>
        simp only [h6, hact] at hrd
        exact absurd hrd (by simp)
    | ded t =>
        simp only [h6, hact] at hrd
        exact absurd hrd (by simp)
  · intro h
    obtain ⟨h1, h2', h3'⟩ := h
    obtain ⟨m, d, h6⟩ : ∃ m d, ev i = Ev.act q m d := h1iff.mp h1
    rw [asgPb]
    refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
    refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
    refine List.any_eq_true.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
    refine List.any_eq_true.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true rfl, ?_⟩
    simp only [h6, hact, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨trivial, h2iff.mp h2'⟩, h3iff.mp h3'⟩

/-- The store-leak conjunction is true exactly when the slot holds the message and the attacker
knows it. -/
theorem assignOf_vau_iff (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh)
    (hu : u < shVal sh) (hsec : storeSecret sh P q x = true) :
    (assignOf sh P cfg ev (vau sh i q x u) = true) <->
      (assignOf sh P cfg ev (vst sh i q x u) = true ∧
       assignOf sh P cfg ev (vkn sh i u) = true) := by
  have hst_iff : (assignOf sh P cfg ev (vst sh i q x u) = true) <->
      rdSt sh P cfg ev i q x = u := by
    rw [assignOf_st sh P cfg ev hi hq hx hu]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  have hkn_iff : (assignOf sh P cfg ev (vkn sh i u) = true) <->
      match valAt sh u with
      | some t => t ∈ (cfg i).kn
      | none => False := by
    rw [assignOf_kn sh P cfg ev hi hu, knHolds]
    cases h : valAt sh u with
    | none => simp [h]
    | some t => simp [h, decide_eq_true_eq]
  rw [assignOf_vau sh P cfg ev hi hq hx hu]
  constructor
  · intro h
    rw [asgAu] at h
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
    obtain ⟨rfl, rfl, rfl, rfl⟩ := vau_inj_full hq (List.mem_range.mp hq') hx
      (List.mem_range.mp hx') hu (List.mem_range.mp hu') (of_decide_eq_true heq)
    cases h6 : valAt sh u with
    | none =>
        simp only [h6] at hrd
        exact absurd hrd (by simp)
    | some t =>
        simp only [h6, Bool.and_eq_true, decide_eq_true_eq] at hrd
        obtain ⟨hst, hkn⟩ := hrd
        rw [h6] at hkn_iff
        exact ⟨hst_iff.mpr hst, hkn_iff.mpr hkn⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    cases h6 : valAt sh u with
    | none =>
        rw [h6] at hkn_iff
        rw [hkn_iff] at h2
        simp at h2
    | some t =>
        rw [asgAu]
        refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
        refine List.any_eq_true.mpr ⟨q, List.mem_range.mpr hq, ?_⟩
        refine List.any_eq_true.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
        refine List.any_eq_true.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
        rw [Bool.and_eq_true]
        refine ⟨decide_eq_true rfl, ?_⟩
        simp only [h6, Bool.and_eq_true, decide_eq_true_eq]
        rw [h6] at hkn_iff
        exact ⟨hst_iff.mp h1, hkn_iff.mp h2⟩

/-- **Clause group 6 (deduction instances).**  If the event alternative of a universe rule
instance is selected at step i, then every premise of that instance is known at step i and its
conclusion is known at step i+1: this is the propositional form of the eleven rules of
specification section 2, one clause per premise.  The selection literal `evDed sh i n` is true
exactly when the run's event is a deduction whose message is produced by instance n, which is
where the completeness of the instance enumeration (ProtSat.Complete.dedIx_spec) is used. -/
theorem sat_ded (hok : RunOK sh P cfg ev) (hsub : univSub sh)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (dedClauses sh) := by
  intro cl hcl
  simp only [dedClauses, cnfOf, eachStep, eachInst, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, h2⟩ := hcl
  obtain ⟨n, hn, h3⟩ := h2
  have hn' : n < nInst sh := List.mem_range.mp (by simpa using hn)
  cases hinst : instAt sh n with
  | none =>
      rw [dedClausesAt, hinst] at h3
      exact absurd h3 (by simp)
  | some inst =>
      rw [dedClausesAt, hinst] at h3
      rw [List.mem_append] at h3
      rcases h3 with hprem | hconcl
      · -- a premise clause
        rw [List.mem_map] at hprem
        obtain ⟨p, hp, rfl⟩ := hprem
        rcases bool_eq_cases (assignOf sh P cfg ev (evDed sh i n)) with hd | hd
        · obtain ⟨t, htev, hidx⟩ := dedEv_of_evDed sh P cfg ev hok hi hn' hd
          have htU : t ∈ sh.U := runOK_dedU sh P cfg ev hok i t htev
          have htev' : ev i = Ev.ded t := htev
          have hone : OneStep (cfg i).kn t := by
            have h2 := hrel i
            rw [htev] at h2
            exact Rel.ded_oneStep h2
          obtain ⟨n', hn', hon'⟩ :=
            dedIx_exists hsub (runOK_knU sh P cfg ev hok i) htU hone
          have hspec := dedIx_spec ⟨n', hn', hon'⟩
          have hon2 : dedInstOk sh ((cfg i).kn) n (uIdx sh (some t)) = true := by
            rw [← hidx]
            exact hspec.2
          have hall : inst.prem.all fun p' =>
              match valAt sh p' with
              | some x => decide (x ∈ (cfg i).kn)
              | none => false := by
            rw [dedInstOk, hinst] at hon2
            rw [Bool.and_eq_true] at hon2
            exact hon2.2
          rw [List.all_eq_true] at hall
          have h2' := hall p (by simpa using hp)
          have hsl : shVal sh = sh.U.length + 1 := rfl
          have hpV : p < shVal sh := by
            by_contra e
            rw [hsl] at e
            have h3' : valAt sh p = none := rget_oob_ge sh.U p (by omega)
            rw [h3'] at h2'
            simp at h2'
          have hlit : Lit.eval (assignOf sh P cfg ev) (pos (vkn sh i p)) = true := by
            rw [pos_eval, assignOf_kn sh P cfg ev (Nat.le_of_lt hi) hpV, knHolds]
            cases hval : valAt sh p with
            | none => simp [hval] at h2'
            | some x =>
                simp only [hval] at h2' ⊢
                exact h2'
          exact clause2_right _ _ _ hlit
        · exact clause2_left _ _ _ (by simp [neg_eval, hd])
      · -- the conclusion clause
        simp only [List.mem_singleton] at hconcl
        subst hconcl
        rcases bool_eq_cases (assignOf sh P cfg ev (evDed sh i n)) with hd | hd
        · obtain ⟨t, htev, hidx⟩ := dedEv_of_evDed sh P cfg ev hok hi hn' hd
          have htU : t ∈ sh.U := runOK_dedU sh P cfg ev hok i t htev
          have hone : OneStep (cfg i).kn t := by
            have h2 := hrel i
            rw [htev] at h2
            exact Rel.ded_oneStep h2
          obtain ⟨n', hn', hon'⟩ :=
            dedIx_exists hsub (runOK_knU sh P cfg ev hok i) htU hone
          have hspec := dedIx_spec ⟨n', hn', hon'⟩
          have hon2 : dedInstOk sh ((cfg i).kn) n (uIdx sh (some t)) = true := by
            rw [← hidx]
            exact hspec.2
          have hc' : inst.concl = uIdx sh (some t) := by
            rw [dedInstOk, hinst] at hon2
            rw [Bool.and_eq_true] at hon2
            exact of_decide_eq_true hon2.1
          have h2r := hrel i
          rw [htev] at h2r
          have hkn : (cfg (i + 1)).kn = (cfg i).kn ++ [t] := Rel.ded_kn h2r
          have hcV : inst.concl < shVal sh := by rw [hc']; exact uIdx_lt' sh _
          have hlit : Lit.eval (assignOf sh P cfg ev) (pos (vkn sh (i + 1) inst.concl)) = true := by
            rw [pos_eval, assignOf_kn sh P cfg ev (Nat.succ_le_of_lt hi) hcV, knHolds]
            have hv : valAt sh inst.concl = some t := by rw [hc']; exact valAt_uIdx_some sh htU
            rw [hv, hkn]
            exact decide_eq_true (by simp)
          exact clause2_right _ _ _ hlit
        · exact clause2_left _ _ _ (by simp [neg_eval, hd])

/-- **Clause group 7 (publisher conjunctions).**  Each send publisher is a Tseitin definition of
the conjunction "session q acts at step i with program counter c and the value it sends is u";
the characteristic assignment sets the auxiliary variable exactly when the three conjuncts hold
(ProtSat.Complete.assignOf_vpb_iff), which is what the completeness direction of
ProtSat.sat_andNDef requires. -/
theorem sat_pubAux (hok : RunOK sh P cfg ev) :
    Sat (assignOf sh P cfg ev) (pubAuxClauses sh P) := by
  intro cl hcl
  simp only [pubAuxClauses, cnfOf, eachStep, eachSess, eachPc, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, h2⟩ := hcl
  obtain ⟨q, hq, h3⟩ := h2
  obtain ⟨c, hc, h4⟩ := h3
  obtain ⟨u, hu, h5⟩ := h4
  have huV : u < shVal sh := Nat.lt_succ_of_lt hu
  cases h : P.actionAt q c with
  | none =>
      rw [pubAuxEntry, h] at h5
      exact absurd h5 (by simp)
  | some act =>
      cases act with
      | send a e =>
          have heE : eIdx P e < shE sh :=
            runOK_eIdx sh P cfg ev hok e (mem_allExprs_send h)
          rw [pubAuxEntry, h] at h5
          have hiff := assignOf_vpb_iff sh P cfg ev hok hi hq hc huV h
          refine (sat_andNDef.mpr ⟨?_, ?_⟩) cl h5
          · intro haux l hl
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
            rcases hl with rfl | rfl | rfl
            · exact ((hiff.mp haux).1)
            · exact ((hiff.mp haux).2.1)
            · exact ((hiff.mp haux).2.2)
          · intro hall
            refine hiff.mpr ⟨by simpa using hall (pos (evAct sh i q)) (by simp),
              by simpa using hall (pos (vpc sh i q c)) (by simp),
              by simpa using hall (pos (vxe sh i q (eIdx P e) u)) (by simp)⟩
      | _ =>
          rw [pubAuxEntry, h] at h5
          exact absurd h5 (by simp)

/-- **Clause group 10 (store-leak conjunctions).**  Each store-leak auxiliary variable defines
the conjunction "session q holds the message numbered u at step i and the attacker knows it", and
again the characteristic assignment agrees with the definition. -/
theorem sat_leakAux (hok : RunOK sh P cfg ev) :
    Sat (assignOf sh P cfg ev) (leakAuxClauses sh P) := by
  intro cl hcl
  simp only [leakAuxClauses, cnfOf, eachStep1, eachSess, eachVar, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, h2⟩ := hcl
  obtain ⟨q, hq, h3⟩ := h2
  obtain ⟨x, hx, h4⟩ := h3
  rw [leakAuxEntry] at h4
  by_cases hsec : storeSecret sh P q x
  · rw [if_pos hsec, List.mem_flatMap] at h4
    obtain ⟨u, hu, h5⟩ := h4
    have huV : u < shVal sh := Nat.lt_succ_of_lt (List.mem_range.mp hu)
    rw [andNDef] at h5
    have hiff := assignOf_vau_iff sh P cfg ev (Nat.le_of_lt_succ hi) hq hx huV hsec
    refine (sat_andNDef.mpr ⟨?_, ?_⟩) cl h5
    · intro haux l hl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · exact (hiff.mp haux).1
      · exact (hiff.mp haux).2
    · intro hall
      refine hiff.mpr ⟨by simpa using hall (pos (vst sh i q x u)) (by simp),
        by simpa using hall (pos (vkn sh i u)) (by simp)⟩
  · rw [if_neg hsec] at h4
    exact absurd h4 (by simp)

/-- The freshness side condition of ProtSat.Rel.rFresh, recovered from a legal step. -/
theorem Rel.fresh_used {P₁ : Protocol} {C C' : Cfg} {q : Nat} {x : Nat} {N : NonceName}
    {m : Term} {d : NonceName} (h : Rel P₁ C (Ev.act q m d) C')
    (hamt : P₁.actionAt q (pcOf C q) = some (Action.fresh x N)) : nonceUsed C d = false := by
  cases h with
  | rFresh _ _ hn => exact hn
  | rRecv hq => exact absurd (hq.symm.trans hamt) (by simp)
  | rAssign hq => exact absurd (hq.symm.trans hamt) (by simp)
  | rSend hq => exact absurd (hq.symm.trans hamt) (by simp)
  | rCheck hq => exact absurd (hq.symm.trans hamt) (by simp)
  | rSecret hq => exact absurd (hq.symm.trans hamt) (by simp)
  | rClaim hq => exact absurd (hq.symm.trans hamt) (by simp)
  | rCommit hq => exact absurd (hq.symm.trans hamt) (by simp)

/-- With a duplicate-free universe the value index of a message is its unique position. -/
theorem uIdx_eq_of_valAt (hn : List.Nodup sh.U) {u : Nat} {t : Term} (hv : valAt sh u = some t) :
    uIdx sh (some t) = u := by
  have htU : t ∈ sh.U := by
    show t ∈ sh.U
    have h0 : rget sh.U u = some t := hv
    exact rget_some_mem sh.U u t h0
  have h1 : rget sh.U (ixOf t sh.U) = some t := rget_ixOf sh.U t htU
  have h2 : ixOf t sh.U = u := rget_nodup_inj sh.U hn _ _ t h1 hv
  show (if t ∈ sh.U then ixOf t sh.U else sh.U.length) = u
  rw [if_pos htU]
  exact h2

/-- A nonce held by some session is used. -/
theorem nonceUsed_of_store {C : Cfg} {r x : Nat} {N : NonceName}
    (hr : r < C.sess.length) (h : readVar x (storeOf C r) = some (Term.nonce N)) :
    nonceUsed C N = true := by
  obtain ⟨st, hst⟩ := sessAt_lt hr
  have hmem : st ∈ C.sess := by
    unfold sessAt at hst
    exact rget_some_mem C.sess r st hst
  have hstore : storeOf C r = st.store := by
    unfold storeOf
    rw [hst]
    simp
  have h1 : Term.nonce N ∈ storeVals st.store := by
    rw [← hstore]
    exact readVar_mem_storeVals h
  unfold nonceUsed
  rw [Bool.or_eq_true, List.any_eq_true]
  exact Or.inl ⟨st, hmem, List.contains_iff_mem.mpr h1⟩

/-- A nonce the attacker knows is used. -/
theorem nonceUsed_of_kn {C : Cfg} {N : NonceName} (h : Term.nonce N ∈ C.kn) :
    nonceUsed C N = true := by
  unfold nonceUsed
  rw [Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr h)

/-- An unused nonce is neither stored nor known. -/
theorem nonceUsed_false_store {C : Cfg} {r x : Nat} {N : NonceName}
    (h : nonceUsed C N = false) (h2 : readVar x (storeOf C r) = some (Term.nonce N)) : False := by
  by_cases hr : r < C.sess.length
  · exact absurd (nonceUsed_of_store hr h2) (by simpa using h)
  · have hlen : storeOf C r = [] := by
      unfold storeOf sessAt
      rw [rget_oob_ge (C.sess) r (Nat.not_lt.mp hr)]
      simp
    rw [hlen] at h2
    simp [readVar, Expr.lookup] at h2

/-- **Clause group 8 (knowledge is justified).**  A message the attacker knows after step i was
either known before it, or is the conclusion of a deduction instance that fired at step i, or
was published by a session that sent it: the propositional form of the requirement that the
attacker cannot invent messages (specification section 2).  Without this group the solver could
declare every universe message known, which is exactly the approximation the specification
forbids. -/
theorem sat_knSupport (hok : RunOK sh P cfg ev) (hsub : univSub sh) (hn : List.Nodup sh.U)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (knSupportClauses sh P) := by
  intro cl hcl
  unfold knSupportClauses cnfOf eachStep mapMsg at hcl
  obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl
  obtain ⟨u, hu, heq⟩ := List.mem_map.mp h2
  subst heq
  have hi' : i < sh.steps := List.mem_range.mp hi
  have huV : u < shVal sh := Nat.lt_succ_of_lt (List.mem_range.mp hu)
  rcases bool_eq_cases (assignOf sh P cfg ev (vkn sh (i + 1) u)) with hk | hk
  · -- the message is known after the step: it must be justified
    have hvu : ∃ t, valAt sh u = some t ∧ t ∈ (cfg (i + 1)).kn := by
      rw [assignOf_kn sh P cfg ev (Nat.succ_le_of_lt hi') huV, knHolds] at hk
      cases h : valAt sh u with
      | none => simp [h] at hk
      | some t =>
          simp only [h] at hk
          exact ⟨t, rfl, of_decide_eq_true hk⟩
    obtain ⟨t, hv, htm⟩ := hvu
    have htU : t ∈ sh.U := runOK_knU sh P cfg ev hok (i + 1) t htm
    have hut : uIdx sh (some t) = u := uIdx_eq_of_valAt sh hn hv
    by_cases hki : t ∈ (cfg i).kn
    · refine clause_eval_holds (pos (vkn sh i u))
        (List.mem_append_left _ (List.Mem.tail _ (List.Mem.head _))) ?_
      rw [pos_eval, assignOf_kn sh P cfg ev (Nat.le_of_lt hi') huV, knHolds, hv]
      exact decide_eq_true hki
    · rcases Rel.kn_step (hrel i) with heq | ⟨t', het, hkn⟩ |
        ⟨q, t', m, d, a, x, het, hkn, hamt, heval⟩
      · rw [heq] at htm
        exact absurd htm hki
      · -- a deduction step produced it
        have ht' : t' = t := by
          rw [hkn, List.mem_append, List.mem_singleton] at htm
          rcases htm with h | h
          · exact absurd h hki
          · exact h.symm
        have hone : OneStep (cfg i).kn t := by
          have h2 := hrel i
          rw [het, ht'] at h2
          exact Rel.ded_oneStep h2
        have hspec := dedIx_spec (dedIx_exists hsub (runOK_knU sh P cfg ev hok i) htU hone)
        have hsel : assignOf sh P cfg ev
            (evDed sh i (dedIx sh ((cfg i).kn) (uIdx sh (some t)))) = true := by
          have hsev : shEv sh = 1 + shS sh + nInst sh := rfl
          rw [evDed, assignOf_ev sh P cfg ev hi'
            (by rw [hsev]; exact Nat.add_lt_add_left hspec.1 _)]
          refine decide_eq_true ?_
          have h2 : rdEv sh P cfg ev i =
              1 + shS sh + dedIx sh ((cfg i).kn) (uIdx sh (some t)) := by
            unfold rdEv
            rw [het, ht']
          rw [h2]
        have hmem : pos (evDed sh i (dedIx sh ((cfg i).kn) (uIdx sh (some t)))) ∈
            [neg (vkn sh (i + 1) u), pos (vkn sh i u)] ++ publisherLits sh P i u := by
          rw [List.mem_append]
          refine Or.inr ?_
          unfold publisherLits
          rw [List.mem_append]
          refine Or.inr ?_
          unfold litsInst
          simp only [List.mem_flatMap]
          refine ⟨dedIx sh ((cfg i).kn) (uIdx sh (some t)), List.mem_range.mpr hspec.1, ?_⟩
          rw [instPublisher]
          cases hinst : instAt sh (dedIx sh ((cfg i).kn) (uIdx sh (some t))) with
          | none =>
              have hx : dedInstOk sh ((cfg i).kn)
                  (dedIx sh ((cfg i).kn) (uIdx sh (some t))) (uIdx sh (some t)) = true := hspec.2
              rw [dedInstOk, hinst] at hx
              simp at hx
          | some ins =>
              have h2 := hspec.2
              simp only [dedInstOk, hinst] at h2
              rw [Bool.and_eq_true] at h2
              have hc : ins.concl = uIdx sh (some t) := of_decide_eq_true h2.1
              have hmem2 : pos (evDed sh i (dedIx sh ((cfg i).kn) (uIdx sh (some t)))) ∈
                  if ins.concl = u then
                    [pos (evDed sh i (dedIx sh ((cfg i).kn) (uIdx sh (some t))))]
                  else [] := by
                rw [if_pos (by rw [hc, hut])]
                exact List.Mem.head _
              exact hmem2
        exact clause_eval_holds
          (pos (evDed sh i (dedIx sh ((cfg i).kn) (uIdx sh (some t))))) hmem hsel
      · -- a send published it
        have ht' : t' = t := by
          rw [hkn, List.mem_append, List.mem_singleton] at htm
          rcases htm with h | h
          · exact absurd h hki
          · exact h.symm
        have hqS : q < sh.nS1 := (runOK_act sh P cfg ev hok i q m d het).1
        have hq' : q < shS sh := by rw [shS]; omega
        have hc : pcOf (cfg i) q < shPc sh := runOK_pc sh P cfg ev hok i q hqS
        have hmemx : x ∈ allExprs P := mem_allExprs_send hamt
        have hiff := assignOf_vpb_iff sh P cfg ev hok hi' hq' hc huV hamt
        have hxe : rdXe sh P cfg ev i q (eIdx P x) = u := by
          rw [rdXe_eIdx sh P cfg ev hmemx, heval, ht']
          exact hut
        have hA : assignOf sh P cfg ev (evAct sh i q) = true := by
          rw [assignOf_evAct sh P cfg ev hi' hq']
          refine decide_eq_true ?_
          unfold rdEv
          rw [het]
        have hP : assignOf sh P cfg ev (vpc sh i q (pcOf (cfg i) q)) = true := by
          rw [assignOf_pc sh P cfg ev (Nat.le_of_lt hi') hq' hc]
          exact decide_eq_true rfl
        have hX : assignOf sh P cfg ev (vxe sh i q (eIdx P x) u) = true := by
          rw [assignOf_xe sh P cfg ev (Nat.le_of_lt hi') hq'
            (runOK_eIdx sh P cfg ev hok x hmemx) huV]
          exact decide_eq_true hxe
        have hpub : assignOf sh P cfg ev (vpb sh i q (pcOf (cfg i) q) u) = true :=
          hiff.mpr ⟨hA, hP, hX⟩
        have hmem : pos (vpb sh i q (pcOf (cfg i) q) u) ∈
            [neg (vkn sh (i + 1) u), pos (vkn sh i u)] ++ publisherLits sh P i u := by
          rw [List.mem_append]
          refine Or.inr ?_
          unfold publisherLits
          rw [List.mem_append]
          refine Or.inl ?_
          unfold litsSess litsPc
          simp only [List.mem_flatMap]
          refine ⟨q, List.mem_range.mpr hq', pcOf (cfg i) q, List.mem_range.mpr hc, ?_⟩
          rw [sendPubLit, hamt]
          exact List.Mem.head _
        exact clause_eval_holds (pos (vpb sh i q (pcOf (cfg i) q) u)) hmem hpub
  · exact clause_eval_holds (neg (vkn sh (i + 1) u)) (List.mem_append_left _ (List.Mem.head _))
      (by simp [neg_eval, hk])

/-- When the freshness literal of a fresh step is selected, the nonce it names is the nonce the
event generated, and that nonce is unused in the current configuration. -/
theorem fresh_selected (hok : RunOK sh P cfg ev)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1)))
    (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh)
    (h : P.actionAt q c = some (Action.fresh xa Na))
    (hg : Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c) = false)
    (hd : d < shD sh) (hrd : rget sh.D d = some N)
    (hf : assignOf sh P cfg ev (vfr sh i q d) = true) :
    nonceUsed (cfg i) N = false := by
  obtain ⟨⟨m, dd, hevm⟩, hpcd⟩ := (actGuard_false sh P cfg ev hok hi hq hc).mp hg
  have hpcq : pcOf (cfg i) q = c := hpcd
  have h1 : rdFr sh P cfg ev i q = d := by
    rw [assignOf_fr sh P cfg ev hi hq hd] at hf
    exact of_decide_eq_true hf
  have h2 : rdFr sh P cfg ev i q = ixOf dd sh.D := by simp [rdFr, hevm]
  have hdeq : d = ixOf dd sh.D := h1.symm.trans h2
  have h3 : rget sh.D (ixOf dd sh.D) = some N := by
    rw [← hdeq]
    exact hrd
  have h4 : rget sh.D (ixOf dd sh.D) = some dd :=
    rget_ixOf sh.D dd (runOK_act_dD sh P cfg ev hok hevm ⟨xa, Na, by rw [hpcq]; exact h⟩)
  have hdd : dd = N := Option.some.inj (h4.symm.trans h3)
  have h2r : Rel P (cfg i) (Ev.act q m dd) (cfg (i + 1)) := by rw [← hevm]; exact hrel i
  have h5 : nonceUsed (cfg i) dd = false := Rel.fresh_used h2r (by rw [hpcq]; exact h)
  rw [hdd] at h5
  exact h5

/-- **Clause group 9 (freshness).**  The nonce a session generates may not already sit in some
session's store, nor be known to the attacker: the propositional form of the side condition of
ProtSat.Rel.rFresh (ProtSat.nonceUsed). -/
theorem sat_fresh (hok : RunOK sh P cfg ev)
    (hD : ∀ N ∈ sh.D, Term.nonce N ∈ sh.U)
    (hrel : ∀ i, Rel P (cfg i) (ev i) (cfg (i + 1))) :
    Sat (assignOf sh P cfg ev) (freshClauses sh P) := by
  intro cl hcl
  unfold freshClauses cnfOf eachStep eachSess eachPc at hcl
  obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hcl
  obtain ⟨q, hq, h3⟩ := List.mem_flatMap.mp h2
  obtain ⟨c, hc, h4⟩ := List.mem_flatMap.mp h3
  have hi' : i < sh.steps := List.mem_range.mp hi
  have hq' : q < shS sh := List.mem_range.mp hq
  have hc' : c < shPc sh := List.mem_range.mp hc
  unfold freshClausesAt at h4
  cases h : P.actionAt q c with
  | none =>
      rw [h] at h4
      exact absurd h4 (by simp)
  | some act =>
      cases act with
      | fresh xa Na =>
          rw [h] at h4
          rw [List.mem_flatMap] at h4
          obtain ⟨d, hd, h5⟩ := h4
          have hd' : d < shD sh := List.mem_range.mp hd
          rw [freshUseClauses] at h5
          cases hrd : rget sh.D d with
          | none =>
              rw [hrd] at h5
              exact absurd h5 (by simp)
          | some N =>
              rw [hrd] at h5
              have hN : Term.nonce N ∈ sh.U := hD N (rget_some_mem sh.D d N hrd)
              have hnU : uIdx sh (some (Term.nonce N)) < sh.U.length := uIdx_some_lt sh hN
              rw [List.mem_append] at h5
              rcases h5 with hstore | hknown
              · -- a store slot may not already hold the nonce
                rw [List.mem_flatMap] at hstore
                obtain ⟨r, hr, h6⟩ := hstore
                have hr' : r < shS sh := List.mem_range.mp hr
                rw [List.mem_map] at h6
                obtain ⟨y, hy, heq⟩ := h6
                have hyV : y < shV sh := List.mem_range.mp hy
                subst heq
                rcases bool_eq_cases (Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c))
                    with hg | hg
                · exact clause_eval_append_left_true _ _ _ hg
                · rcases bool_eq_cases (assignOf sh P cfg ev (vfr sh i q d)) with hf | hf
                  · have hused :=
                      fresh_selected sh P cfg ev hok hrel hi' hq' hc' h hg hd' hrd hf
                    refine clause_eval_append_right_true _ _ _
                      (clause2_right _ _ _ (neg_lit _ _ ?_))
                    rw [assignOf_st sh P cfg ev (Nat.le_of_lt hi') hr' hyV (uIdx_lt' sh _)]
                    refine decide_eq_false ?_
                    intro heq2
                    have h7 : valAt sh (uIdx sh (some (Term.nonce N))) = some (Term.nonce N) :=
                      valAt_uIdx_some sh hN
                    have h8 : uIdx sh (readVar y (storeOf (cfg i) r)) =
                        uIdx sh (some (Term.nonce N)) := heq2
                    have hval : valAt sh (uIdx sh (readVar y (storeOf (cfg i) r))) =
                        some (Term.nonce N) := by
                      rw [h8]
                      exact h7
                    cases hrv : readVar y (storeOf (cfg i) r) with
                    | none => simp [hrv] at hval
                    | some v =>
                        have hvU : v ∈ sh.U := by
                          by_cases hrS : r < sh.nS1
                          · exact runOK_storeU sh P cfg ev hok i r v hrS
                              (readVar_mem_storeVals hrv)
                          · have hlen : (cfg i).sess.length = sh.nS1 :=
                              runOK_sessLen sh P cfg ev hok i
                            have hempty : storeOf (cfg i) r = [] := by
                              unfold storeOf sessAt
                              rw [rget_oob_ge (cfg i).sess r (by omega)]
                              rfl
                            rw [hempty] at hrv
                            simp [readVar, Expr.lookup] at hrv
                        have h9 : uIdx sh (readVar y (storeOf (cfg i) r)) = uIdx sh (some v) := by
                          rw [hrv]
                        rw [h9, valAt_uIdx_some sh hvU] at hval
                        have heqv : v = Term.nonce N := Option.some.inj hval
                        subst heqv
                        exact nonceUsed_false_store hused hrv
                  · exact clause_eval_append_right_true _ _ _
                      (clause2_left _ _ _ (by simp [neg_eval, hf]))
              · -- the attacker may not already know the nonce
                simp only [List.mem_singleton] at hknown
                subst hknown
                rcases bool_eq_cases (Clause.eval (assignOf sh P cfg ev) (actGuard sh i q c))
                    with hg | hg
                · exact clause_eval_append_left_true _ _ _ hg
                · rcases bool_eq_cases (assignOf sh P cfg ev (vfr sh i q d)) with hf | hf
                  · have hused :=
                      fresh_selected sh P cfg ev hok hrel hi' hq' hc' h hg hd' hrd hf
                    refine clause_eval_append_right_true _ _ _
                      (clause2_right _ _ _ (neg_lit _ _ ?_))
                    rw [assignOf_kn sh P cfg ev (Nat.le_of_lt hi') (uIdx_lt' sh _), knHolds,
                      valAt_uIdx_some sh hN]
                    refine decide_eq_false ?_
                    intro hmem
                    have h1 : nonceUsed (cfg i) N = true := nonceUsed_of_kn hmem
                    rw [h1] at hused
                    simp at hused
                  · exact clause_eval_append_right_true _ _ _
                      (clause2_left _ _ _ (by simp [neg_eval, hf]))
      | _ =>
          rw [h] at h4
          exact absurd h4 (by simp)

/-- **The secret hypothesis.**  The bounds must be able to name the declared secrets: every
secret store variable has a store slot in the shape, and every closed secret message is a
universe message.  Without this the violation clause of the encoding could not even mention the
leak - the same kind of bound hypothesis specification section 4 asks for. -/
def SecretsOK (sh : Shape) (P : Protocol) : Prop :=
  (∀ q x, (Secret.store q x) ∈ P.secrets → x < shV sh) ∧
    (∀ s ∈ P.closedSecretTerms, s ∈ sh.U)

/-- Reading an in-range position of a run gives one of its configurations. -/
theorem cfgAt_lt : ∀ (Cs : List Cfg) (i : Nat), i < Cs.length ->
    ∃ C, C ∈ Cs ∧ cfgAt Cs i = C := by
  intro Cs
  induction Cs with
  | nil => intro i h; exact absurd h (by simp)
  | cons C rest ih =>
      intro i h
      cases i with
      | zero => exact ⟨C, List.Mem.head _, cfgAt_head⟩
      | succ k =>
          have hlenC : (C :: rest).length = rest.length + 1 := rfl
          rw [hlenC] at h
          have hk : k < rest.length := by omega
          have hne : rest ≠ [] := by
            intro he
            rw [he] at hk
            simp at hk
          obtain ⟨D, hD, hEq⟩ := ih k hk
          exact ⟨D, List.mem_cons.mpr (Or.inr hD), by
            rw [cfgAt_cons_succ hne k, hEq]⟩

/-- **Clause group 11 (the violation).**  The violation clause is satisfied: the run really
leaks, and the leak is named by one of the literals the clause offers. -/
theorem sat_violation (hok : RunOK sh P cfg ev) (hsec : SecretsOK sh P)
    (hleak : ∃ i, i ≤ sh.steps ∧ Leak P (cfg i)) :
    Sat (assignOf sh P cfg ev) (violationClauses sh P) := by
  intro cl hcl
  rw [violationClauses, cnfOf, List.mem_singleton] at hcl
  subst hcl
  obtain ⟨i, hi, hleak'⟩ := hleak
  rcases hleak' with ⟨s, hs, hkn⟩ | ⟨q, x, v, hsq, hread, hvkn⟩
  · -- a closed declared secret is known
    have hsU : s ∈ sh.U := hsec.2 s hs
    set u := uIdx sh (some s) with hu_def
    have huV : u < shVal sh := by rw [hu_def]; exact uIdx_lt' sh _
    have hlen : u < sh.U.length := uIdx_some_lt sh hsU
    have hval : valAt sh u = some s := valAt_uIdx_some sh hsU
    have hlit : pos (vkn sh i u) ∈ violationLits sh P := by
      unfold violationLits litsStep1
      rw [List.mem_flatMap]
      refine ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      rw [List.mem_append]
      refine Or.inl ?_
      unfold closedLeakLits
      rw [List.mem_filterMap]
      refine ⟨u, List.mem_range.mpr hlen, ?_⟩
      simp [hval, hs]
    have htrue : Lit.eval (assignOf sh P cfg ev) (pos (vkn sh i u)) = true := by
      rw [pos_eval, assignOf_kn sh P cfg ev hi huV, knHolds, hval]
      exact decide_eq_true hkn
    exact clause_eval_holds (pos (vkn sh i u)) hlit htrue
  · -- a store secret leaks
    obtain ⟨hxV, _⟩ := hsec
    have hx : x < shV sh := hxV q x hsq
    have hread' : readVar x (storeOf (cfg i) q) = some v := by
      cases h : sessAt (cfg i) q with
      | none => simp [h] at hread
      | some st =>
          have h2 : (sessAt (cfg i) q).map (fun st => readVar x st.store) =
              some (readVar x st.store) := by simp [h]
          rw [h2] at hread
          have hst : storeOf (cfg i) q = st.store := by
            unfold storeOf
            rw [h]
            simp
          rw [hst]
          exact Option.some.inj hread
    have hqS : q < (cfg i).sess.length := by
      by_contra e
      have h2 : storeOf (cfg i) q = [] := by
        unfold storeOf sessAt
        rw [rget_oob_ge (cfg i).sess q (Nat.not_lt.mp e)]
        simp
      rw [h2] at hread'
      simp [readVar, Expr.lookup] at hread'
    have hqS' : q < sh.nS1 := by
      have hlen : (cfg i).sess.length = sh.nS1 := runOK_sessLen sh P cfg ev hok i
      rw [← hlen]
      exact hqS
    have hsecb : storeSecret sh P q x = true := by
      unfold storeSecret
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hsq⟩
    have hqS'' : q < shS sh := by rw [shS]; omega
    have hvU : v ∈ sh.U := runOK_storeU sh P cfg ev hok i q v hqS'
      (readVar_mem_storeVals hread')
    set u := uIdx sh (some v) with hu_def
    have huV : u < shVal sh := by rw [hu_def]; exact uIdx_lt' sh _
    have hlen : u < sh.U.length := uIdx_some_lt sh hvU
    have hrd : rdSt sh P cfg ev i q x = u := by
      show uIdx sh (readVar x (storeOf (cfg i) q)) = uIdx sh (some v)
      rw [hread']
    have hkn : assignOf sh P cfg ev (vkn sh i u) = true := by
      rw [assignOf_kn sh P cfg ev hi huV, knHolds, hu_def, valAt_uIdx_some sh hvU]
      exact decide_eq_true hvkn
    have hst : assignOf sh P cfg ev (vst sh i q x u) = true := by
      rw [assignOf_st sh P cfg ev hi hqS'' hx huV]
      exact decide_eq_true hrd
    have hiff := assignOf_vau_iff sh P cfg ev hi hqS'' hx huV hsecb
    have hvau : assignOf sh P cfg ev (vau sh i q x u) = true :=
      hiff.mpr ⟨hst, hkn⟩
    have hlit : pos (vau sh i q x u) ∈ violationLits sh P := by
      unfold violationLits litsStep1
      rw [List.mem_flatMap]
      refine ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
      rw [List.mem_append]
      refine Or.inr ?_
      unfold storeLeakLits litsSess litsVar
      refine List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (by rw [shS]; omega),
        List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩⟩
      unfold storeLeakLitsAt
      rw [if_pos hsecb, List.mem_map]
      exact ⟨u, List.mem_range.mpr hlen, rfl⟩
    exact clause_eval_holds (pos (vau sh i q x u)) hlit hvau


/-- An in-range read of a run's configuration list gives the configuration at that position. -/
theorem cfgAt_eq_of_rget : ∀ (Cs : List Cfg) (i : Nat) (C : Cfg), rget Cs i = some C ->
    cfgAt Cs i = C := by
  intro Cs
  induction Cs with
  | nil => intro i C h; exact absurd h (by simp [rget])
  | cons D rest ih =>
      intro i C h
      cases i with
      | zero =>
          have hDC : D = C := Option.some.inj h
          subst hDC
          exact cfgAt_head
      | succ k =>
          by_cases hne : rest = []
          · subst hne
            simp [rget] at h
          · rw [cfgAt_cons_succ hne k]
            exact ih k C (by simpa [rget] using h)

/-- **Encoding completeness (specification 8B).**  Every valid bounded attack execution of the
protocol is represented by a satisfying assignment of the generated CNF.

The assignment is the characteristic function of the run (ProtSat.Complete.assignOf): a
propositional variable is true exactly when the semantic fact it names holds.  The theorem is
the converse of ProtSat.Encoding.encoding_sound (8A), and together they are the correspondence
between symbolic protocol attacks and satisfying assignments of the formula: within the declared
bounds the two statements are the same statement.

The hypotheses are the bounds conditions of specification section 4, collected in
ProtSat.Complete.RunOK (the run stays inside the shape), ProtSat.Encode.univClosed (the universe
names the messages the protocol computes), ProtSat.Complete.univSub (the universe is closed under
subterms, needed to enumerate the attacker's rule instances - now discharged by
ProtSat.Complete.univSub_shapeOf, so it is no longer a hypothesis) and ProtSat.Complete.SecretsOK (the
bounds can name the declared secrets).  None of them is a technicality: a run that leaves the
universe has no finite name, and a violation the encoding cannot mention cannot be found. -/
theorem encoding_complete {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hU : univClosed (shapeOf P B) P)
    (hsec : SecretsOK (shapeOf P B) P)
    (hrun : Runs P (initCfg P) tr Cs) (hlen : tr.length ≤ B.steps)
    (hleak : runsLeaks P Cs) (hbnd : WithinBounds P B (cfgAt Cs) (evAt tr)) :
    Satisfiable (encode P B) := by
  refine ⟨assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr), ?_⟩
  intro cl hcl
  rw [encode, cnfOf, List.mem_flatMap] at hcl
  obtain ⟨g, hg, hc⟩ := hcl
  have hrel : ∀ i, Rel P (cfgAt Cs i) (evAt tr i) (cfgAt Cs (i + 1)) := (runs_rel hrun).2
  have hcfg0 : cfgAt Cs 0 = initCfg P := ((runs_rel hrun).1).symm
  have hleak' : ∃ i, i ≤ (shapeOf P B).steps ∧ Leak P (cfgAt Cs i) := by
    obtain ⟨C, hC, hleakC⟩ := hleak
    obtain ⟨i, hi, hrg⟩ := mem_rget Cs C hC
    have hlenCs : Cs.length = tr.length + 1 := runs_length hrun
    have hbnd : i ≤ (shapeOf P B).steps := by
      have hsteps : (shapeOf P B).steps = B.steps := rfl
      rw [hsteps]
      omega
    exact ⟨i, hbnd, by rw [cfgAt_eq_of_rget Cs i C hrg]; exact hleakC⟩
  simp only [encodeGroups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sat_oneHot (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd (univSub_shapeOf P B) hrel cl hc
  · exact sat_init (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hcfg0 cl hc
  · exact sat_frame (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel cl hc
  · exact sat_eval (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd cl hc
  · exact sat_step (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel cl hc
  · exact sat_ded (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd (univSub_shapeOf P B) hrel cl hc
  · exact sat_pubAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd cl hc
  · exact sat_knSupport (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd (univSub_shapeOf P B) U_nodup
      hrel cl hc
  · exact sat_fresh (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
      (fun N hN => nonces_subset_univ P B N hN) hrel cl hc
  · exact sat_leakAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd cl hc
  · exact sat_violation (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hsec hleak' cl hc

end ProtSat.Complete
