/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Bounded
import ProtSat.OneHot

/-!
# ProtSat: compiling bounded protocol reachability into CNF (specification section 5)

## What is encoded

For a protocol P, bounds B = (L steps, rounds of closure) and universe U = Bounded.univ
P B, the CNF "encode P B" is satisfiable exactly when P has a bounded attack within
those bounds.  The Boolean variables are grouped by the semantic role they play:

    pc  i q c      session q's program counter at step i is c
    st  i q x u    session q's variable x holds value u at step i
    kn  i u        the attacker knows U[u] at step i
    ev  i k        the event at step i is the k-th alternative
                   (idle, "session q acts", or "attacker derives U[u]")
    dl  i q u      the message delivered to session q at step i is U[u]
    fr  i q d      the nonce value session q picks at step i is D[d]
    xe  i q c e u  at step i, session q with pc c, subexpression e of that action
                   has value u
    ob  i q c u    session q acts at step i with pc c and publishes U[u]

The clause groups are:

* oneHotClauses    - each group is one-hot (exactly one value selected);
* initClauses      - step 0 is the initial configuration;
* frameClauses     - a session that does not act keeps its pc and store; knowledge is
  monotone;
* stepClauses      - the transition clauses: if session q acts while its pc is c, the
  successor is the one the operational semantics prescribes for the action at (q, c);
* evalClauses      - Tseitin definitional clauses for expression evaluation, one group
  of clauses per subexpression, so the encoding is linear in the size of the protocol
  rather than exponential in the number of variables;
* dedClauses       - a "derive" event must be justified by one instance of an attacker
  rule over the knowledge of the previous step (one clause group per rule of
  specification section 2);
* knSupportClauses - knowledge at step i+1 is either already known, or published by a
  send at step i, or the conclusion of a derive event at step i.  This is what makes the
  decoded knowledge *justified* rather than guessed (specification 8A);
* freshClauses     - the fresh value belongs to the nonce domain and is unused;
* violationClauses - at least one declared violation occurs.

## Why this is not trace enumeration

Specification section 5 forbids enumerating all traces and encoding a precomputed
answer.  Here the search space is the product of the per-step choices (which session
acts, which message is delivered, which nonce is picked, which term the attacker
derives), and the formula only says that the sequence of states is a run of the
transition system.  The solver, not the encoder, decides which trace (if any) exists:
the encoder never evaluates the transition relation on a complete trace.

## Indexing

Variables are allocated by a linear (base-expansion) encoding: group g occupies the
half-open interval [base_g, base_g + size_g), and inside a group the index is a
positional code in the group's own ranges.  The generic injectivity lemmas lin_inj2 and
lin_inj3 do the bookkeeping once, so no group can alias another and no two distinct
domain elements share a variable.
-/

namespace ProtSat.Encode

open ProtSat Term OneHot
open ProtSat.Bounded
open ProtSat.Attacker

/-! ### Injectivity of positional codes -/

/-- Two-level positional code is injective below the stride: the remainder modulo the
stride recovers the last coordinate, and cancelling it recovers the first. -/
theorem lin_inj2 {a b a' b' K : Nat} (hK : 0 < K) (hb : b < K) (hb' : b' < K)
    (h : a * K + b = a' * K + b') : a = a' ∧ b = b' := by
  have h1 : (a * K + b) % K = b := by
    rw [Nat.add_comm, Nat.mul_comm a K, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h2 : (a' * K + b') % K = b' := by
    rw [Nat.add_comm, Nat.mul_comm a' K, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
  have hc : b = b' := by
    rw [<- h1, <- h2, h]
  subst hc
  have hk : a * K = a' * K := Nat.add_right_cancel h
  exact ⟨Nat.eq_of_mul_eq_mul_right hK hk, rfl⟩

/-- Three-level positional code is injective below the strides. -/
theorem lin_inj3 {a b c a' b' c' K M : Nat} (hK : 0 < K) (hM : 0 < M)
    (hb : b < K) (hb' : b' < K) (hc : c < M) (hc' : c' < M)
    (h : (a * K + b) * M + c = (a' * K + b') * M + c') : a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, hc2⟩ := lin_inj2 hM hc hc' h
  obtain ⟨h2, h3⟩ := lin_inj2 hK hb hb' h1
  exact ⟨h2, h3, hc2⟩

/-! ### The shape of an encoding -/

/-- The data an encoding needs about a protocol and its bounds.  Everything is a plain
Nat or List so that index arithmetic stays simple and the allocation is computable.
The "1" fields are maxima, so every stride below is a successor and therefore strictly
positive - which is what makes the positional codes injective without extra hypotheses. -/
structure Shape where
  /-- One less than the number of sessions. -/
  nS1 : Nat
  /-- The largest program counter over all sessions (a role's length). -/
  nPc1 : Nat
  /-- The largest store variable index over all sessions. -/
  nV1 : Nat
  /-- The universe of messages. -/
  U : List Term
  /-- The nonce domain. -/
  D : List NonceName
  /-- The step bound L. -/
  steps : Nat

/-- Stride: number of sessions. -/
def shS (sh : Shape) : Nat := sh.nS1 + 1
/-- Stride: number of program-counter values. -/
def shPc (sh : Shape) : Nat := sh.nPc1 + 1
/-- Stride: number of store-variable slots. -/
def shV (sh : Shape) : Nat := sh.nV1 + 1
/-- Stride: number of values (unset plus the universe). -/
def shVal (sh : Shape) : Nat := sh.U.length + 1
/-- Stride: number of nonce choices (a dummy slot when the domain is empty). -/
def shD (sh : Shape) : Nat := sh.D.length + 1
/-- Stride: number of event alternatives: idle, one per session, one per universe
message. -/
def shEv (sh : Shape) : Nat := 1 + shS sh + sh.U.length

/-- Every stride is strictly positive: the fact the positional codes need. -/
theorem shS_pos (sh : Shape) : 0 < shS sh := Nat.succ_pos _
theorem shPc_pos (sh : Shape) : 0 < shPc sh := Nat.succ_pos _
theorem shV_pos (sh : Shape) : 0 < shV sh := Nat.succ_pos _
theorem shVal_pos (sh : Shape) : 0 < shVal sh := Nat.succ_pos _
theorem shD_pos (sh : Shape) : 0 < shD sh := Nat.succ_pos _
theorem shEv_pos (sh : Shape) : 0 < shEv sh := by
  simp only [shEv]
  omega

/-- The maximum of a list of naturals, with a lower bound. -/
def maxNat : List Nat -> Nat -> Nat
  | [], lo => lo
  | x :: xs, lo => max x (maxNat xs lo)

theorem le_maxNat (l : List Nat) (lo : Nat) : lo ≤ maxNat l lo := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- The shape of a protocol under the given bounds. -/
def shapeOf (P : Protocol) (B : Bounds) : Shape :=
  { nS1 := P.sessions.length,
    nPc1 := maxNat ((List.range P.sessions.length).map fun q => P.roleLen q) 0,
    nV1 := maxNat ((List.range P.sessions.length).map fun q =>
                     maxNat (P.sessionVars q) 0) 0,
    U := Bounded.univ P B,
    D := P.nonceDomain,
    steps := B.steps }

/-- Session indices, program counters and variable indices are within their strides. -/
theorem q_lt_shS (sh : Shape) (q : Nat) (h : q ≤ sh.nS1) : q < shS sh := by
  simp [shS]; omega
theorem c_lt_shPc (sh : Shape) (c : Nat) (h : c ≤ sh.nPc1) : c < shPc sh := by
  simp [shPc]; omega
theorem x_lt_shV (sh : Shape) (x : Nat) (h : x ≤ sh.nV1) : x < shV sh := by
  simp [shV]; omega

/-! ### Group sizes and bases -/

/-- Size of each group. -/
def szPc (sh : Shape) : Nat := (sh.steps + 1) * shS sh * shPc sh
def szSt (sh : Shape) : Nat := (sh.steps + 1) * shS sh * shV sh * shVal sh
def szKn (sh : Shape) : Nat := (sh.steps + 1) * shVal sh
def szEv (sh : Shape) : Nat := (sh.steps + 1) * shEv sh
def szDl (sh : Shape) : Nat := sh.steps * shS sh * shVal sh
def szFr (sh : Shape) : Nat := sh.steps * shS sh * shD sh

/-- Bases: each group occupies a disjoint block of variables. -/
def bsPc (sh : Shape) : Nat := 0
def bsSt (sh : Shape) : Nat := bsPc sh + szPc sh
def bsKn (sh : Shape) : Nat := bsSt sh + szSt sh
def bsEv (sh : Shape) : Nat := bsKn sh + szKn sh
def bsDl (sh : Shape) : Nat := bsEv sh + szEv sh
def bsFr (sh : Shape) : Nat := bsDl sh + szDl sh
def bsTotal (sh : Shape) : Nat := bsFr sh + szFr sh

/-! ### Index functions -/

/-- The variable saying "session q's program counter at step i is c". -/
def vpc (sh : Shape) (i q c : Nat) : Nat :=
  bsPc sh + ((i * shS sh + q) * shPc sh + c)

/-- The variable saying "session q's variable x holds value number u at step i". -/
def vst (sh : Shape) (i q x u : Nat) : Nat :=
  bsSt sh + (((i * shS sh + q) * shV sh + x) * shVal sh + u)

/-- The variable saying "the attacker knows value number u at step i". -/
def vkn (sh : Shape) (i u : Nat) : Nat :=
  bsKn sh + (i * shVal sh + u)

/-- The variable saying "the event at step i is alternative k". -/
def vev (sh : Shape) (i k : Nat) : Nat :=
  bsEv sh + (i * shEv sh + k)

/-- The variable saying "the message delivered to session q at step i is value u". -/
def vdl (sh : Shape) (i q u : Nat) : Nat :=
  bsDl sh + ((i * shS sh + q) * shVal sh + u)

/-- The variable saying "session q picks nonce number d at step i". -/
def vfr (sh : Shape) (i q d : Nat) : Nat :=
  bsFr sh + ((i * shS sh + q) * shD sh + d)

/-- The total number of variables used by the shape. -/
def nVars (sh : Shape) : Nat := bsTotal sh

/-- Each index function is injective in its value coordinate.  These four lemmas are
what makes the one-hot groups well defined. -/
theorem vpc_inj {sh : Shape} {i q c c' : Nat} (hc : c < shPc sh) (hc' : c' < shPc sh)
    (h : vpc sh i q c = vpc sh i q c') : c = c' := by
  unfold vpc bsPc at h
  exact (lin_inj2 (shPc_pos sh) hc hc' (Nat.add_left_cancel h)).2

theorem vst_inj {sh : Shape} {i q x u u' : Nat} (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vst sh i q x u = vst sh i q x u') : u = u' := by
  unfold vst bsSt at h
  exact (lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)).2

theorem vev_inj {sh : Shape} {i k k' : Nat} (hk : k < shEv sh) (hk' : k' < shEv sh)
    (h : vev sh i k = vev sh i k') : k = k' := by
  unfold vev bsEv at h
  exact (lin_inj2 (shEv_pos sh) hk hk' (Nat.add_left_cancel h)).2

theorem vdl_inj {sh : Shape} {i q u u' : Nat} (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vdl sh i q u = vdl sh i q u') : u = u' := by
  unfold vdl bsDl at h
  exact (lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)).2

theorem vfr_inj {sh : Shape} {i q d d' : Nat} (hd : d < shD sh) (hd' : d' < shD sh)
    (h : vfr sh i q d = vfr sh i q d') : d = d' := by
  unfold vfr bsFr at h
  exact (lin_inj2 (shD_pos sh) hd hd' (Nat.add_left_cancel h)).2

/-! ### The one-hot groups -/

/-- Build the one-hot group of a positional code: the domain is the range of the
stride, and the variable map is injective because the positional code is. -/
def ohOf (f : Nat -> Nat) (K : Nat) (hK : 0 < K)
    (f_inj : ∀ x y, x < K -> y < K -> f x = f y -> x = y) : Oh Nat :=
  { vals := List.range K,
    varOf := f,
    varInj := fun x hx y hy h => f_inj x y (List.mem_range.mp hx) (List.mem_range.mp hy) h,
    nonempty := by
      intro h
      have hlen := congrArg List.length h
      simp only [List.length_nil] at hlen
      have h2 : (List.range K).length = K := List.length_range
      omega }

/-- The program-counter group of session q at step i. -/
def pcOh (sh : Shape) (i q : Nat) : Oh Nat :=
  ohOf (fun c => vpc sh i q c) (shPc sh) (shPc_pos sh) (fun x y hx hy h => vpc_inj hx hy h)

/-- The store group of session q's variable x at step i. -/
def stOh (sh : Shape) (i q x : Nat) : Oh Nat :=
  ohOf (fun u => vst sh i q x u) (shVal sh) (shVal_pos sh)
    (fun a b ha hb h => vst_inj ha hb h)

/-- The event group at step i: idle, one alternative per session, one per universe
message (the attacker's deduction choice). -/
def evOh (sh : Shape) (i : Nat) : Oh Nat :=
  ohOf (fun k => vev sh i k) (shEv sh) (shEv_pos sh) (fun x y hx hy h => vev_inj hx hy h)

/-- The delivered-message group at step i for session q. -/
def dlOh (sh : Shape) (i q : Nat) : Oh Nat :=
  ohOf (fun u => vdl sh i q u) (shVal sh) (shVal_pos sh) (fun x y hx hy h => vdl_inj hx hy h)

/-- The fresh-nonce group at step i for session q. -/
def frOh (sh : Shape) (i q : Nat) : Oh Nat :=
  ohOf (fun d => vfr sh i q d) (shD sh) (shD_pos sh) (fun x y hx hy h => vfr_inj hx hy h)

/-! ### Values -/

/-- Reading past the end of a list gives none. -/
theorem rget_oob : ∀ (l : List α), rget l l.length = none := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => exact ih

/-- Any index beyond the length reads as none. -/
theorem rget_oob_ge : ∀ (l : List α) (i : Nat), i ≥ l.length -> rget l i = none := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons x xs ih =>
      intro i hi
      cases i with
      | zero =>
          have : 0 < List.length (x :: xs) := by simp
          omega
      | succ i =>
          show rget xs i = none
          exact ih i (by simp [List.length_cons] at hi; omega)

/-- Reading the head of a list at index 0. -/
theorem rget_zero {α : Type} (x : α) (xs : List α) : rget (x :: xs) 0 = some x := rfl

/-- Reading past the head shifts the index. -/
theorem rget_succ {α : Type} (x : α) (xs : List α) (n : Nat) :
    rget (x :: xs) (n + 1) = rget xs n := rfl

/-- The index of the first occurrence of a in l, or 0 when a is absent.  Written by hand
rather than with List.idxOf so that its unfolding is available to the proofs below. -/
def pos [BEq α] (a : α) : List α -> Nat
  | [] => 0
  | x :: xs => if x == a then 0 else pos a xs + 1

/-- The first occurrence of an element reads back as that element. -/
theorem rget_pos [BEq α] [LawfulBEq α] : ∀ (l : List α) (a : α),
    a ∈ l -> rget l (pos a l) = some a := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons x xs ih =>
      intro a h
      by_cases hx : x == a
      · rw [pos, if_pos hx]
        exact LawfulBEq.eq_of_beq hx ▸ rget_zero x xs
      · rw [pos, if_neg hx, rget_succ]
        rw [List.mem_cons] at h
        rcases h with rfl | h'
        · exact absurd (by simp) hx
        · exact ih a h'

/-- The value with number u: the u-th message of the universe, or unset when u is out of
range (the last index is reserved for "unset"). -/
def valAt (sh : Shape) (u : Nat) : Val := rget sh.U u

/-- The number of a value: a universe message uses its first position, unset is last. -/
def uIdx (sh : Shape) : Val -> Nat
  | none => sh.U.length
  | some t => pos t sh.U

/-- valAt of the unset index is unset. -/
@[simp] theorem valAt_uIdx_none (sh : Shape) : valAt sh (uIdx sh none) = none :=
  rget_oob sh.U

/-- valAt inverts uIdx on universe messages. -/
theorem valAt_uIdx_some (sh : Shape) {t : Term} (ht : t ∈ sh.U) :
    valAt sh (uIdx sh (some t)) = some t :=
  rget_pos sh.U t ht

/-- The index of a value is within the stride. -/
theorem uIdx_lt (sh : Shape) (v : Val) (hv : v ∈ sh.U.map some ++ [none]) :
    uIdx sh v < shVal sh := by
  cases v with
  | none => simp [uIdx, shVal]
  | some t =>
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at hv
      rcases hv with h | h
      · obtain ⟨u, hu, hut⟩ := h
        have hut' : u = t := Option.some.inj hut
        have h1 : rget sh.U (pos t sh.U) = some t :=
          hut' ▸ rget_pos sh.U u hu
        have hlt : pos t sh.U < sh.U.length := by
          by_contra e
          have h2 : rget sh.U (pos t sh.U) = none := rget_oob_ge sh.U _ (by omega)
          rw [h2] at h1; simp at h1
        simp only [uIdx]
        have : shVal sh = sh.U.length + 1 := rfl
        omega
      · exact absurd h (by simp)

/-! ### Decoding a configuration from an assignment -/

/-- The store of session q at step i, read off the one-hot groups. -/
def decodeStore (sh : Shape) (a : Assignment) (i q : Nat) : List (Var × Term) :=
  (List.range sh.nV1).filterMap fun x =>
    match stOh sh i q x |>.decode a with
    | some u => match valAt sh u with
        | some t => some (x, t)
        | none => none
    | none => none

/-- The attacker's knowledge at step i. -/
def decodeKn (sh : Shape) (a : Assignment) (i : Nat) : List Term :=
  (List.range sh.U.length).filterMap fun u =>
    if a (vkn sh i u) then some (rget sh.U u |>.getD (Term.nonce 0)) else none

/-- The program counter of session q at step i. -/
def decodePc (sh : Shape) (a : Assignment) (i q : Nat) : Nat :=
  (pcOh sh i q).decode a |>.getD 0

/-- The configuration decoded from an assignment at step i. -/
def decodeCfg (sh : Shape) (a : Assignment) (i : Nat) : Cfg :=
  { sess := (List.range sh.nS1).map fun q =>
      { pc := decodePc sh a i q, store := decodeStore sh a i q },
    kn := decodeKn sh a i }

end ProtSat.Encode
