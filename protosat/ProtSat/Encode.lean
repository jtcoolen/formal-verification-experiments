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

For a protocol P, bounds B = (L steps, rounds of closure) and universe
U = Bounded.univ P B, the CNF encode P B is satisfiable exactly when P has a bounded
attack within those bounds.  The Boolean variables are grouped by the semantic role
they play:

    pc  i q c      session q's program counter at step i is c
    st  i q x u    session q's variable x holds value number u at step i
    kn  i u        the attacker knows the message with number u at step i
    ev  i k        the event at step i is alternative k
                   (0 = idle, 1+q = session q acts, 1+nS+u = attacker derives U[u])
    dl  i q u      the message delivered to session q at step i is U[u]
    fr  i q d      the nonce session q picks at step i is D[d]
    xe  i q e u    at step i, session q's evaluation of expression-table entry e is u

The clause groups (ProtSat.Encode.clauses) are:

* oneHotClauses    - each group above is one-hot;
* initClauses      - step 0 is the initial configuration;
* frameClauses     - a session that does not act keeps its pc and store; knowledge is
  monotone;
* stepClauses      - if session q acts while its pc is c, the successor is the one the
  operational semantics prescribes for the action at (q, c);
* evalClauses      - Tseitin definitional clauses for expression evaluation, one group
  of clauses per subexpression, so the encoding is linear in the size of the protocol
  rather than exponential in the number of variables;
* dedClauses       - a "derive" event must be justified by one instance of an attacker
  rule over the knowledge of the previous step (one clause group per rule of
  specification section 2);
* knSupportClauses - knowledge at step i+1 is either already known, or published by a
  send at step i, or the conclusion of a derive event at step i.  This is what makes the
  decoded knowledge justified rather than guessed (specification 8A);
* freshClauses     - the fresh value belongs to the nonce domain and is unused;
* violationClauses - at least one declared violation occurs.

## Why this is not trace enumeration

Specification section 5 forbids enumerating all traces and encoding a precomputed
answer.  The search space here is the product of the per-step choices (which session
acts, which message is delivered, which nonce is picked, which term the attacker
derives), and the formula only says that the sequence of states is a run of the
transition system.  The solver, not the encoder, decides which trace (if any) exists:
the encoder never evaluates the transition relation on a complete trace.

## Indexing

Variables are allocated by positional (base-expansion) codes: group g occupies the
half-open interval [base_g, base_g + size_g), and inside a group the index is a
positional code in the group's own strides.  The generic injectivity lemmas lin_inj2
and lin_inj3 do the bookkeeping once, so no group can alias another and no two distinct
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
  exact ⟨Nat.eq_of_mul_eq_mul_right hK (Nat.add_right_cancel h), rfl⟩

/-- Three-level positional code is injective below the strides. -/
theorem lin_inj3 {a b c a' b' c' K M : Nat} (hK : 0 < K) (hM : 0 < M)
    (hb : b < K) (hb' : b' < K) (hc : c < M) (hc' : c' < M)
    (h : (a * K + b) * M + c = (a' * K + b') * M + c') : a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, hc2⟩ := lin_inj2 hM hc hc' h
  obtain ⟨h2, h3⟩ := lin_inj2 hK hb hb' h1
  exact ⟨h2, h3, hc2⟩

/-! ### Small helpers -/

/-- The maximum of a list of naturals, with a lower bound. -/
def maxNat : List Nat -> Nat -> Nat
  | [], lo => lo
  | x :: xs, lo => max x (maxNat xs lo)

theorem le_maxNat (l : List Nat) (lo : Nat) : lo ≤ maxNat l lo := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- The index of the first occurrence of a in l, or 0 when a is absent.  Written by hand
rather than with List.idxOf so that its unfolding is available to the proofs below. -/
def ixOf [BEq α] (a : α) : List α -> Nat
  | [] => 0
  | x :: xs => if x == a then 0 else ixOf a xs + 1

/-- The first-occurrence index never exceeds the length: an absent element gets index 0. -/
theorem ixOf_le [BEq α] : ∀ (l : List α) (a : α), ixOf a l ≤ l.length := by
  intro l
  induction l with
  | nil => intro a; simp [ixOf]
  | cons x xs ih =>
      intro a
      have hi := ih a
      by_cases h : x == a
      · simp [ixOf, h]
      · simp only [ixOf, if_neg h, List.length_cons]
        omega

/-- Reading the head of a list at index 0. -/
theorem rget_zero {α : Type} (x : α) (xs : List α) : rget (x :: xs) 0 = some x := rfl

/-- Reading past the head shifts the index. -/
theorem rget_succ {α : Type} (x : α) (xs : List α) (n : Nat) :
    rget (x :: xs) (n + 1) = rget xs n := rfl

/-- Reading at the length of a list gives none. -/
theorem rget_len : ∀ (l : List α), rget l l.length = none := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => exact ih

/-- Any index at or beyond the length reads as none. -/
theorem rget_oob_ge : ∀ (l : List α) (i : Nat), i ≥ l.length -> rget l i = none := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons x xs ih =>
      intro i hi
      cases i with
      | zero =>
          have h : 0 < List.length (x :: xs) := by simp
          omega
      | succ i =>
          show rget xs i = none
          exact ih i (by simp [List.length_cons] at hi; omega)

/-- An in-range read succeeds. -/
theorem rget_lt {α : Type} : ∀ (l : List α) (i : Nat), i < l.length -> ∃ x, rget l i = some x := by
  intro l
  induction l with
  | nil => intro i h; exact absurd h (Nat.not_lt_zero i)
  | cons x xs ih =>
      intro i hi
      cases i with
      | zero => exact ⟨x, rfl⟩
      | succ i => exact ih i (by simpa [List.length_cons] using hi)

/-- An in-range read returns an element of the list. -/
theorem rget_mem {α : Type} : ∀ (l : List α) (i : Nat) (x : α), i < l.length ->
    rget l i = some x -> x ∈ l := by
  intro l
  induction l with
  | nil => intro i x _ h; cases h
  | cons y ys ih =>
      intro i x hi h
      cases i with
      | zero => cases h; exact List.Mem.head _
      | succ i => exact List.Mem.tail _ (ih i x (by simpa [List.length_cons] using hi) h)

/-- Whatever an in-bounds or out-of-bounds read returns is an element of the list. -/
theorem rget_some_mem {α : Type} : ∀ (l : List α) (i : Nat) (x : α),
    rget l i = some x -> x ∈ l := by
  intro l
  induction l with
  | nil => intro i x h; cases h
  | cons y ys ih =>
      intro i x h
      cases i with
      | zero =>
          cases h
          exact List.Mem.head _
      | succ i => exact List.Mem.tail _ (ih i x h)

/-- The first occurrence of an element reads back as that element. -/
theorem rget_ixOf [BEq α] [LawfulBEq α] : ∀ (l : List α) (a : α),
    a ∈ l -> rget l (ixOf a l) = some a := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons x xs ih =>
      intro a h
      by_cases hx : x == a
      · rw [ixOf, if_pos hx]
        exact LawfulBEq.eq_of_beq hx ▸ rget_zero x xs
      · rw [ixOf, if_neg hx, rget_succ]
        rw [List.mem_cons] at h
        rcases h with rfl | h'
        · exact absurd (by simp) hx
        · exact ih a h'

/-! ### The expression table -/

/-- All subexpressions occurring in any action of any role, deduplicated.  Every
subexpression of a member of this list is again a member, which is what makes the
Tseitin clauses below close. -/
def allExprs (P : Protocol) : List Expr :=
  (P.roles.flatMap fun r => r.acts.flatMap Action.exprs).eraseDups

/-- The index of an expression in the expression table. -/
def eIdx (P : Protocol) (e : Expr) : Nat := ixOf e (allExprs P)

/-- The expression at a given table index. -/
def eAt (P : Protocol) (k : Nat) : Expr := (rget (allExprs P) k).getD (Expr.agent 0)

/-! ### The shape of an encoding -/

/-- The data an encoding needs about a protocol and its bounds.  The "1" fields are
maxima, so every stride below is a successor and therefore strictly positive - which is
what makes the positional codes injective without extra hypotheses. -/
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
  /-- The number of distinct subexpressions over all roles. -/
  nE1 : Nat

/-! ### Deduction instances -/

/-- One instance of one of the attacker rules of specification section 2, expressed over the
finite universe: the number of its conclusion, and the numbers of the universe messages it
requires the attacker to already know.  The SAT encoding gives one event alternative to each
instance, which is what turns the eleven deduction rules into propositional clauses without
any exponential case split. -/
structure DedInst where
  /-- The index of the conclusion in the universe. -/
  concl : Nat
  /-- The indices of the premises in the universe. -/
  prem : List Nat
  deriving Repr, DecidableEq

/-- The index of a message in the universe, if it is there at all. -/
def tIx (sh : Shape) (t : Term) : Option Nat :=
  if t ∈ sh.U then some (ixOf t sh.U) else none

/-- The rule instances whose conclusion is the universe message with number u.  At most a
constant number per message, so the whole list is linear in the size of the universe. -/
def dedInstsOf (sh : Shape) (u : Nat) : List DedInst :=
  match rget sh.U u with
  | none => []
  | some t =>
      { concl := u, prem := [u] } ::
      (match t with
       | Term.agent _ => [{ concl := u, prem := [] }]
       | Term.key (Key.pub _) => [{ concl := u, prem := [] }]
       | Term.pair x y =>
           match tIx sh x, tIx sh y with
           | some a, some b => [{ concl := u, prem := [a, b] }]
           | _, _ => []
       | Term.encS m k =>
           match tIx sh m, tIx sh (Term.key k) with
           | some a, some b => [{ concl := u, prem := [a, b] }]
           | _, _ => []
       | Term.encA m _ =>
           match tIx sh m with
           | some a => [{ concl := u, prem := [a] }]
           | none => []
       | Term.hash m =>
           match tIx sh m with
           | some a => [{ concl := u, prem := [a] }]
           | none => []
       | _ => [])
      ++ (sh.U.filterMap fun p =>
          match p with
          | Term.pair x y =>
              if x == t then some { concl := u, prem := [ixOf p sh.U] }
              else if y == t then some { concl := u, prem := [ixOf p sh.U] }
              else none
          | Term.encS m k =>
              if m == t then
                match tIx sh (Term.key k) with
                | some b => some { concl := u, prem := [ixOf p sh.U, b] }
                | none => none
              else none
          | Term.encA m a =>
              if m == t then
                match tIx sh (Term.key (Key.priv a)) with
                | some b => some { concl := u, prem := [ixOf p sh.U, b] }
                | none => none
              else none
          | _ => none)

/-- Every rule instance supported by the universe. -/
def dedInsts (sh : Shape) : List DedInst :=
  (List.range sh.U.length).flatMap (dedInstsOf sh)

/-- The number of deduction instances. -/
def nInst (sh : Shape) : Nat := (dedInsts sh).length

/-- The deduction instance with a given number, if the number is in range. -/
def instAt (sh : Shape) (n : Nat) : Option DedInst := rget (dedInsts sh) n

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
/-- Stride: number of expression-table entries (a dummy slot when there are none). -/
def shE (sh : Shape) : Nat := sh.nE1 + 1
/-- Stride: number of event alternatives: idle, one per session, one per deduction
instance. -/
def shEv (sh : Shape) : Nat := 1 + shS sh + nInst sh

/-- Every stride is strictly positive: the fact the positional codes need. -/
theorem shS_pos (sh : Shape) : 0 < shS sh := Nat.succ_pos _
theorem shPc_pos (sh : Shape) : 0 < shPc sh := Nat.succ_pos _
theorem shV_pos (sh : Shape) : 0 < shV sh := Nat.succ_pos _
theorem shVal_pos (sh : Shape) : 0 < shVal sh := Nat.succ_pos _
theorem shD_pos (sh : Shape) : 0 < shD sh := Nat.succ_pos _
theorem shE_pos (sh : Shape) : 0 < shE sh := Nat.succ_pos _
theorem shEv_pos (sh : Shape) : 0 < shEv sh := by
  simp only [shEv]
  omega

/-- The shape of a protocol under the given bounds. -/
def shapeOf (P : Protocol) (B : Bounds) : Shape :=
  { nS1 := P.sessions.length,
    nPc1 := maxNat ((List.range P.sessions.length).map fun q => P.roleLen q) 0,
    nV1 := maxNat ((P.roles.flatMap fun r =>
                     (r.acts.flatMap fun a => a.written ++ a.exprs.flatMap Expr.vars))) 0,
    U := Bounded.univ P B,
    D := P.nonceDomain,
    steps := B.steps,
    nE1 := (allExprs P).length }

/-! ### Group sizes and bases -/

/-- Size of each group. -/
def szPc (sh : Shape) : Nat := (sh.steps + 1) * shS sh * shPc sh
def szSt (sh : Shape) : Nat := (sh.steps + 1) * shS sh * shV sh * shVal sh
def szKn (sh : Shape) : Nat := (sh.steps + 1) * shVal sh
def szEv (sh : Shape) : Nat := (sh.steps + 1) * shEv sh
def szDl (sh : Shape) : Nat := sh.steps * shS sh * shVal sh
def szFr (sh : Shape) : Nat := sh.steps * shS sh * shD sh
def szXe (sh : Shape) : Nat := (sh.steps + 1) * shS sh * shE sh * shVal sh

/-- Bases: each group occupies a disjoint block of variables. -/
def bsPc (sh : Shape) : Nat := 0
def bsSt (sh : Shape) : Nat := bsPc sh + szPc sh
def bsKn (sh : Shape) : Nat := bsSt sh + szSt sh
def bsEv (sh : Shape) : Nat := bsKn sh + szKn sh
def bsDl (sh : Shape) : Nat := bsEv sh + szEv sh
def bsFr (sh : Shape) : Nat := bsDl sh + szDl sh
def bsXe (sh : Shape) : Nat := bsFr sh + szFr sh
def bsTotal (sh : Shape) : Nat := bsXe sh + szXe sh

/-- The total number of variables used by the shape. -/
def nVars (sh : Shape) : Nat := bsTotal sh

/-! ### Index functions -/

/-- "Session q's program counter at step i is c". -/
def vpc (sh : Shape) (i q c : Nat) : Nat :=
  bsPc sh + ((i * shS sh + q) * shPc sh + c)

/-- "Session q's variable x holds value number u at step i". -/
def vst (sh : Shape) (i q x u : Nat) : Nat :=
  bsSt sh + (((i * shS sh + q) * shV sh + x) * shVal sh + u)

/-- "The attacker knows value number u at step i". -/
def vkn (sh : Shape) (i u : Nat) : Nat :=
  bsKn sh + (i * shVal sh + u)

/-- "The event at step i is alternative k". -/
def vev (sh : Shape) (i k : Nat) : Nat :=
  bsEv sh + (i * shEv sh + k)

/-- "The message delivered to session q at step i is value u". -/
def vdl (sh : Shape) (i q u : Nat) : Nat :=
  bsDl sh + ((i * shS sh + q) * shVal sh + u)

/-- "Session q picks nonce number d at step i". -/
def vfr (sh : Shape) (i q d : Nat) : Nat :=
  bsFr sh + ((i * shS sh + q) * shD sh + d)

/-- "At step i, session q's evaluation of expression-table entry e has value number u". -/
def vxe (sh : Shape) (i q e u : Nat) : Nat :=
  bsXe sh + ((((i * shS sh + q) * shE sh + e) * shVal sh) + u)

/-! ### Injectivity of the index functions -/

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

theorem vxe_inj {sh : Shape} {i q e u u' : Nat} (hu : u < shVal sh) (hu' : u' < shVal sh)
    (h : vxe sh i q e u = vxe sh i q e u') : u = u' := by
  unfold vxe bsXe at h
  exact (lin_inj2 (shVal_pos sh) hu hu' (Nat.add_left_cancel h)).2

/-! ### The one-hot groups -/

/-- Build the one-hot group of a positional code: the domain is the range of the stride,
and the variable map is injective because the positional code is. -/
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

/-- The evaluation group at step i, session q, table entry e. -/
def xeOh (sh : Shape) (i q e : Nat) : Oh Nat :=
  ohOf (fun u => vxe sh i q e u) (shVal sh) (shVal_pos sh)
    (fun a b ha hb h => vxe_inj ha hb h)

/-! ### Values -/

/-- The value with number u: the u-th message of the universe, or unset when u is out of
range (the last index is reserved for "unset"). -/
def valAt (sh : Shape) (u : Nat) : Val := rget sh.U u

/-- The number of a value: a universe message uses its first position, unset is last. -/
def uIdx (sh : Shape) : Val -> Nat
  | none => sh.U.length
  | some t => ixOf t sh.U

/-- valAt of the unset index is unset. -/
@[simp] theorem valAt_uIdx_none (sh : Shape) : valAt sh (uIdx sh none) = none :=
  rget_len sh.U

/-- valAt inverts uIdx on universe messages. -/
theorem valAt_uIdx_some (sh : Shape) {t : Term} (ht : t ∈ sh.U) :
    valAt sh (uIdx sh (some t)) = some t :=
  rget_ixOf sh.U t ht

/-- tIx reads back through valAt. -/
theorem tIx_valAt {sh : Shape} {t : Term} {n : Nat} (h : tIx sh t = some n) :
    valAt sh n = some t := by
  unfold tIx at h
  by_cases hm : t ∈ sh.U
  · rw [if_pos hm] at h
    cases h
    exact rget_ixOf sh.U t hm
  · rw [if_neg hm] at h
    exact absurd h (by simp)

/-- The index recorded by tIx is within the universe. -/
theorem tIx_lt {sh : Shape} {t : Term} {n : Nat} (h : tIx sh t = some n) :
    n < sh.U.length := by
  unfold tIx at h
  by_cases hm : t ∈ sh.U
  · rw [if_pos hm] at h
    cases h
    by_contra e
    have h2 : rget sh.U (ixOf t sh.U) = none := rget_oob_ge sh.U _ (by omega)
    have h3 : rget sh.U (ixOf t sh.U) = some t := rget_ixOf sh.U t hm
    rw [h3] at h2; simp at h2
  · rw [if_neg hm] at h
    exact absurd h (by simp)

/-- The index of a value is always within the stride: pos returns 0 for a message that is
absent, so even a value outside the universe gets a legal (if meaningless) index. -/
theorem uIdx_lt' (sh : Shape) (v : Val) : uIdx sh v < shVal sh := by
  cases v with
  | none => simp [uIdx, shVal]
  | some t =>
      have hle : ∀ (l : List Term) (a : Term), ixOf a l ≤ l.length := by
        intro l
        induction l with
        | nil => intro a; simp [ixOf]
        | cons x xs ih =>
            intro a
            have hi := ih a
            by_cases hxa : x == a
            · simp [ixOf, hxa]
            · simp only [ixOf, if_neg hxa, List.length_cons]
              omega
      have h1 := hle sh.U t
      show ixOf t sh.U < sh.U.length + 1
      omega

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
        have h1 : rget sh.U (ixOf t sh.U) = some t := hut' ▸ rget_ixOf sh.U u hu
        have hlt : ixOf t sh.U < sh.U.length := by
          by_contra e
          have h2 : rget sh.U (ixOf t sh.U) = none := rget_oob_ge sh.U _ (by omega)
          rw [h2] at h1; simp at h1
        simp only [uIdx]
        have : shVal sh = sh.U.length + 1 := rfl
        omega
      · exact absurd h (by simp)

/-! ### Event alternatives -/

/-- Event alternative codes. -/
def evIdle (sh : Shape) (i : Nat) : Nat := vev sh i 0
def evAct (sh : Shape) (i q : Nat) : Nat := vev sh i (1 + q)
def evDed (sh : Shape) (i n : Nat) : Nat := vev sh i (1 + shS sh + n)

theorem evAct_lt (sh : Shape) (i q : Nat) (hq : q < shS sh) : 1 + q < shEv sh := by
  simp [shEv]; omega
theorem evDed_lt (sh : Shape) (i n : Nat) (hn : n < nInst sh) :
    1 + shS sh + n < shEv sh := by
  simp [shEv]; omega

/-! ### Decoding a configuration from an assignment -/

/-- The pair the store group of slot x contributes to the decoded store: the slot keyed
with the value it selects, or none when the slot is unset. -/
def slotPair (sh : Shape) (a : Assignment) (i q x : Nat) : Option (Var × Term) :=
  match stOh sh i q x |>.decode a with
  | some u => (valAt sh u).map (fun t => (x, t))
  | none => none

/-- The store of session q at step i, read off the one-hot groups. -/
def decodeStore (sh : Shape) (a : Assignment) (i q : Nat) : List (Var × Term) :=
  (List.range (shV sh)).filterMap (slotPair sh a i q)

/-- The attacker's knowledge at step i. -/
def decodeKn (sh : Shape) (a : Assignment) (i : Nat) : List Term :=
  (List.range sh.U.length).filterMap fun u =>
    if a (vkn sh i u) then some ((rget sh.U u).getD (Term.nonce 0)) else none

/-- The program counter of session q at step i. -/
def decodePc (sh : Shape) (a : Assignment) (i q : Nat) : Nat :=
  (pcOh sh i q).decode a |>.getD 0

/-- The configuration decoded from an assignment at step i. -/
def decodeCfg (sh : Shape) (a : Assignment) (i : Nat) : Cfg :=
  { sess := (List.range sh.nS1).map fun q =>
      { pc := decodePc sh a i q, store := decodeStore sh a i q },
    kn := decodeKn sh a i }

end ProtSat.Encode
