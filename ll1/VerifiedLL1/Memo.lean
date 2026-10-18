/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Fixpoint

/-!
# Phase 4.0b - A memoized Boolean-list backend for the fixed-point approximants

## Why this module exists

'Fixpoint.iterP' iterates a *function*: 'iterP P n' unfolds to
'P (P (... (fun _ => false)))', so the single query 'iterP P n x' re-unfolds the whole
chain of n transformers, and every nested call 'P f y' re-unfolds 'f y' in its turn.
Under 'by decide' - kernel reduction, no compiler, no sharing - that is what makes the
FOLLOW and ll1Check decisions expensive.

This module computes *exactly the same approximants* as an explicit 'List Bool' aligned
with a carrier list, so round k+1 is one pass over a materialised list of bits rather
than a nested unfolding:

* 'lookup carrier bits x' - the bit aligned with x in carrier, 'false' if absent;
* 'tabulate' - a **strict continuation-based worker**: it matches every produced Bool
  before accumulating it, so the kernel is forced to materialise the list instead of
  leaving a lazy 'List.map' chain (a bare 'List.map' is not enough);
* 'step' - one round: 'step carrier P bits = carrier.map (P (lookup carrier bits))';
* 'loop' - a fuel-bounded forward loop from the all-false bit list that stops **exactly**
  when two consecutive bit lists are '==';
* 'iterBits carrier P n' - the final bit list; 'iterMemo carrier P n x' - its lookup.

The bridge theorems are 'iterBits_eq_map_iterP' and 'iterMemo_eq_iterP': the memoized
backend computes the n-th approximant of 'Fixpoint.iterP', bit for bit.

## No monotonicity is needed - but exhaustiveness is

'iterMemo_eq_iterP' is a statement about the *exact* n-th approximant, not about a least
fixed point, so it holds for an arbitrary transformer P, monotone or not.  The price is
the hypothesis 'hall : ∀ x, x ∈ carrier'.  It is what turns a bit list into a *total*
function: 'lookup carrier (carrier.map f) x = f x' for every x (see 'lookup_map'), hence

* equality of two tabulated bit lists lifts to pointwise equality of the two approximants
  *everywhere*, and 'eq_of_map_beq' is exactly that lift; and
* P is then applied to the *same* function in the memoized and in the unfolded iteration,
  which is the only fact the early-stop branch of 'loop_map' uses.

Without 'hall' the statement is **false**: a transformer may differ off-carrier and feed
that difference back on-carrier.  Concretely, take alpha := Bool, carrier := [true] (so
false ∉ carrier) and 'badP f x = if x then f false else true'.  Then

    iterP badP 0       = fun _ => false
    iterP badP 1 true  = iterP badP 0 false = false
    iterP badP 1 false = true                  -- off-carrier, but P reads it back
    iterP badP 2 true  = iterP badP 1 false = true

whereas 'lookup [true] bits false = false' for *every* bit list, so the memoized round
function is always 'fun _ => false', 'iterBits [true] badP n = [false]' for every n, and
'iterMemo [true] badP 2 true = false' while 'iterP badP 2 true = true'.  'MemoTest.lean'
checks this divergence with the kernel, so the failure of the bridge without 'hall' is
itself a verified fact and not a comment-only claim.

## Duplicates in the carrier are allowed

'FiniteEnum' only guarantees that 'elems' is *exhaustive*, never that it is duplicate-free.
The docstring of 'Fixpoint.lean' asserts that "the carrier is required to be
duplicate-free"; nothing in the library ever uses or establishes that, and it is *not*
needed here: the termination and closure theorems only ever consume
'hall : ∀ x, x ∈ carrier'.  Everything in this module is therefore phrased through
'idxOf'/'getD', which tolerates repetition: 'idxOf' answers with the *first* occurrence, so
a repeated carrier entry is tabulated several times with the same value and 'getD' reads
the bit at that first index.  'lookup_map', 'iterBits_eq_map_iterP' and
'iterMemo_eq_iterP' are all unaffected by duplicates, and 'MemoTest.lean' exercises a
carrier with duplicates.
-/

set_option linter.unusedSectionVars false

universe u

namespace VerifiedLL1.Memo

variable {α : Type u}

/-- Lookup of a memoized approximant: the bit aligned with x in carrier, 'false' if absent.

'List.idxOf' returns 'carrier.length' when x does not occur and 'List.getD' returns the
fallback for an out-of-range index, so absence is exactly 'false'.  If x occurs more than
once the *first* occurrence decides the bit, and every later copy of x in the carrier is
tabulated with that same value. -/
def lookup [BEq α] (carrier : List α) (bits : List Bool) (x : α) : Bool :=
  bits.getD (carrier.idxOf x) false

section Lookup

variable [BEq α] [LawfulBEq α]

theorem idxOf_cons_eq (a b : α) (l : List α) (h : (a == b) = true) :
    List.idxOf b (a :: l) = 0 := by
  rw [List.idxOf_cons]
  exact ite_eq_left h

theorem idxOf_cons_ne (a b : α) (l : List α) (h : (a == b) = false) :
    List.idxOf b (a :: l) = List.idxOf b l + 1 := by
  rw [List.idxOf_cons]
  exact ite_eq_right (by simp [h])

/-- Membership-indexed form of 'lookup_map': the induction needs the membership of the
*query* point, which the global 'hall' then supplies. -/
theorem lookup_map_of_mem (carrier : List α) (f : α → Bool) :
    ∀ x, x ∈ carrier → lookup carrier (carrier.map f) x = f x := by
  induction carrier with
  | nil => intro x h; exact absurd h (by simp)
  | cons y ys ih =>
      intro x hx
      cases hbeq : (y == x) with
      | true =>
          have hidx : List.idxOf x (y :: ys) = 0 := idxOf_cons_eq y x ys hbeq
          have hyx : y = x := eq_of_beq hbeq
          show ((f y :: ys.map f)).getD (List.idxOf x (y :: ys)) false = f x
          rw [hidx, List.getD_cons_zero]
          subst hyx
          rfl
      | false =>
          have hne : ¬ y = x := by
            intro hh
            rw [hh] at hbeq
            simp at hbeq
          have hidx : List.idxOf x (y :: ys) = List.idxOf x ys + 1 := idxOf_cons_ne y x ys hbeq
          obtain hxy | hx' := List.mem_cons.mp hx
          · exact absurd hxy (fun hy => hne hy.symm)
          · show ((f y :: ys.map f)).getD (List.idxOf x (y :: ys)) false = f x
            rw [hidx, List.getD_cons_succ]
            exact ih x hx'

/-- **An exhaustive carrier makes a bit list a total function.**  Looking up the tabulated
list recovers the tabulated function.  Duplicates in carrier are harmless: 'idxOf' always
answers with the first occurrence and 'map' writes the same value at every copy. -/
theorem lookup_map (carrier : List α) (f : α → Bool) (hall : ∀ x, x ∈ carrier) (x : α) :
    lookup carrier (carrier.map f) x = f x :=
  lookup_map_of_mem carrier f x (hall x)

/-- Two tabulated bit lists that are '==' define the same function, provided the carrier is
exhaustive.  This is the one place where 'hall' is load-bearing, and the reason no
monotonicity hypothesis is needed anywhere below. -/
theorem eq_of_map_beq (carrier : List α) (f g : α → Bool)
    (h : (carrier.map f == carrier.map g) = true) (hall : ∀ x, x ∈ carrier) (x : α) :
    f x = g x := by
  have hmap : carrier.map f = carrier.map g := eq_of_beq h
  calc f x = lookup carrier (carrier.map f) x := (lookup_map carrier f hall x).symm
    _ = lookup carrier (carrier.map g) x := by rw [hmap]
    _ = g x := lookup_map carrier g hall x

end Lookup

section Tabulate

/-- **Strict continuation-based tabulation.**  'tabulate carrier f k' applies f to every
element of carrier and hands the resulting bit list to the continuation k.

Every produced bit is matched *before* it is accumulated, so the kernel must reduce 'f x'
to a constructor to make the recursive call: the list cannot stay a chain of unevaluated
'List.map' applications.  The continuation is applied only at the end, so the bits come out
in carrier order with no reversal. -/
def tabulate (carrier : List α) (f : α → Bool) (k : List Bool → List Bool) : List Bool :=
  match carrier with
  | [] => k []
  | x :: xs =>
      match f x with
      | true => tabulate xs f (fun r => k (true :: r))
      | false => tabulate xs f (fun r => k (false :: r))

theorem tabulate_nil (f : α → Bool) (k : List Bool → List Bool) : tabulate [] f k = k [] := rfl

theorem tabulate_cons (x : α) (xs : List α) (f : α → Bool) (k : List Bool → List Bool) :
    tabulate (x :: xs) f k =
      match f x with
      | true => tabulate xs f (fun r => k (true :: r))
      | false => tabulate xs f (fun r => k (false :: r)) := rfl

/-- The accumulator invariant: the worker produces exactly the map of f.  The continuation
is quantified last so that the induction hypothesis can be instantiated at the extended
continuation. -/
theorem tabulate_map (carrier : List α) (f : α → Bool) :
    ∀ (k : List Bool → List Bool), tabulate carrier f k = k (carrier.map f) := by
  induction carrier with
  | nil => intro k; rfl
  | cons x xs ih =>
      intro k
      have key : ∀ b : Bool,
          (match b with
           | true => tabulate xs f (fun r => k (true :: r))
           | false => tabulate xs f (fun r => k (false :: r))) = k (b :: xs.map f) := by
        intro b
        cases b <;> simp only [ih]
      show tabulate (x :: xs) f k = k ((x :: xs).map f)
      rw [tabulate_cons]
      exact key (f x)

/-- One memoized round: tabulate P applied to the function the current bit list represents. -/
def step [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) (cur : List Bool) : List Bool :=
  tabulate carrier (P (lookup carrier cur)) (fun r => r)

theorem step_map [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) (cur : List Bool) :
    step carrier P cur = carrier.map (P (lookup carrier cur)) :=
  tabulate_map carrier _ _

end Tabulate

section IterFrom

/-- 'iterFrom P n f' applies the transformer P to f exactly n times.  It is the
generalisation of 'Fixpoint.iterP' with an arbitrary starting function; 'iterP P n' is
'iterFrom P n (fun _ => false)'. -/
def iterFrom (P : (α → Bool) → α → Bool) : Nat → (α → Bool) → (α → Bool)
  | 0, f => f
  | n + 1, f => P (iterFrom P n f)

theorem iterFrom_zero (P : (α → Bool) → α → Bool) (f : α → Bool) : iterFrom P 0 f = f := rfl

theorem iterFrom_succ (P : (α → Bool) → α → Bool) (n : Nat) (f : α → Bool) :
    iterFrom P (n + 1) f = P (iterFrom P n f) := rfl

theorem iterFrom_succ_right (P : (α → Bool) → α → Bool) (n : Nat) (f : α → Bool) :
    iterFrom P n (P f) = iterFrom P (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterFrom_succ, ih]; exact (iterFrom_succ ..).symm

/-- Once P fixes f, every further application of P fixes it too. -/
theorem iterFrom_fixed (P : (α → Bool) → α → Bool) (f : α → Bool) (hf : P f = f) :
    ∀ n : Nat, iterFrom P n f = f := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [iterFrom_succ, ih, hf]

/-- The starting function of 'Fixpoint.iterP' is the all-false predicate. -/
theorem iterFrom_eq_iterP (P : (α → Bool) → α → Bool) (n : Nat) :
    iterFrom P n (fun _ => false) = Fixpoint.iterP P n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterFrom_succ, ih]; rfl

end IterFrom

section Loop

/-- **The fuel-bounded forward loop.**  'loop carrier P n cur' performs at most n rounds
starting from the bit list cur, stopping *exactly* when two consecutive bit lists are '=='.
Because the carrier is exhaustive, that test is a genuine fixed-point test on the
represented function, so early stopping cannot change the answer. -/
def loop [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) : Nat → List Bool → List Bool
  | 0, cur => cur
  | n + 1, cur =>
      match step carrier P cur with
      | next => if next == cur then next else loop carrier P n next

theorem loop_zero [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) (cur : List Bool) :
    loop carrier P 0 cur = cur := rfl

theorem loop_succ [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) (n : Nat)
    (cur : List Bool) :
    loop carrier P (n + 1) cur =
      if step carrier P cur == cur then step carrier P cur
        else loop carrier P n (step carrier P cur) := rfl

/-- **Loop refinement from an arbitrary initial bit list** already of the form
'carrier.map f': n rounds tabulate 'iterFrom P n f'.  No monotonicity is used; the
early-stop branch is justified by 'eq_of_map_beq', which needs the carrier to be
exhaustive. -/
theorem loop_map [BEq α] [LawfulBEq α] (carrier : List α) (P : (α → Bool) → α → Bool)
    (hall : ∀ x, x ∈ carrier) :
    ∀ (n : Nat) (f : α → Bool),
      loop carrier P n (carrier.map f) = carrier.map (iterFrom P n f) := by
  intro n
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      have hl : lookup carrier (carrier.map f) = f := funext (lookup_map carrier f hall)
      have hstep : step carrier P (carrier.map f) = carrier.map (P f) := by rw [step_map, hl]
      rw [loop_succ, hstep]
      by_cases hbeq : (carrier.map (P f) == carrier.map f) = true
      · -- early stop: the two bit lists are '==', so P f = f everywhere and no later
        -- round can change anything
        have hf : P f = f := funext (eq_of_map_beq carrier (P f) f hbeq hall)
        rw [ite_eq_left hbeq, hf, iterFrom_fixed P f hf (n + 1)]
      · rw [ite_eq_right (fun hb => absurd hb hbeq), ih (P f), iterFrom_succ_right]

end Loop

/-- The final bit list of the memoized iteration: at most n rounds from the all-false bit
list, with exact early stopping. -/
def iterBits [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) (n : Nat) : List Bool :=
  loop carrier P n (carrier.map fun _ => false)

/-- **The memoized bit list is the tabulated approximant.** -/
theorem iterBits_eq_map_iterP [BEq α] [LawfulBEq α] (carrier : List α)
    (P : (α → Bool) → α → Bool) (hall : ∀ x, x ∈ carrier) (n : Nat) :
    iterBits carrier P n = carrier.map (Fixpoint.iterP P n) := by
  show loop carrier P n (carrier.map fun _ => false) = _
  rw [loop_map carrier P hall n, iterFrom_eq_iterP]

/-- **The memoized predicate**: the bit of the n-th approximant aligned with x. -/
def iterMemo [BEq α] (carrier : List α) (P : (α → Bool) → α → Bool) (n : Nat) (x : α) : Bool :=
  lookup carrier (iterBits carrier P n) x

/-- **The bridge.**  The memoized predicate is the n-th approximant of 'Fixpoint.iterP',
pointwise, for *every* transformer - monotone or not, and for a carrier with duplicates. -/
theorem iterMemo_eq_iterP [BEq α] [LawfulBEq α] (carrier : List α)
    (P : (α → Bool) → α → Bool) (hall : ∀ x, x ∈ carrier) (n : Nat) (x : α) :
    iterMemo carrier P n x = Fixpoint.iterP P n x := by
  show lookup carrier (iterBits carrier P n) x = Fixpoint.iterP P n x
  rw [iterBits_eq_map_iterP carrier P hall n]
  exact lookup_map carrier (Fixpoint.iterP P n) hall x

section Transfer

/-- The memoized limit is stable: one more round adds nothing.  Transferred from
'Fixpoint.iterP_stable' through the bridge. -/
theorem iterMemo_stable [BEq α] [LawfulBEq α] (carrier : List α)
    (P : (α → Bool) → α → Bool) (hmono : Fixpoint.PMono P) (hall : ∀ x, x ∈ carrier)
    (x : α) :
    iterMemo carrier P (carrier.length + 1) x = iterMemo carrier P carrier.length x := by
  rw [iterMemo_eq_iterP carrier P hall (carrier.length + 1) x,
      iterMemo_eq_iterP carrier P hall carrier.length x]
  exact Fixpoint.iterP_stable carrier P hmono hall x

/-- The memoized limit is closed under the transformer.  Transferred from
'Fixpoint.iterP_closed' through the bridge. -/
theorem iterMemo_closed [BEq α] [LawfulBEq α] (carrier : List α)
    (P : (α → Bool) → α → Bool) (hmono : Fixpoint.PMono P) (hall : ∀ x, x ∈ carrier)
    (x : α) :
    iterMemo carrier P carrier.length x = true ↔
      P (iterMemo carrier P carrier.length) x = true := by
  have hfun : iterMemo carrier P carrier.length = Fixpoint.iterP P carrier.length :=
    funext (iterMemo_eq_iterP carrier P hall carrier.length)
  have h1 : iterMemo carrier P carrier.length x = Fixpoint.iterP P carrier.length x :=
    iterMemo_eq_iterP carrier P hall carrier.length x
  have h2 : P (iterMemo carrier P carrier.length) x =
      P (Fixpoint.iterP P carrier.length) x := by rw [hfun]
  rw [h1, h2]
  exact Fixpoint.iterP_closed carrier P hmono hall x

/-- Monotone growth, transferred through the bridge. -/
theorem iterMemo_increasing [BEq α] [LawfulBEq α] (carrier : List α)
    (P : (α → Bool) → α → Bool) (hmono : Fixpoint.PMono P) (hall : ∀ x, x ∈ carrier)
    (n : Nat) (x : α) :
    iterMemo carrier P n x = true → iterMemo carrier P (n + 1) x = true := by
  rw [iterMemo_eq_iterP carrier P hall n x, iterMemo_eq_iterP carrier P hall (n + 1) x]
  exact Fixpoint.iterP_increasing P hmono n x

end Transfer

end VerifiedLL1.Memo