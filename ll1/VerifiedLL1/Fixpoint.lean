/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Grammar

/-!
# Phase 4.0 — Finite monotone fixed points

`NULLABLE`, `FIRST` and `FOLLOW` are all least fixed points of monotone rules over a
*finite* carrier (the nonterminals; symbols; nonterminal/lookahead pairs).  This
module provides the one generic construction and the one generic termination argument
that the three analyses share, so each of them only has to prove that its own rule set
is monotone, and that its rules are sound and complete with respect to a
*derivation-level* specification stated in Phase 1.

## Representation

A finite set is a list `carrier` enumerating the universe, together with a boolean
predicate; the set itself is `carrier.filter p`.  Everything stays executable:
membership is `p x`, union is `fun x => p x || q x`, and the iteration is structural
recursion on a natural number.  The carrier is required to be duplicate-free and
*exhaustive* (`FiniteEnum` supplies exactly that), which is what turns "the two
approximants agree on the carrier" into "the two approximants are equal", the form
needed to propagate stability forward.

## Termination

`iterP P n` applies the monotone transformer `P` to the empty predicate `n` times.
Approximants increase (`iterP_increasing`); a strict increase between step `i` and
step `i+1` makes the filtered set strictly larger (`length_filter_lt_of_new`); the
filtered set is always a sublist of the carrier, so there can be at most
`carrier.length` strict increases.  Hence the iteration is stable at stage
`carrier.length` (`iterP_stable`): applying `P` to the limit does not add anything,
which is the closure property each analysis consumes.
-/

set_option linter.unusedSectionVars false

universe w

namespace VerifiedLL1.Fixpoint

variable {α : Type w} [BEq α]

/-- Boolean conjunction as a membership fact. -/
theorem and_eq_true_iff {a b : Bool} :
    ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

/-- `PMono P`: `P` is monotone in the pointwise order on predicates. -/
def PMono (P : (α → Bool) → α → Bool) : Prop :=
  ∀ (f g : α → Bool), (∀ x, f x = true → g x = true) → ∀ x, P f x = true → P g x = true

/-- The `n`-th approximant of a monotone transformer, starting from the empty set. -/
def iterP (P : (α → Bool) → α → Bool) : Nat → α → Bool
  | 0 => fun _ => false
  | n + 1 => P (iterP P n)

@[simp] theorem iterP_zero (P : (α → Bool) → α → Bool) (x : α) : iterP P 0 x = false := rfl

theorem iterP_succ (P : (α → Bool) → α → Bool) (n : Nat) (x : α) :
    iterP P (n + 1) x = P (iterP P n) x := rfl

/-- Monotonicity makes the approximants increase. -/
theorem iterP_increasing (P : (α → Bool) → α → Bool) (hmono : PMono P) :
    ∀ (n : Nat) (x : α), iterP P n x = true → iterP P (n + 1) x = true := by
  intro n
  induction n with
  | zero => intro x h; exact absurd h (by simp)
  | succ n ih =>
      intro x h
      have h' : P (iterP P n) x = true := h
      exact hmono (iterP P n) (iterP P (n + 1)) (fun y hy => ih y hy) x h'

/-- Every approximant is below a later one. -/
theorem iterP_le_limit (P : (α → Bool) → α → Bool) (hmono : PMono P) :
    ∀ (x : α) (k n : Nat), k ≤ n → iterP P k x = true → iterP P n x = true := by
  intro x k n
  induction n with
  | zero =>
      intro hle h
      have : k = 0 := Nat.le_zero.mp hle
      subst this; exact h
  | succ n ih =>
      intro hle h
      by_cases hkn : k = n + 1
      · subst hkn; exact h
      · exact iterP_increasing P hmono n x (ih (by omega) h)

section Filter

variable {β : Type w} [BEq β]

theorem length_filter_le (l : List β) (p : β → Bool) : (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a = true
      · rw [List.filter_cons_of_pos h]
        simp; omega
      · rw [List.filter_cons_of_neg h]
        have := ih
        simp; omega

theorem length_filter_le_of_le {l : List β} (p q : β → Bool)
    (hpq : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases hpa : p a = true
      · have hqa : q a = true := hpq a (List.Mem.head _) hpa
        rw [List.filter_cons_of_pos hpa, List.filter_cons_of_pos hqa]
        have := ih (fun x hx => hpq x (List.Mem.tail _ hx))
        simp at this ⊢; omega
      · rw [List.filter_cons_of_neg hpa]
        have := ih (fun x hx => hpq x (List.Mem.tail _ hx))
        by_cases hqa : q a = true
        · rw [List.filter_cons_of_pos hqa]
          simp at this ⊢; omega
        · rw [List.filter_cons_of_neg hqa]; exact this

theorem length_filter_lt_of_new {l : List β} (p q : β → Bool)
    (hpq : ∀ x ∈ l, p x = true → q x = true)
    (hnew : ∃ x ∈ l, q x = true ∧ p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => exact absurd hnew (by simp)
  | cons a as ih =>
      obtain ⟨x, hx, hqx, hpx⟩ := hnew
      by_cases hpa : p a = true
      · have hqa : q a = true := hpq a (List.Mem.head _) hpa
        rw [List.filter_cons_of_pos hpa, List.filter_cons_of_pos hqa]
        rw [List.mem_cons] at hx
        rcases hx with h | h
        · subst h
          rw [hpa] at hpx
          exact absurd hpx (by decide)
        · have := ih (fun y hy => hpq y (List.Mem.tail _ hy)) ⟨x, h, hqx, hpx⟩
          simp at this ⊢; omega
      · rw [List.filter_cons_of_neg hpa]
        by_cases hqa : q a = true
        · rw [List.filter_cons_of_pos hqa]
          have hle := length_filter_le_of_le (l := as) p q
            (fun y hy => hpq y (List.Mem.tail _ hy))
          simp at hle ⊢; omega
        · rw [List.filter_cons_of_neg hqa]
          rw [List.mem_cons] at hx
          rcases hx with h | h
          · subst h
            exact absurd hqx hqa
          · exact ih (fun y hy => hpq y (List.Mem.tail _ hy)) ⟨x, h, hqx, hpx⟩

end Filter

/-- Does the step from `i` to `i+1` add a new carrier element? -/
def growsAt (carrier : List α) (P : (α → Bool) → α → Bool) (i : Nat) : Bool :=
  carrier.any fun x => iterP P (i + 1) x && !iterP P i x

theorem growsAt_true {carrier : List α} {P : (α → Bool) → α → Bool} {i : Nat}
    (h : growsAt carrier P i = true) :
    ∃ x ∈ carrier, iterP P (i + 1) x = true ∧ iterP P i x = false := by
  obtain ⟨x, hx, hxy⟩ := (List.any_eq_true.mp h)
  obtain ⟨h1, h2⟩ := and_eq_true_iff.mp hxy
  refine ⟨x, hx, h1, ?_⟩
  cases h : iterP P i x with
  | true => rw [h] at h2; exact absurd h2 (by decide)
  | false => rfl

theorem growsAt_false {carrier : List α} {P : (α → Bool) → α → Bool} {i : Nat}
    (h : growsAt carrier P i = false) (hmono : PMono P) :
    ∀ x ∈ carrier, iterP P (i + 1) x = iterP P i x := by
  intro x hx
  by_cases hi : iterP P i x = true
  · have h1 : iterP P (i + 1) x = true := iterP_increasing P hmono i x hi
    rw [h1, hi]
  · by_cases h2 : iterP P (i + 1) x = true
    · exfalso
      have hno := (List.any_eq_false.mp h) x hx
      refine hno ?_
      rw [h2]
      simp [hi]
    · have e1 : iterP P (i + 1) x = false := by
        cases h : iterP P (i + 1) x with
        | true => exact absurd h h2
        | false => rfl
      have e2 : iterP P i x = false := by
        cases h : iterP P i x with
        | true => exact absurd h hi
        | false => rfl
      rw [e1, e2]

/-- A bounded negation of a decidable predicate yields a witness. -/
theorem exists_le_of_not_forall_le (n : Nat) (p : Nat → Bool)
    (h : ¬ ∀ i, i ≤ n → p i = true) : ∃ i, i ≤ n ∧ p i = false := by
  induction n with
  | zero =>
      by_cases h0 : p 0 = false
      · exact ⟨0, by omega, h0⟩
      · exfalso
        apply h
        intro i hi
        have : i = 0 := Nat.le_zero.mp hi
        subst this
        cases h : p 0 with
        | true => rfl
        | false => exact absurd h h0
  | succ n ih =>
      by_cases h1 : p (n + 1) = false
      · exact ⟨n + 1, by omega, h1⟩
      · have hnot : ¬ ∀ i, i ≤ n → p i = true := by
          intro hall
          apply h
          intro i hi
          rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
          · exact hall i (by omega)
          · have : i = n + 1 := by omega
            subst this
            cases h : p (n + 1) with
            | true => rfl
            | false => exact absurd h h1
        obtain ⟨i, hi, hfalse⟩ := ih hnot
        exact ⟨i, by omega, hfalse⟩

/-- **Termination.**  A monotone transformer over a finite exhaustive carrier reaches a
fixed point within `carrier.length` steps. -/
theorem iterP_stable (carrier : List α) (P : (α → Bool) → α → Bool) (hmono : PMono P)
    (hall : ∀ x, x ∈ carrier) :
    ∀ x, iterP P (carrier.length + 1) x = iterP P carrier.length x := by
  have hbound : ∀ k, (carrier.filter (iterP P k)).length ≤ carrier.length := fun k =>
    length_filter_le carrier _
  have hgrow : ∀ k, k ≤ carrier.length + 1 → (∀ i, i < k → growsAt carrier P i = true) →
      (carrier.filter (iterP P k)).length ≥ k := by
    intro k
    induction k with
    | zero => intro _ _; simp
    | succ k ih =>
        intro hle hsteps
        have hlt : (carrier.filter (iterP P k)).length <
            (carrier.filter (iterP P (k + 1))).length := by
          refine length_filter_lt_of_new (l := carrier) (iterP P k) (iterP P (k + 1))
            (fun x hx htrue => iterP_increasing P hmono k x htrue)
            (growsAt_true (hsteps k (by omega)))
        have hle' : (carrier.filter (iterP P k)).length ≥ k :=
          ih (by omega) (fun i hi => hsteps i (by omega))
        omega
  have hsome : ∃ i, i ≤ carrier.length ∧ growsAt carrier P i = false := by
    refine exists_le_of_not_forall_le carrier.length (growsAt carrier P) ?_
    intro hsteps
    have h1 := hgrow (carrier.length + 1) (by omega) (fun i hi => hsteps i (by omega))
    have hb := hbound (carrier.length + 1)
    omega
  obtain ⟨i, hi, hg⟩ := hsome
  have hstep_i : ∀ y, iterP P (i + 1) y = iterP P i y := fun y =>
    growsAt_false hg hmono y (hall y)
  have hfun : ∀ j, i ≤ j → ∀ y, iterP P j y = iterP P i y := by
    intro j
    induction j with
    | zero =>
        intro hle y
        have : i = 0 := Nat.le_zero.mp hle
        subst this; rfl
    | succ j ih =>
        intro hle y
        by_cases hji : i = j + 1
        · subst hji; rfl
        · have hle' : i ≤ j := by omega
          have hij : ∀ z, iterP P j z = iterP P i z := ih hle'
          have hP : P (iterP P j) = P (iterP P i) := by rw [funext hij]
          calc iterP P (j + 1) y = P (iterP P j) y := iterP_succ ..
            _ = P (iterP P i) y := by rw [hP]
            _ = iterP P (i + 1) y := (iterP_succ ..).symm
            _ = iterP P i y := hstep_i y
  intro x
  rw [hfun (carrier.length + 1) (by omega) x, hfun carrier.length (by omega) x]

/-- The limit is closed under the transformer. -/
theorem iterP_closed (carrier : List α) (P : (α → Bool) → α → Bool) (hmono : PMono P)
    (hall : ∀ x, x ∈ carrier) (x : α) :
    iterP P carrier.length x = true ↔ P (iterP P carrier.length) x = true := by
  have h1 : iterP P (carrier.length + 1) x = iterP P carrier.length x :=
    iterP_stable carrier P hmono hall x
  have h2 : iterP P (carrier.length + 1) x = P (iterP P carrier.length) x :=
    iterP_succ ..
  rw [← h1, h2]

end Fixpoint
