/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Completeness

/-!
# Why table correctness needs a reachability hypothesis

The naive reading of "the table entry for (A, lookahead) must work for *every*
continuation" is unsatisfiable: a top-down parser only ever sees continuations that
the grammar can produce, and demanding correctness for the others forces contradictory
requirements on a single table entry.

This module proves that, for the grammar

    s -> A B
    A -> eps | a
    B -> b

which is LL(1) (its language is { b, a b }), *no* table can satisfy the
reachability-free variant `Table.CompleteStrong`.  Concretely:

* with continuation `[tok a]` the word `[a]` is derivable from `var A :: [tok a]`
  (via A => eps), so the entry for (A, a) would have to be an epsilon-producing
  right-hand side;
* with continuation `[]` the word `[a]` is derivable from `var A` via A => a, so the
  entry for (A, a) would have to be `[tok a]` itself.

One entry cannot do both.  The reachable forms of this grammar are
`[s], [A,B], [a,B], [B], [b], [a,b]` - `var A :: [tok a]` is not among them, and the
reachability hypothesis in `Table.Complete` is what discards that demand.
-/

namespace VerifiedLL1.Examples.Continuation

inductive Tok where
  | a | b
  deriving DecidableEq, Repr

inductive Var where
  | s
  | A
  | B
  deriving DecidableEq, Repr

open Tok Var Sym

/-- s -> A B;  A -> eps | a;  B -> b. -/
def R : Grammar Tok Var where
  productions := [⟨s, [var A, var B]⟩, ⟨A, []⟩, ⟨A, [tok a]⟩, ⟨B, [tok b]⟩]
  start := s

theorem mem_Ae : (A, []) ∈ R.productions := by
  simp [R, List.mem_cons]
theorem mem_Aa : (A, [tok a]) ∈ R.productions := by
  simp [R, List.mem_cons]

/-- The two demands `CompleteStrong` places on the entry for (A, a) are incompatible. -/
theorem not_complete_strong (M : Table Tok Var) (hM : M.Sound R) :
    ¬ Table.CompleteStrong R M := by
  intro hcomplete
  -- demand 1: continuation `[tok a]`, word `[a]`, derived through A => eps
  obtain ⟨rhs₁, hget₁, hder₁⟩ :=
    hcomplete A [Sym.tok a] [a] [] ⟨[], mem_Ae, derives_refl (toks [a])⟩
  -- demand 2: empty continuation, word `[a]`, derived through A => a
  obtain ⟨rhs₂, hget₂, hder₂⟩ :=
    hcomplete A [] [a] [] ⟨[Sym.tok a], mem_Aa, derives_refl (toks [a])⟩
  have heq : rhs₁ = rhs₂ := Option.some.inj (by rw [← hget₁, ← hget₂])
  subst heq
  -- soundness pins rhs₁ down to a production of A
  have hprod : (A, rhs₁) ∈ R.productions := hM A (LTok.tok a) rhs₁ hget₁
  have hcases : rhs₁ = [] ∨ rhs₁ = [Sym.tok a] := by
    simp only [R, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at hprod
    rcases hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | hf
    · cases h1
    · cases h1; exact Or.inl h2
    · cases h1; exact Or.inr h2
    · cases h1
    · exact absurd hf (by simp)
  rcases hcases with h | h
  · -- rhs₁ = []: demand 2 becomes eps =>* [a], impossible
    subst h
    have hcontra : Derives R (toks ([] : List Tok)) (toks [a]) := hder₂
    have heq := derives_toks_inj hcontra
    simp at heq
  · -- rhs₁ = [tok a]: demand 1 becomes [a,a] =>* [a], impossible
    subst h
    have hcontra : Derives R (toks [a, a]) (toks [a]) := hder₁
    have heq := derives_toks_inj hcontra
    simp at heq

end VerifiedLL1.Examples.Continuation
