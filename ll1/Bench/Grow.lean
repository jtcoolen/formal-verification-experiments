import VerifiedLL1.Generator

/-!
# The growing-grammar benchmark family

    A0     -> eps
    A(i+1) -> Ai Ai

Every nonterminal is nullable and every nonterminal has exactly one production, so the
grammar is LL(1) and left-recursion free.  What makes it a stress test is the *cost* of the
naive approximation: Fixpoint.iterP is a chain of function applications, so one query
re-unfolds the whole chain, and each A(i+1) query touches Ai twice -- the work grows like
2^d at depth d.  This is the family the memoized backend is measured on.

The nonterminal alphabet is Fin (d+1), which supplies a FiniteEnum instance, so the whole
development (NULLABLE, FIRST, FOLLOW, SELECT, ll1Check) applies unchanged.
-/

open VerifiedLL1

namespace Bench

inductive BTok where
  | x
  deriving DecidableEq, Repr

instance : FiniteEnum BTok where
  elems := [BTok.x]
  complete := by intro t; cases t; simp

/-- Every Fin n is enumerable: this is what lets one benchmark family be indexed by a number
instead of declaring a new inductive type per depth. -/
instance (n : Nat) : FiniteEnum (Fin n) where
  elems := List.finRange n
  complete := fun i => List.mem_finRange i

/-- A0 -> eps, A(i+1) -> Ai Ai over the nonterminal alphabet Fin (d+1). -/
def grow (d : Nat) : Grammar BTok (Fin (d+1)) where
  productions := (List.finRange (d+1)).map fun i =>
    (i, if h : i.val = 0 then []
        else [Sym.var ⟨i.val - 1, by omega⟩, Sym.var ⟨i.val - 1, by omega⟩])
  start := ⟨d, by omega⟩

/-- The deepest nonterminal of the depth-d grammar. -/
def top (d : Nat) : Fin (d+1) := ⟨d, by omega⟩

end Bench
