import VerifiedLL1
namespace ReviewProbe
open VerifiedLL1
inductive Tok where | a | b
  deriving DecidableEq, Repr
inductive Var where | s | u | v | dead
  deriving DecidableEq, Repr
instance : FiniteEnum Tok where
  elems := [.a, .b]
  complete := by intro x; cases x <;> simp
instance : FiniteEnum Var where
  elems := [.s, .u, .v, .dead]
  complete := by intro x; cases x <;> simp
open Sym

def unreachNull : Grammar Tok Var :=
  ⟨[(.s, [tok .a]), (.u, []), (.u, [var .v]), (.v, [])], .s⟩
def duplicate : Grammar Tok Var :=
  ⟨[(.s, [tok .a]), (.s, [tok .a])], .s⟩
def unreachFirst : Grammar Tok Var :=
  ⟨[(.s, [tok .a]), (.u, [tok .a]), (.u, [tok .a, tok .b])], .s⟩
def followDifference : Grammar Tok Var :=
  ⟨[(.s, [tok .a]), (.u, []), (.u, [var .v]), (.v, []), (.dead, [var .u, tok .b])], .s⟩
example : unreachNull.ll1Check = true := by decide
example : duplicate.ll1Check = true := by decide
example : unreachFirst.ll1Check = false := by decide
example : unreachNull.follow .u .eof = false := by decide
example : unreachFirst.genTable.get .u (.tok .a) = some [tok .a] := by decide
example : followDifference.follow .u (.tok .b) = false := by decide
example : followDifference.ll1Check = true := by decide
example {T N : Type} [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (G : Grammar T N) (hall : G.Ll1) (A : N) (x : LTok T) (rhs : List (Sym T N)) :
    G.genTable.get A x = some rhs ↔ (A, rhs) ∈ G.productions ∧ G.Select A rhs x :=
  ⟨Grammar.genTable_entry, fun h => Grammar.genTable_get_of_select G hall h.1 h.2⟩
#eval (unreachNull.ll1Check, duplicate.ll1Check, unreachFirst.ll1Check, followDifference.ll1Check)
end ReviewProbe
