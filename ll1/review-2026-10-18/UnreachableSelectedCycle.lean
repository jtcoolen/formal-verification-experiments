import VerifiedLL1.Generator
import VerifiedLL1.LeftRec
open VerifiedLL1
namespace UnreachableLoopProbe
inductive Tok where | a | b deriving DecidableEq, Repr
inductive Var where | S | U deriving DecidableEq, Repr
open Tok Var
instance : FiniteEnum Tok where
  elems := [a,b]
  complete := by intro t; cases t <;> simp
instance : FiniteEnum Var where
  elems := [S,U]
  complete := by intro v; cases v <;> simp

def G : Grammar Tok Var where
  productions := [(S,[Sym.tok a]), (U,[Sym.var U,Sym.tok b]), (U,[])]
  start := S

example : G.ll1Check = true := by decide
example : G.follow U (LTok.tok b) = false := by decide
example : G.follow U LTok.eof = false := by decide
example : G.noLeftRecursion = false := by decide

theorem get_b : G.genTable.get U (LTok.tok b) = some [Sym.var U, Sym.tok b] := by decide

theorem loop_aux : ∀ f : Nat,
    (∀ (ss : List (Sym Tok Var)) (xs : List (LTok Tok)),
      Parser.parseForest G.genTable f (Sym.var U :: ss) (LTok.tok b :: xs) =
        PRes.error ParseError.outOfFuel) ∧
    (∀ xs : List (LTok Tok),
      Parser.parseSym G.genTable f (Sym.var U) (LTok.tok b :: xs) =
        PRes.error ParseError.outOfFuel) := by
  intro f
  induction f with
  | zero =>
    exact ⟨by intros; rfl, by intros; rfl⟩
  | succ f ih =>
    refine ⟨?_, ?_⟩
    · intro ss xs
      rw [parseForest_cons, ih.2 xs]
      rfl
    · intro xs
      rw [parseSym_var]
      simp only [get_b, ih.1 [Sym.tok b] xs]

theorem never_parses_b (fuel : Nat) :
    Parser.parseSym G.genTable fuel (Sym.var U) (ltoks [b] ++ [LTok.eof]) =
      PRes.error ParseError.outOfFuel := (loop_aux fuel).2 [LTok.eof]

example : Parser.parse G G.genTable 10 (ltoks [a] ++ [LTok.eof]) =
    PRes.ok (Tree.node S [Tree.leaf a]) [LTok.eof] := rfl

#print axioms never_parses_b
end UnreachableLoopProbe

namespace VerifiedLL1
universe u v

def Grammar.SelectedLeftCorner {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) (A B : N) : Prop :=
  ∃ pre post : List (Sym T N),
    (A, pre ++ Sym.var B :: post) ∈ G.productions ∧
    G.Select A (pre ++ Sym.var B :: post) x ∧ Derives G pre []

inductive Grammar.SelectedLCPath {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) : N → N → Prop where
  | single {A B} : G.SelectedLeftCorner x A B → G.SelectedLCPath x A B
  | tail {A B C} : G.SelectedLCPath x A B → G.SelectedLeftCorner x B C →
      G.SelectedLCPath x A C

def Grammar.ReachableSelectedLCAcyclic {T : Type u} {N : Type v}
    (G : Grammar T N) : Prop :=
  ∀ x A, G.Occurs A → ¬ G.SelectedLCPath x A A

end VerifiedLL1
