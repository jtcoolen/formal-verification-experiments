import VerifiedLL1.Generator
open VerifiedLL1
namespace GenProbe
inductive Tok where | a | b deriving DecidableEq, Repr
inductive Var where | S deriving DecidableEq, Repr
open Tok Var
instance : FiniteEnum Tok where
  elems := [a,b]
  complete := by intro t; cases t <;> simp
instance : FiniteEnum Var where
  elems := [S]
  complete := by intro v; cases v <;> simp

def G : Grammar Tok Var where
  productions := [(S,[Sym.tok a]), (S,[Sym.tok a,Sym.tok b])]
  start := S

example : G.ll1Check = false := by decide
example : G.language [a,b] := by
  exact derives_production S [Sym.tok a, Sym.tok b] (by simp [G])
example : Parser.parse G G.genTable 20 (ltoks [a,b] ++ [LTok.eof]) =
    PRes.error (ParseError.trailing (LTok.tok b)) := rfl
#eval G.ll1Check
#eval G.genTable
#eval Parser.parse G G.genTable 20 (ltoks [a,b] ++ [LTok.eof])
end GenProbe
