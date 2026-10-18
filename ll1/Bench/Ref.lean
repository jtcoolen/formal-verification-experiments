import VerifiedLL1.Examples.QCircuits
import VerifiedLL1.Examples.Circuits
import VerifiedLL1.Examples.Toy
import Bench.Circ

/-!
# The all-iterP reference pipeline

The library's FOLLOW computation is now the memoized one (\`Grammar.follow_eq_iterP\` proves it
equal to the iterP approximant).  This module re-states the *old* pipeline - iterP for every
analysis - so the shipped code and the reference can be timed against each other on the same
grammars, inside one build.
-/

open VerifiedLL1

namespace Bench.Ref

variable {T : Type} {N : Type} [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- FOLLOW by the iterP chain (the pre-memoization computation). -/
def rFollow (G : Grammar T N) (A : N) (x : LTok T) : Bool :=
  Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) G.followRounds (A, x)

/-- SELECT with the iterP FOLLOW. -/
def rSelectTest (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) : Bool :=
  ((!isEof x && firstListTest G.first (firstNul G) rhs x) ||
    (rhs.all (firstNul G) && rFollow G A x))

def rSelectRhs (G : Grammar T N) (A : N) (x : LTok T) : List (List (Sym T N)) :=
  (G.productions.filter fun pr => (pr.1 == A && rSelectTest G A pr.2 x)).map Prod.snd

def rll1Check (G : Grammar T N) : Bool :=
  (FiniteEnum.elems (α := N × LTok T)).all fun p =>
    (rSelectRhs G p.1 p.2).all fun a => (rSelectRhs G p.1 p.2).all fun b => (a == b)

/-- The reference pipeline really is the library's check. -/
theorem rFollow_eq (G : Grammar T N) (A : N) (x : LTok T) : rFollow G A x = G.follow A x :=
  (Grammar.follow_eq_iterP G A x).symm

theorem rSelectTest_eq (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) :
    rSelectTest G A rhs x = G.selectTest A rhs x := by
  unfold rSelectTest Grammar.selectTest
  rw [rFollow_eq]

theorem rSelectRhs_eq (G : Grammar T N) (A : N) (x : LTok T) :
    rSelectRhs G A x = G.selectRhs A x := by
  unfold rSelectRhs Grammar.selectRhs
  simp only [rSelectTest_eq]

theorem rll1Check_eq (G : Grammar T N) : rll1Check G = G.ll1Check := by
  unfold rll1Check Grammar.ll1Check
  simp only [rSelectRhs_eq]

end Bench.Ref
