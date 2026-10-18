import Bench.Grow
import VerifiedLL1.Memo

/-!
# The same analyses, computed by the memoized Boolean-list backend

Everything here is *proved* equal to the library's analysis (see Bench/MemoChecks.lean); the
point of the module is that it is a different computation, so the two can be timed against
each other on the growing-grammar family.
-/

open VerifiedLL1 VerifiedLL1.Memo

namespace Bench.Memo

variable {T : Type} {N : Type} [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- Memoized NULLABLE. -/
def mNull (G : Grammar T N) : N → Bool :=
  iterMemo (FiniteEnum.elems (α := N)) (nullableP G) G.nullableRounds

/-- Memoized REACH. -/
def mOcc (G : Grammar T N) : N → Bool :=
  iterMemo (FiniteEnum.elems (α := N)) (occursP G) G.occursRounds

/-- Memoized FIRST (over the memoized NULLABLE). -/
def mFirst (G : Grammar T N) : Sym T N → LTok T → Bool :=
  fun s x => iterMemo (FiniteEnum.elems (α := Sym T N × LTok T))
    (firstP G (symNull (mNull G))) G.firstRounds (s, x)

/-- Memoized FOLLOW (over the memoized NULLABLE, FIRST and REACH). -/
def mFollow (G : Grammar T N) : N → LTok T → Bool :=
  fun A x => iterMemo (FiniteEnum.elems (α := N × LTok T))
    (followP G (mFirst G) (symNull (mNull G)) (mOcc G)) G.followRounds (A, x)

/-- SELECT and the conflict check, driven by the memoized analyses. -/
def mSelectTest (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) : Bool :=
  ((!isEof x && firstListTest (mFirst G) (symNull (mNull G)) rhs x) ||
    (rhs.all (symNull (mNull G)) && mFollow G A x))

def mSelectRhs (G : Grammar T N) (A : N) (x : LTok T) : List (List (Sym T N)) :=
  (G.productions.filter fun pr => (pr.1 == A && mSelectTest G A pr.2 x)).map Prod.snd

def mll1Check (G : Grammar T N) : Bool :=
  (FiniteEnum.elems (α := N × LTok T)).all fun p =>
    (mSelectRhs G p.1 p.2).all fun a => (mSelectRhs G p.1 p.2).all fun b => (a == b)

end Bench.Memo

/-!
# Memoize only the outer loop

The full memoized pipeline above tabulates the whole carrier at every round, so a *sparse*
query pays for points nobody asked about; the kernel's whnf cache already shares the closed
terms iterP P k, so the demand-driven chain is cheap when few carrier points are visited.
FOLLOW, in contrast, is queried at (nearly) every (nonterminal, lookahead) pair by the
conflict check, so it is the loop worth tabulating - while FIRST, NULLABLE and REACH stay
the library's own iterP computations.
-/
namespace Bench.Memo.Fol

variable {T : Type} {N : Type} [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- Memoized FOLLOW over the library's FIRST / NULLABLE / REACH. -/
def fFollow (G : Grammar T N) : N → LTok T → Bool :=
  fun A x => iterMemo (FiniteEnum.elems (α := N × LTok T))
    (followP G G.first (firstNul G) G.occurs) G.followRounds (A, x)

def fSelectTest (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) : Bool :=
  ((!isEof x && firstListTest G.first (firstNul G) rhs x) ||
    (rhs.all (firstNul G) && fFollow G A x))

def fSelectRhs (G : Grammar T N) (A : N) (x : LTok T) : List (List (Sym T N)) :=
  (G.productions.filter fun pr => (pr.1 == A && fSelectTest G A pr.2 x)).map Prod.snd

def fll1Check (G : Grammar T N) : Bool :=
  (FiniteEnum.elems (α := N × LTok T)).all fun p =>
    (fSelectRhs G p.1 p.2).all fun a => (fSelectRhs G p.1 p.2).all fun b => (a == b)

end Bench.Memo.Fol
