/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Fuel

/-!
# Phase 5.7 regression checks - the automatic fuel on concrete grammars

Every check below is a `rfl` or a `decide`: the kernel itself runs the generated parser at
the fuel `Grammar.fuelFor` chooses.  Together they cover the cases the review asks to keep
regressed: end-of-input selection, nullable prefixes, repeated nullable siblings, right
recursion, invalid input (a syntax error rather than fuel exhaustion), trailing input, and
the unreachable selected cycle, whose start parser must terminate even though its `U`
subparser cannot.
-/

namespace VerifiedLL1.Examples.FuelChecks

open Sym Tree Parser

section Eof
inductive TE where | c deriving DecidableEq, Repr
inductive VE where | s deriving DecidableEq, Repr
open TE VE
instance : FiniteEnum TE where
  elems := [c]
  complete := by intro t; cases t <;> simp
instance : FiniteEnum VE where
  elems := [s]
  complete := by intro v; cases v <;> simp

/-- `S -> \varepsilon \mid c`: the empty alternative is selected by `eof`. -/
def E : Grammar TE VE where
  productions := [(s, []), (s, [tok c])]
  start := s

theorem E_ll1 : E.ll1Check = true := by decide
theorem E_fuel : E.fuelFor [] = 12 := rfl
theorem E_empty : E.parseGenerated [] = PRes.ok (node s []) [LTok.eof] := rfl
theorem E_c : E.parseGenerated [c] = PRes.ok (node s [leaf c]) [LTok.eof] := rfl
/-- Trailing input is reported as trailing input, not as fuel exhaustion. -/
theorem E_trailing : E.parseGenerated [c, c] =
    PRes.error (ParseError.trailing (LTok.tok c)) := rfl
end Eof

section Nullable
inductive TN where | x deriving DecidableEq, Repr
inductive VN where | s | n deriving DecidableEq, Repr
open TN VN
instance : FiniteEnum TN where
  elems := [x]
  complete := by intro t; cases t <;> simp
instance : FiniteEnum VN where
  elems := [s, n]
  complete := by intro v; cases v <;> simp

/-- `S -> N N x; N -> \varepsilon`: two *repeated* nullable siblings before the token. -/
def R : Grammar TN VN where
  productions := [(s, [var n, var n, tok x]), (n, [])]
  start := s

theorem R_ll1 : R.ll1Check = true := by decide
theorem R_x : R.parseGenerated [x] =
    PRes.ok (node s [node n [], node n [], leaf x]) [LTok.eof] := rfl
theorem R_empty : R.parseGenerated [] =
    PRes.error (ParseError.noEntry s LTok.eof) := rfl
theorem R_bad : R.parseGenerated [x, x] =
    PRes.error (ParseError.trailing (LTok.tok x)) := rfl
end Nullable

section RightRec
inductive TR where | x | y deriving DecidableEq, Repr
inductive VR where | q deriving DecidableEq, Repr
open TR VR
instance : FiniteEnum TR where
  elems := [x, y]
  complete := by intro t; cases t <;> simp
instance : FiniteEnum VR where
  elems := [q]
  complete := by intro v; cases v <;> simp

/-- `Q -> x Q \mid \varepsilon`: right recursion, so the nesting depth grows with the
input; the bound has to pay for it out of the input-length blocks. -/
def RR : Grammar TR VR where
  productions := [(q, [tok x, var q]), (q, [])]
  start := q

theorem RR_ll1 : RR.ll1Check = true := by decide
theorem RR_fuel : RR.fuelFor [x, x, x] = 44 := rfl
theorem RR_xxx : RR.parseGenerated [x, x, x] =
    PRes.ok (node q [leaf x, node q [leaf x, node q [leaf x, node q []]]]) [LTok.eof] := rfl
theorem RR_empty : RR.parseGenerated [] = PRes.ok (node q []) [LTok.eof] := rfl
/-- A failing run also terminates: `y` has no table entry for `q`, and the parser reports
that instead of running out of fuel. -/
theorem RR_bad : RR.parseGenerated [x, y] =
    PRes.error (ParseError.noEntry q (LTok.tok y)) := rfl
end RightRec

section Unreachable
inductive TU where | a | b deriving DecidableEq, Repr
inductive VU where | s | u deriving DecidableEq, Repr
open TU VU
instance : FiniteEnum TU where
  elems := [a, b]
  complete := by intro t; cases t <;> simp
instance : FiniteEnum VU where
  elems := [s, u]
  complete := by intro v; cases v <;> simp

/-- `S -> a; U -> U b \mid \varepsilon`: the checker accepts it, `U` lies on a selected
cycle at `b`, and the `U` subparser exhausts every fuel - but the *start* parser must
terminate on every input, which is what these checks show. -/
def U : Grammar TU VU where
  productions := [(s, [tok a]), (u, [var u, tok b]), (u, [])]
  start := s

theorem U_ll1 : U.ll1Check = true := by decide
theorem U_a : U.parseGenerated [a] = PRes.ok (node s [leaf a]) [LTok.eof] := rfl
theorem U_b : U.parseGenerated [b] = PRes.error (ParseError.noEntry s (LTok.tok b)) := rfl
theorem U_empty : U.parseGenerated [] = PRes.error (ParseError.noEntry s LTok.eof) := rfl
/-- The `U` *subparser* diverges on `b` at every fuel
(`VerifiedLL1.Examples.UnreachableSelectedCycle.never_parses_b`), and `U` lies on a selected
cycle at `b` - yet the start parser terminates on every input above.  That is the gap the
reachable-only formulation of Phase 5.3 leaves, and the gap `fuelFor` closes. -/
theorem U_cycle : U.SelectedLCPath (LTok.tok b) u u :=
  Grammar.SelectedLCPath.single
    ⟨[], [tok b], List.Mem.tail (s, [tok a]) (List.Mem.head _),
      Or.inl ⟨by simp [isEof],
        ⟨[], derives_single (Derives1.step (pre := []) (rhs := []) (post := [tok b])
          (List.Mem.tail (s, [tok a]) (List.Mem.tail (u, [var u, tok b]) (List.Mem.head _))))⟩⟩,
      derives_refl _⟩

end Unreachable

/-- The bound is a *theorem* about these grammars, not just a number that happens to work:
no input exhausts fuel, and success is exactly membership with the exact tree. -/
theorem E_ok : E.FuelBound E.fuelFor := E.fuelFor_bound E_ll1
theorem R_ok : R.FuelBound R.fuelFor := R.fuelFor_bound R_ll1
theorem RR_ok : RR.FuelBound RR.fuelFor := RR.fuelFor_bound RR_ll1
theorem U_ok : U.FuelBound U.fuelFor := U.fuelFor_bound U_ll1

#print axioms E_ok
#print axioms R_ok
#print axioms RR_ok
#print axioms U_ok
#print axioms E_empty
#print axioms RR_xxx
#print axioms U_b

end VerifiedLL1.Examples.FuelChecks