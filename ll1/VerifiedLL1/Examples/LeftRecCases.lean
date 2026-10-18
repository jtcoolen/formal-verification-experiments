/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.LeftRec

/-!
# The left-recursion checker sees every shape of cycle

`LeftRecChecks.lean` shows the *structural* hypotheses cannot be dropped.  This module shows
the checker is not blind: each classical shape of left recursion makes `noLeftRecursion =
false`, and - exactly as `noLeftRecursion_of_ll1` then forces - a *reduced* grammar with such
a cycle cannot pass `ll1Check` either.

* `DirectLR`:     S -> S a | a
* `IndirectLR`:   S -> A,  A -> S x | z
* `EpsCycleLR`:   S -> U,  U -> U | eps       (epsilon-only cycle, reachable and productive)
* `NullPrefixLR`: S -> E B, E -> eps, B -> S  (a cycle through a nullable prefix)

The first three are reachable and productive, so the theorem predicts a conflict and `decide`
finds one.  The fourth passes the conflict check: no token is ever produced, so no lookahead
selects any production and there is nothing to conflict about.  What fails instead is
productivity - every right-hand side of that grammar is variable-only, and the only erasing
production (E -> eps) can never remove the last variable, so S and B derive no terminal word
at all.  That is exactly the hypothesis `Reduced.2` supplies.
-/

namespace VerifiedLL1.Examples

inductive LRTok where | a | x | z
  deriving DecidableEq, Repr

instance : FiniteEnum LRTok where
  elems := [LRTok.a, LRTok.x, LRTok.z]
  complete := by intro t; cases t <;> simp

namespace DirectLR

open Sym Tree LRTok

inductive Var where | s
  deriving DecidableEq, Repr

open Var

instance : FiniteEnum Var where
  elems := [s]
  complete := by intro v; cases v; simp

/-- Direct left recursion: S -> S a | a. -/
def G : Grammar LRTok Var where
  productions := [ (s, [var s, tok a]), (s, [tok a]) ]
  start := s

theorem cycle : G.LeftCorner s s := ⟨[], [tok a], List.Mem.head _, derives_refl _⟩

/-- The left-recursion checker sees it, and so does the conflict check: both productions of S
are selected by the token a. -/
theorem direct_lr : G.noLeftRecursion = false := by decide
theorem direct_not_ll1 : G.ll1Check = false := by decide

end DirectLR

namespace IndirectLR

open Sym Tree LRTok

inductive Var where | s | a
  deriving DecidableEq, Repr

open Var

instance : FiniteEnum Var where
  elems := [s, a]
  complete := by intro v; cases v <;> simp

/-- Indirect left recursion: S -> A, A -> S x | z. -/
def G : Grammar LRTok Var where
  productions := [ (s, [var a]), (a, [var s, tok x]), (a, [tok z]) ]
  start := s

theorem cycle_s : G.LeftCorner s a := ⟨[], [], List.Mem.head _, derives_refl _⟩
theorem cycle_a : G.LeftCorner a s := ⟨[], [tok x], List.Mem.tail _ (List.Mem.head _), derives_refl _⟩

theorem indirect_lr : G.noLeftRecursion = false := by decide
theorem indirect_not_ll1 : G.ll1Check = false := by decide

end IndirectLR

namespace EpsCycleLR

open Sym Tree LRTok

inductive Var where | s | u
  deriving DecidableEq, Repr

open Var

instance : FiniteEnum Var where
  elems := [s, u]
  complete := by intro v; cases v <;> simp

/-- An epsilon-only cycle, reachable from the start symbol and productive. -/
def G : Grammar LRTok Var where
  productions := [ (s, [var u]), (u, [var u]), (u, []) ]
  start := s

theorem eps_lr : G.noLeftRecursion = false := by decide
theorem eps_not_ll1 : G.ll1Check = false := by decide

end EpsCycleLR

namespace NullPrefixLR

open Sym Tree LRTok

inductive Var where | s | e | b
  deriving DecidableEq, Repr

open Var

instance : FiniteEnum Var where
  elems := [s, e, b]
  complete := by intro v; cases v <;> simp

/-- A cycle through a nullable prefix: S -> E B, E -> eps, B -> S. -/
def G : Grammar LRTok Var where
  productions := [ (s, [var e, var b]), (e, []), (b, [var s]) ]
  start := s

theorem leftcorner_s_b : G.LeftCorner s b :=
  ⟨[var e], [], List.Mem.head _, derives_production e [] (List.Mem.tail _ (List.Mem.head _))⟩
theorem leftcorner_b_s : G.LeftCorner b s := ⟨[], [], List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), derives_refl _⟩

theorem np_lr : G.noLeftRecursion = false := by decide

/-- The conflict check does not see this one, and correctly so: the grammar is LL(1) but not
productive, so Reduced.2 is what rules it out. -/
theorem np_ll1 : G.ll1Check = true := by decide

end NullPrefixLR

end VerifiedLL1.Examples
