/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.SelectedLC

/-!
# The reachability hypothesis of Phase 5.3 is necessary

`Grammar.reachableSelectedLCAcyclic` excludes selected left-corner cycles at occurring
nonterminals.  This module shows that the restriction to `Occurs` cannot be dropped, on
the grammar

    S -> a
    U -> U b | epsilon

from the review artifact.  The checker accepts it: this repository's FOLLOW only
collects lookaheads from *reachable* occurrences, so `b` is not in `FOLLOW(U)` and the
epsilon rule is not selected at `b`.  Nevertheless the entry the generator writes for
(U, b) selects `U b`, so `U` lies on a selected cycle at `b` - and a subparser started at
`U` on the input `b` exhausts every fuel.  Parsing from the start symbol is unaffected,
which is exactly the gap between a global subparser theorem and the reachable one.
-/

namespace VerifiedLL1.Examples.UnreachableSelectedCycle

open Sym Tree Parser

inductive Tok where
  | a | b
  deriving DecidableEq, Repr

inductive Var where
  | S | U
  deriving DecidableEq, Repr

open Tok Var

instance : FiniteEnum Tok where
  elems := [a, b]
  complete := by intro t; cases t <;> simp

instance : FiniteEnum Var where
  elems := [S, U]
  complete := by intro v; cases v <;> simp

/-- The grammar of the review artifact. -/
def G : Grammar Tok Var where
  productions := [(S, [tok a]), (U, [var U, tok b]), (U, [])]
  start := S

/-- The generator accepts it: `b` is not in `FOLLOW(U)` because the only occurrence of `U`
that could contribute it is unreachable. -/
example : G.ll1Check = true := by decide

example : G.follow U (LTok.tok b) = false := by decide

example : G.follow U LTok.eof = false := by decide

/-- `U` does not occur, so the grammar is not reduced. -/
theorem not_occurs_U : ¬ G.Occurs U := by
  intro h
  have h' : G.occurs U = true := (occurs_iff G U).mpr h
  exact absurd h' (by decide)

example : ¬ G.Reduced := by
  intro hred
  exact not_occurs_U (hred.1 U ⟨[var U, tok b], List.Mem.tail (S, [tok a]) (List.Mem.head _)⟩)

/-- `U` nevertheless carries a selected cycle at the lookahead `b`. -/
theorem selLCPath_U_U : G.SelectedLCPath (LTok.tok b) U U := by
  refine Grammar.SelectedLCPath.single ⟨[], [tok b], ?_, ?_, derives_refl _⟩
  · exact List.Mem.tail (S, [tok a]) (List.Mem.head _)
  · refine Or.inl ⟨by simp [isEof], ⟨[], derives_single (Derives1.step (pre := []) (rhs := [])
      (post := [tok b]) (List.Mem.tail (S, [tok a])
        (List.Mem.tail (U, [var U, tok b]) (List.Mem.head _))))⟩⟩

/-- **The unrestricted version is false.**  A selected cycle exists at a non-occurring
nonterminal, and the checker still passes. -/
example : ¬ (∀ (x : LTok Tok) (A : Var), ¬ G.SelectedLCPath x A A) :=
  fun h => h (LTok.tok b) U selLCPath_U_U

/-- The generated entry for `(U, b)` selects `U b`. -/
theorem get_b : G.genTable.get U (LTok.tok b) = some [var U, tok b] := by decide

/-- **A subparser started at `U` on the input `b` never terminates**, at any fuel: the
selected cycle is a real operational divergence, not an artifact of the definition. -/
theorem loop_aux : ∀ f : Nat,
    (∀ (ss : List (Sym Tok Var)) (xs : List (LTok Tok)),
      parseForest G.genTable f (var U :: ss) (LTok.tok b :: xs) =
        PRes.error ParseError.outOfFuel) ∧
    (∀ xs : List (LTok Tok),
      parseSym G.genTable f (var U) (LTok.tok b :: xs) =
        PRes.error ParseError.outOfFuel) := by
  intro f
  induction f with
  | zero => exact ⟨by intros; rfl, by intros; rfl⟩
  | succ f ih =>
      refine ⟨?_, ?_⟩
      · intro ss xs
        rw [parseForest_cons, ih.2 xs]
        rfl
      · intro xs
        rw [parseSym_var]
        simp only [get_b, ih.1 [tok b] xs]

/-- The subparser call itself. -/
theorem never_parses_b (fuel : Nat) :
    parseSym G.genTable fuel (var U) (ltoks [b] ++ [LTok.eof]) =
      PRes.error ParseError.outOfFuel := (loop_aux fuel).2 [LTok.eof]

/-- Parsing from the start symbol is fine. -/
example : Parser.parse G G.genTable 10 (ltoks [a] ++ [LTok.eof]) =
    PRes.ok (Tree.node S [Tree.leaf a]) [LTok.eof] := rfl

end VerifiedLL1.Examples.UnreachableSelectedCycle
