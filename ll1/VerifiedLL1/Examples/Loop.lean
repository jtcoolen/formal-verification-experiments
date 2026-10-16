/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Completeness

/-!
# Phase 3 counterexample - a *correct* table that never terminates

The grammar

    p -> p | a | eps

with start symbol p has language { [], [a] }.  The table below maps p, under every
lookahead, to the right-hand side [var p]:

* it is **sound** - every entry names a real production;
* it is **adequate** - the entry repeats the symbol being expanded, so adequacy is
  the identity;
* it is **complete** - whenever *some* production of p derives the remaining input,
  so does [var p]: if p => a and then the rest, then p => a =>* ... ; if p => eps
  then p => eps as well.  Each case is a *forward* derivation step followed by the
  hypothesis, so no cancellation of derivations is needed.

Yet no fuel ever suffices: the parser expands p into p until the fuel runs out, so
it rejects the word a, which *is* in the language.  This is exactly the
non-consuming expansion cycle the phase statement asks to handle, and it is why
completeness is stated with the extra Table.Progressing hypothesis.

We also prove that *no* ranking can rescue this table: for every w the table is not
Progressing, and that the grammar is not cycleFree.
-/

universe u v

namespace VerifiedLL1.Examples.Loop

inductive Tok where
  | a
  deriving DecidableEq, Repr

inductive Var where
  | p
  deriving DecidableEq, Repr

open Tok Var Sym Tree

/-- p -> p | a | eps. -/
def L : Grammar Tok Var where
  productions := [⟨p, [var p]⟩, ⟨p, [tok a]⟩, ⟨p, []⟩]
  start := p

/-- The looping table: p expands to p under every lookahead. -/
def M : Table Tok Var where
  entries :=
    [ ⟨p, (LTok.tok a, [var p])⟩
    , ⟨p, (LTok.eof, [var p])⟩ ]

theorem mem_pp : (p, [var p]) ∈ L.productions := by simp [L, List.mem_cons]
theorem mem_pa : (p, [tok a]) ∈ L.productions := by simp [L, List.mem_cons]
theorem mem_pe : (p, []) ∈ L.productions := by simp [L, List.mem_cons]

theorem L_wellFormed : L.wellFormed := by
  refine ⟨⟨_, mem_pp⟩, ?_⟩
  intro A rhs hp x hx B hxB
  subst hxB
  simp [L, List.mem_cons] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [List.mem_singleton] at hx
    cases hx; exact ⟨_, mem_pp⟩
  · rw [List.mem_singleton] at hx
    exact absurd hx (Sym.ne_var_tok B a)
  · exact absurd hx (by simp)

/-- a is in the language: p => a. -/
theorem a_in_language : L.language [a] := by
  refine (L.language_iff_tree [a]).mpr ⟨[leaf a], ?_, ?_⟩
  · exact Valid.mk mem_pa (MatchList.tok MatchList.nil)
  · simp [Tree.yieldForest_cons, Tree.yield_node, Tree.yield_leaf]

/-- eps is in the language: p => eps. -/
theorem nil_in_language : L.language ([] : List Tok) := by
  refine (L.language_iff_tree ([] : List Tok)).mpr ⟨[], ?_, ?_⟩
  · exact Valid.mk mem_pe MatchList.nil
  · simp [Tree.yield_node, Tree.yieldForest_nil]

section Lookup

theorem get_M (x : LTok Tok) : M.get p x = some ([var p] : List (Sym Tok Var)) := by
  cases x with
  | tok t => cases t <;> rfl
  | eof => rfl

end Lookup

section Correct

theorem M_sound : M.Sound L := Table.sound_of_check L M (by decide)

/-- Adequacy is the identity here: the entry repeats the symbol it expands. -/
theorem M_adequate : M.Adequate L := by
  intro A x rhs hget cont u v hlook hder
  cases A with
  | p =>
      have hsome : some rhs = some ([var p] : List (Sym Tok Var)) := by
        rw [← hget]
        exact get_M x
      have hrhs : rhs = [var p] := Option.some.inj hsome
      subst hrhs
      exact hder

theorem productions_p : ∀ rhs, (p, rhs) ∈ L.productions →
    rhs = [var p] ∨ rhs = [tok a] ∨ rhs = [] := by
  intro rhs hp
  simp only [L, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | hf
  · cases h1; exact Or.inl h2
  · cases h1; exact Or.inr (Or.inl h2)
  · cases h1; exact Or.inr (Or.inr h2)
  · exact absurd hf (by simp)

theorem M_complete : M.Complete L := by
  intro A cont u v hpremise
  obtain ⟨rhs, hp, hder⟩ := hpremise
  cases A with
  | p =>
      rcases productions_p rhs hp with h | h | h
      · subst h
        exact ⟨[var p], get_M (lookaheadOf (u ++ v)), hder⟩
      · subst h
        -- the table expands p to p; p can also expand to a, which is what the
        -- hypothesis used, so one forward step simulates it
        refine ⟨[var p], get_M (lookaheadOf (u ++ v)), ?_⟩
        have h1 : Derives L ([var p] ++ cont) ([tok a] ++ cont) := by
          simpa using derives_ctx (derives_production p [tok a] mem_pa) [] cont
        exact derives_trans h1 hder
      · subst h
        refine ⟨[var p], get_M (lookaheadOf (u ++ v)), ?_⟩
        have h1 : Derives L ([var p] ++ cont) ([] ++ cont) := by
          simpa using derives_ctx (derives_production p [] mem_pe) [] cont
        exact derives_trans h1 hder

/-- **The looping table is correct** in the independent Phase 2 sense. -/
theorem M_correct : M.Correct L := ⟨M_sound, M_adequate, M_complete⟩

end Correct

section NoProgress

/-- No ranking makes this table progressing: p is expanded to a child p that yields
eps at the very position where the expansion started. -/
theorem not_progressing (w : Var → Nat) : ¬ Table.Progressing L M w := by
  intro hw
  -- the forest [node p []] matches [var p] and yields eps
  have hmatch : MatchList L [var p] [Tree.node p []] := by
    simpa using MatchList.var mem_pe MatchList.nil MatchList.nil
  have hyield : Tree.yieldForest ([Tree.node p []] : List (Tree Tok Var)) = [] := by
    simp [Tree.yieldForest_cons, Tree.yield_node, Tree.yieldForest_nil]
  have h := hw p LTok.eof [var p] (get_M LTok.eof) [] (Tree.node p []) [] [] [] p
    hmatch hyield (by simp) (by simp [Tree.root?]) rfl
  omega

/-- The grammar has a non-consuming expansion cycle: p => p. -/
theorem not_cycleFree : ¬ cycleFree L := by
  intro h
  exact h p ⟨[var p], derives_refl _, by
    simpa using Derives1.step (A := p) (rhs := [var p]) (pre := []) (post := []) mem_pp⟩

end NoProgress

section NonTermination

open Parser

/-- Parsing p at any position of a non-empty stream loops until the fuel is gone:
both the forest and the single-symbol parse fail with outOfFuel, at every fuel. -/
theorem loop_aux : ∀ (f : Nat) (x : LTok Tok) (xs : List (LTok Tok)),
    parseForest M f [var p] (x :: xs) = PRes.error ParseError.outOfFuel ∧
      parseSym M f (Sym.var p) (x :: xs) = PRes.error ParseError.outOfFuel := by
  intro f
  induction f with
  | zero => intro x xs; exact ⟨by simp [parseForest], by simp [parseSym]⟩
  | succ f ih =>
      intro x xs
      refine ⟨?_, ?_⟩
      · rw [parseForest_cons, (ih x xs).2]
        simp [pbind]
      · rw [parseSym_var]
        simp only [get_M x, (ih x xs).1]

theorem pforest_p : ∀ (f : Nat) (x : LTok Tok) (xs : List (LTok Tok)),
    parseForest M f [var p] (x :: xs) = PRes.error ParseError.outOfFuel :=
  fun f x xs => (loop_aux f x xs).1

/-- **The counterexample.**  Even with a correct table, the parser rejects the word
a - which the grammar generates - at *every* fuel value.  Completeness genuinely
needs the progress hypothesis. -/
theorem never_accepts_a :
    ∀ (fuel : Nat) (t : Tree Tok Var),
      Parser.parse L M fuel (ltoks [a] ++ [LTok.eof]) ≠ PRes.ok t [LTok.eof] := by
  intro fuel t h
  obtain ⟨hcall, _⟩ := parse_ok h
  have h1 : ltoks [a] ++ [LTok.eof] = LTok.tok a :: (ltoks [] ++ [LTok.eof]) := rfl
  rw [h1] at hcall
  have hkey : parseForest M fuel [var p] (LTok.tok a :: (ltoks [] ++ [LTok.eof])) =
      PRes.error ParseError.outOfFuel := pforest_p fuel (LTok.tok a) (ltoks [] ++ [LTok.eof])
  rw [hkey] at hcall
  exact absurd hcall (by simp)

/-- Likewise for the empty word, which the grammar also generates. -/
theorem never_accepts_nil :
    ∀ (fuel : Nat) (t : Tree Tok Var),
      Parser.parse L M fuel (ltoks ([] : List Tok) ++ [LTok.eof]) ≠ PRes.ok t [LTok.eof] := by
  intro fuel t h
  obtain ⟨hcall, _⟩ := parse_ok h
  have h1 : ltoks ([] : List Tok) ++ [LTok.eof] = (LTok.eof :: [] : List (LTok Tok)) := rfl
  rw [h1] at hcall
  have hkey : parseForest M fuel [var p] (LTok.eof :: ([] : List (LTok Tok))) =
      PRes.error ParseError.outOfFuel := pforest_p fuel LTok.eof []
  rw [hkey] at hcall
  exact absurd hcall (by simp)

end NonTermination

end VerifiedLL1.Examples.Loop
