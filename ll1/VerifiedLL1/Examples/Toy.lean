/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.First

/-!
# Phase 1.4 — A worked example grammar

A small grammar with epsilon productions, used to exercise the definitions and to
show that the correspondence theorem really does both *accept* and *reject* words.

```text
s → p q
p → a | ε
q → b q | ε
```

Its language is `{a·bⁿ | n ≥ 0} ∪ {bⁿ | n ≥ 0}`.
-/

namespace VerifiedLL1.Examples.Toy

inductive Tok where
  | a | b | c
  deriving DecidableEq, Repr

inductive Var where
  | s | p | q | u
  deriving DecidableEq, Repr

open Tok Var Sym Tree

/-- The example grammar. -/
def G : Grammar Tok Var where
  productions :=
    [ (s, [var p, var q])
    , (p, [tok a])
    , (p, [])
    , (q, [tok b, var q])
    , (q, []) ]
  start := s

section Prods

theorem mem_sq : (s, [var p, var q]) ∈ G.productions := List.Mem.head _
theorem mem_pa : (p, [tok a]) ∈ G.productions := List.Mem.tail _ (List.Mem.head _)
theorem mem_pe : (p, []) ∈ G.productions := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem mem_qbq : (q, [tok b, var q]) ∈ G.productions :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem mem_qe : (q, []) ∈ G.productions :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- `G` is well-formed: the start symbol has a production, and so does every
nonterminal mentioned on a right-hand side. -/
theorem wellFormed : G.wellFormed := by
  refine ⟨⟨_, mem_sq⟩, ?_⟩
  intro A rhs hp x hx B hxB
  subst hxB
  -- enumerate the (finitely many) productions
  simp [G] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `s ⇒ p q`
    rw [List.mem_cons, List.mem_singleton] at hx
    rcases hx with h | h
    · cases h; exact ⟨_, mem_pa⟩
    · cases h; exact ⟨_, mem_qbq⟩
  · -- `p ⇒ a`
    rw [List.mem_cons] at hx
    rcases hx with h | h
    · cases h
    · cases h
  · -- `p ⇒ ε`
    cases hx
  · -- `q ⇒ b q`
    rw [List.mem_cons, List.mem_singleton] at hx
    rcases hx with h | h
    · exact absurd h (Sym.ne_var_tok B b)
    · cases h; exact ⟨_, mem_qbq⟩
  · -- `q ⇒ ε`
    cases hx

end Prods

section Trees

/-- The parse tree of the word `a b`: `s ⇒ p q ⇒ a q ⇒ a b q ⇒ a b`. -/
def tree_ab : Tree Tok Var :=
  node s [node p [leaf a], node q [leaf b, node q []]]

theorem tree_ab_valid : Valid G tree_ab :=
  Valid.mk mem_sq
    (MatchList.var mem_pa (MatchList.tok MatchList.nil)
      (MatchList.var mem_qbq
        (MatchList.tok (MatchList.var mem_qe MatchList.nil MatchList.nil))
        MatchList.nil))

theorem tree_ab_yield : yield tree_ab = [a, b] := by simp [tree_ab]

/-- `s ⇒ p q ⇒ a q ⇒ a`, using `q ⇒ ε`. -/
def tree_a : Tree Tok Var := node s [node p [leaf a], node q []]

theorem tree_a_valid : Valid G tree_a :=
  Valid.mk mem_sq
    (MatchList.var mem_pa (MatchList.tok MatchList.nil)
      (MatchList.var mem_qe MatchList.nil MatchList.nil))

theorem tree_a_yield : yield tree_a = [a] := by simp [tree_a]

/-- `b b`, derived with `p ⇒ ε`: the epsilon branch really is used. -/
def tree_bb : Tree Tok Var :=
  node s [node p [], node q [leaf b, node q [leaf b, node q []]]]

theorem tree_bb_valid : Valid G tree_bb :=
  Valid.mk mem_sq
    (MatchList.var mem_pe MatchList.nil
      (MatchList.var mem_qbq
        (MatchList.tok (MatchList.var mem_qbq
          (MatchList.tok (MatchList.var mem_qe MatchList.nil MatchList.nil))
          MatchList.nil))
        MatchList.nil))

theorem tree_bb_yield : yield tree_bb = [b, b] := by simp [tree_bb]

/-- `ε ∈ ⟦G⟧`, via `p ⇒ ε` and `q ⇒ ε`. -/
def tree_eps : Tree Tok Var := node s [node p [], node q []]

theorem tree_eps_valid : Valid G tree_eps :=
  Valid.mk mem_sq
    (MatchList.var mem_pe MatchList.nil (MatchList.var mem_qe MatchList.nil MatchList.nil))

theorem tree_eps_yield : yield tree_eps = [] := by simp [tree_eps]

end Trees

section Derivations

/-- Soundness instantiated at the examples: each valid tree gives a derivation. -/
theorem derives_ab : Derives G [var s] (toks [a, b]) := by
  rw [← tree_ab_yield]; exact valid_derives tree_ab_valid

theorem derives_a : Derives G [var s] (toks [a]) := by
  rw [← tree_a_yield]; exact valid_derives tree_a_valid

theorem derives_bb : Derives G [var s] (toks [b, b]) := by
  rw [← tree_bb_yield]; exact valid_derives tree_bb_valid

theorem language_ab : G.language [a, b] := derives_ab

theorem language_bb : G.language [b, b] := derives_bb

/-- `ε` is in the language, via `p ⇒ ε` and `q ⇒ ε`. -/
theorem language_eps : G.language [] := by
  rw [← tree_eps_yield]; exact valid_derives tree_eps_valid

/-- The correspondence theorem instantiated: the two views coincide. -/
theorem iff_example : (∃ ts, Valid G (node s ts) ∧ yield (node s ts) = [a, b]) ↔
    Derives G [var s] (toks [a, b]) := tree_iff_derives

end Derivations

section Counterexamples

/-- `p ⇒ b` is not a production, so the one-node tree with yield `b` is invalid. -/
theorem not_valid_pb : ¬ Valid G (node p [leaf b]) := by
  intro h
  obtain ⟨rhs, hp, hm⟩ := h
  cases rhs with
  | nil =>
      have : ([Tree.leaf b] : List (Tree Tok Var)) = [] := MatchList.eq_nil hm
      cases this
  | cons x xs =>
      cases x with
      | tok t =>
          obtain ⟨ts', hts, _⟩ := MatchList.eq_leaf_cons hm
          cases hts
          exact absurd hp (by simp [G])
      | var A =>
          obtain ⟨ts', rhsA, ts'', hts, _, _, _⟩ := MatchList.eq_node_cons hm
          cases hts

/-- A second, deliberately tiny grammar, used to show that the framework proves
*rejection* as well as acceptance.

```text
u → c
``` -/
def H : Grammar Tok Var where
  productions := [ (u, [tok c]) ]
  start := u

theorem mem_uc : (u, [tok c]) ∈ H.productions := List.Mem.head _

/-- `a ∉ ⟦H⟧`: no parse tree over `H` yields `[a]`.  The proof goes through the
correspondence theorem, so it rules out *every* tree, not just the ones we
thought to draw. -/
theorem not_language_H_a : ¬ H.language [a] := by
  intro h
  obtain ⟨ts, hv, hy⟩ := H.language_iff_tree [a] |>.mp h
  obtain ⟨rhs, hp, hm⟩ := hv
  have hrhs : rhs = [tok c] := by
    simpa [H, Prod.mk.injEq] using hp
  subst hrhs
  obtain ⟨t', ht, hrest⟩ := MatchList.eq_leaf_cons hm
  have hnil : t' = [] := MatchList.eq_nil hrest
  subst hnil; subst ht
  simp_all [H, Tree.yield_node, Tree.yieldForest_cons, Tree.yield_leaf]

/-- `b ∉ ⟦H⟧` as well. -/
theorem not_language_H_b : ¬ H.language [b] := by
  intro h
  obtain ⟨ts, hv, hy⟩ := H.language_iff_tree [b] |>.mp h
  obtain ⟨rhs, hp, hm⟩ := hv
  have hrhs : rhs = [tok c] := by
    simpa [H, Prod.mk.injEq] using hp
  subst hrhs
  obtain ⟨t', ht, hrest⟩ := MatchList.eq_leaf_cons hm
  have hnil : t' = [] := MatchList.eq_nil hrest
  subst hnil; subst ht
  simp_all [H, Tree.yield_node, Tree.yieldForest_cons, Tree.yield_leaf]

end Counterexamples

section Computations

#eval G.nonterminals
#eval G.terminals
#eval yield tree_ab
#eval yield tree_bb
#eval yield tree_eps
#eval H.rhsOf u

end Computations


/-- A concatenation is empty only if both parts are. -/
theorem eq_nil_of_append_eq_nil {α : Type} {as bs : List α} (h : as ++ bs = []) :
    as = [] ∧ bs = [] := by
  cases as with
  | nil => exact ⟨rfl, by simpa using h⟩
  | cons a rest => exact absurd h (by simp)

section Nullable

/-- The example grammar is finite, so the Phase 4 analyses can run on it. -/
instance : FiniteEnum Tok where
  elems := [a, b, c]
  complete := by
    intro x
    cases x <;> simp

instance : FiniteEnum Var where
  elems := [s, p, q, u]
  complete := by
    intro x
    cases x <;> simp

/-- `p ⇒ ε\' and `q ⇒ ε\' are derivations of the empty word. -/
theorem nullable_spec_p : G.Nullable p := derives_production p [] mem_pe
theorem nullable_spec_q : G.Nullable q := derives_production q [] mem_qe

/-- `s ⇒ p q ⇒ ε q ⇒ ε\': the start symbol is nullable, through two ε-productions. -/
theorem nullable_spec_s : G.Nullable s := by
  refine derives_trans (derives_production s [var p, var q] mem_sq) ?_
  have h1 : Derives G [var p] [] := derives_production p [] mem_pe
  have h2 : Derives G [var q] [] := derives_production q [] mem_qe
  simpa using derives_append h1 h2

/-- The computed set agrees with the specification. -/
theorem nullable_p : G.nullable p = true := (nullable_iff G p).mpr nullable_spec_p
theorem nullable_q : G.nullable q = true := (nullable_iff G q).mpr nullable_spec_q
theorem nullable_s : G.nullable s = true := (nullable_iff G s).mpr nullable_spec_s

/-- `u\' occurs in the enumeration but has no production: nothing can be derived from it
except itself. -/
theorem forms_u : ∀ ys, Derives G [Sym.var u] ys → ys = [Sym.var u] := by
  intro ys h
  induction h with
  | refl => rfl
  | @tail mid fin hrec hstep ih =>
      subst ih
      obtain ⟨B, rhs, pre, post, hp, e1, e2⟩ := derives1_decompose hstep
      -- `[var u] = pre ++ var B :: post\' forces `pre = []\', `B = u\', `post = []\'
      have hpre : pre = [] := by
        cases pre with
        | nil => rfl
        | cons a as' =>
            rw [List.cons_append] at e1
            obtain ⟨ha, hrest⟩ := List.cons.inj e1
            subst ha
            obtain ⟨_, h4⟩ := eq_nil_of_append_eq_nil hrest.symm
            exact absurd h4 (by simp)
      subst hpre
      rw [List.nil_append] at e1
      obtain ⟨hBu, hpost⟩ := List.cons.inj e1
      subst hpost
      cases hBu
      -- now `B` is `u`
      -- but `u\' has no production at all
      exact absurd hp (by simp [G, List.mem_cons])

/-- `u' is *not* nullable, and the computation knows it. -/
theorem not_nullable_u : ¬ (G.nullable u = true) := by
  intro h
  have hspec : G.Nullable u := (nullable_iff G u).mp h
  have h1 : ([] : List (Sym Tok Var)) = [Sym.var u] := forms_u [] hspec
  exact absurd h1 (by simp)

/-- The computed NULLABLE set of the example grammar: exactly `s, p, q'. -/
theorem nullableSet_eq : G.nullableSet = [s, p, q] := by
  unfold Grammar.nullableSet
  decide

#eval G.nullableSet

end Nullable
section First

/-- `p ⇒ a': `a' is in the FIRST of `p'. -/
theorem first_p_a : G.first (Sym.var p) (LTok.tok a) = true :=
  (first_iff G _ _).mpr ⟨[], derives_production p [tok a] mem_pa⟩

/-- `q ⇒ b q': `b' is in the FIRST of `q'. -/
theorem first_q_b : G.first (Sym.var q) (LTok.tok b) = true :=
  (first_iff G _ _).mpr ⟨[Sym.var q], derives_production q [tok b, var q] mem_qbq⟩

/-- `s ⇒ p q ⇒ q ⇒ b q ⇒ b': the token comes from `q' because `p' is nullable. -/
theorem first_s_b : G.first (Sym.var s) (LTok.tok b) = true := by
  refine (first_iff G _ _).mpr ⟨[Sym.var q], ?_⟩
  have h1 : Derives G [Sym.var s] [Sym.var p, Sym.var q] :=
    derives_production s [var p, var q] mem_sq
  have h2 : Derives G [Sym.var p, Sym.var q] [Sym.tok b, Sym.var q] :=
    derives_append (derives_production p [] mem_pe)
      (derives_production q [tok b, var q] mem_qbq)
  exact derives_trans h1 h2

/-- `eof' is in the FIRST of `p' because `p ⇒ ε'. -/
theorem first_p_eof : G.first (Sym.var p) LTok.eof = true :=
  (first_eof_iff_nullable G _).mpr (derives_production p [] mem_pe)

/-- `u ⇒ c' is the only production of `u': `eof' is *not* in its FIRST. -/
theorem first_u_not_eof : ¬ (G.first (Sym.var u) LTok.eof = true) := by
  intro h
  have hspec : Derives G [Sym.var u] [] := (first_eof_iff_nullable G _).mp h
  have h1 : ([] : List (Sym Tok Var)) = [Sym.var u] := forms_u [] hspec
  exact absurd h1 (by simp)
/-- The computed FIRST relation of the example grammar, as a finite list of pairs. -/
def firstPairs : List (Sym Tok Var × LTok Tok) :=
  (FiniteEnum.elems (α := Sym Tok Var × LTok Tok)).filter
    (fun p => G.first p.1 p.2)

#eval firstPairs

end First
end VerifiedLL1.Examples.Toy
