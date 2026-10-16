/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Derivation

/-!
# Phase 1.6 — leftmost derivations

A predictive (LL) parser never chooses freely *which* nonterminal to expand: it
always expands the leftmost one.  So the theorem that will connect a parser to the
grammar semantics is not "the parser's output has *a* derivation" but "the parser's
output has a **leftmost** derivation".  This module establishes the semantic side of
that fact, still without any parser:

```lean
(∃ ts, Valid G (node A ts) ∧ yield (node A ts) = ws) ↔ LeftDerives G [var A] (toks ws)
```

Composing this with `tree_iff_derives` yields the classical **leftmost-derivation
lemma** — every derivable word has a leftmost derivation (`derives_iff_leftDerives`)
— proved here by reordering through parse trees rather than by a delicate induction
on derivations.

## Design note

A leftmost step is written as `toks ws ++ var A :: post ⇒ toks ws ++ rhs ++ post`:
the terminal prefix is given as a *word* `ws`, so "everything to the left of the
rewritten nonterminal is a terminal" is true by construction and needs no side
condition.  The two context lemmas then come out asymmetric, which is exactly the
asymmetry of leftmost derivation itself:

* a **right** context is always admissible (`leftDerives_rightCtx`);
* a **left** context is admissible only if it is terminal (`leftDerives_leftCtxToks`).
-/

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v} {G : Grammar T N}

/-- One leftmost derivation step: the leftmost nonterminal of the sentential form is
expanded. -/
inductive DerivesLeft1 (G : Grammar T N) : List (Sym T N) → List (Sym T N) → Prop where
  | step : ∀ {ws A rhs post}, (A, rhs) ∈ G.productions →
      DerivesLeft1 G (toks ws ++ Sym.var A :: post) (toks ws ++ rhs ++ post)

/-- Leftmost derivation: the reflexive-transitive closure of `DerivesLeft1`. -/
inductive LeftDerives (G : Grammar T N) : List (Sym T N) → List (Sym T N) → Prop where
  | refl (xs : List (Sym T N)) : LeftDerives G xs xs
  | tail : ∀ {xs ys zs}, LeftDerives G xs ys → DerivesLeft1 G ys zs → LeftDerives G xs zs

section LeftAPI

theorem leftDerives_refl (xs : List (Sym T N)) : LeftDerives G xs xs := LeftDerives.refl xs

theorem leftDerives_single (h : DerivesLeft1 G xs ys) : LeftDerives G xs ys :=
  LeftDerives.tail (LeftDerives.refl xs) h

theorem leftDerives_trans (h : LeftDerives G xs ys) (h' : LeftDerives G ys zs) :
    LeftDerives G xs zs := by
  induction h' with
  | refl => exact h
  | tail h2 hstep ih => exact LeftDerives.tail ih hstep

/-- Every leftmost step expands the leftmost nonterminal, after a terminal prefix. -/
theorem derivesLeft1_decompose (h : DerivesLeft1 G xs ys) :
    ∃ ws A rhs post, (A, rhs) ∈ G.productions
      ∧ xs = toks ws ++ Sym.var A :: post ∧ ys = toks ws ++ rhs ++ post := by
  cases h with
  | @step ws A rhs post hp => exact ⟨ws, A, rhs, post, hp, rfl, rfl⟩

/-- A right context is always admissible for a leftmost step. -/
theorem derivesLeft1_rightCtx (h : DerivesLeft1 G xs ys) (zs : List (Sym T N)) :
    DerivesLeft1 G (xs ++ zs) (ys ++ zs) := by
  cases h with
  | @step ws A rhs post hp =>
      have key := DerivesLeft1.step (ws := ws) (post := post ++ zs) hp
      simpa [List.append_assoc] using key

theorem leftDerives_rightCtx (h : LeftDerives G xs ys) (zs : List (Sym T N)) :
    LeftDerives G (xs ++ zs) (ys ++ zs) := by
  induction h with
  | refl => exact leftDerives_refl _
  | tail h' hstep ih => exact LeftDerives.tail ih (derivesLeft1_rightCtx hstep zs)

/-- A *terminal* left context is admissible for a leftmost step. -/
theorem derivesLeft1_leftCtxToks (h : DerivesLeft1 G xs ys) (ws' : List T) :
    DerivesLeft1 G (toks ws' ++ xs) (toks ws' ++ ys) := by
  cases h with
  | @step ws A rhs post hp =>
      have key := DerivesLeft1.step (ws := ws' ++ ws) (post := post) hp
      simp only [toks_append, List.append_assoc] at key ⊢
      exact key

theorem leftDerives_leftCtxToks (h : LeftDerives G xs ys) (ws' : List T) :
    LeftDerives G (toks ws' ++ xs) (toks ws' ++ ys) := by
  induction h with
  | refl => exact leftDerives_refl _
  | tail h' hstep ih =>
      exact LeftDerives.tail ih (derivesLeft1_leftCtxToks hstep ws')

/-- A nonterminal derives, leftmost, each of its right-hand sides. -/
theorem leftDerives_production (A : N) (rhs : List (Sym T N))
    (hp : (A, rhs) ∈ G.productions) : LeftDerives G [Sym.var A] rhs := by
  have key : DerivesLeft1 G (toks ([] : List T) ++ Sym.var A :: []) (toks [] ++ rhs ++ []) :=
    DerivesLeft1.step (ws := []) (post := []) hp
  exact leftDerives_single (by simpa [toks] using key)

end LeftAPI

section LeftCorrespondence

/-- **Downwards transport, leftmost.** -/
theorem matchList_leftDerives : ∀ {rhs ts}, MatchList G rhs ts →
    LeftDerives G rhs (toks (Tree.yieldForest ts)) := by
  intro rhs ts h
  induction h with
  | nil => exact LeftDerives.refl []
  | @tok rhs ts t hrec ih =>
      have := leftDerives_leftCtxToks ih [t]
      simpa [toks, List.map_cons, Tree.yieldForest_cons, Tree.yield_leaf] using this
  | @var rhs ts A ts' rhsA hp hchild hrest ihchild ihrest =>
      -- `var A :: rhs ⇒ rhsA ++ rhs ⇒* toks (yield ts') ++ rhs ⇒* toks (…) ++ toks (…)'
      have h1 : LeftDerives G (Sym.var A :: rhs) (rhsA ++ rhs) :=
        leftDerives_rightCtx (leftDerives_production A rhsA hp) rhs
      have h2 : LeftDerives G (rhsA ++ rhs) (toks (Tree.yieldForest ts') ++ rhs) :=
        leftDerives_rightCtx ihchild rhs
      have h3 : LeftDerives G (toks (Tree.yieldForest ts') ++ rhs)
          (toks (Tree.yieldForest ts') ++ toks (Tree.yieldForest ts)) :=
        leftDerives_leftCtxToks ihrest (Tree.yieldForest ts')
      have h4 : LeftDerives G (Sym.var A :: rhs)
          (toks (Tree.yieldForest ts') ++ toks (Tree.yieldForest ts)) :=
        leftDerives_trans (leftDerives_trans h1 h2) h3
      simpa [Tree.yieldForest_cons, Tree.yield_node, toks, List.map_append] using h4

/-- **Soundness, leftmost form.** -/
theorem valid_leftDerives {A : N} {ts : List (Tree T N)} (h : Valid G (Tree.node A ts)) :
    LeftDerives G [Sym.var A] (toks (Tree.yield (Tree.node A ts))) := by
  obtain ⟨rhs, hp, hm⟩ := h
  have h1 : LeftDerives G [Sym.var A] rhs := leftDerives_production A rhs hp
  have h2 : LeftDerives G rhs (toks (Tree.yieldForest ts)) := matchList_leftDerives hm
  simpa [Tree.yield_node] using leftDerives_trans h1 h2

/-- **Upwards transport, leftmost.** -/
theorem substitute_left (h : LeftDerives G xs ys) : ∀ {ts : List (Tree T N)},
    MatchList G ys ts → ∃ ts', MatchList G xs ts' ∧ Tree.yieldForest ts' = Tree.yieldForest ts := by
  induction h with
  | refl => intro ts hm; exact ⟨ts, hm, rfl⟩
  | tail h' hstep ih =>
      intro ts hm
      cases hstep with
      | @step ws A rhs post hp =>
          -- hm : MatchList G (toks ws ++ (rhs ++ post)) ts
          simp only [List.append_assoc] at hm
          obtain ⟨t0, trest, heq, h0, hrest⟩ := MatchList.split (toks ws) (rhs ++ post) ts hm
          obtain ⟨tA, tpost, heq2, hA, hpost⟩ := MatchList.split rhs post trest hrest
          subst heq2
          have hmid : MatchList G (Sym.var A :: post) (Tree.node A tA :: tpost) :=
            MatchList.var hp hA hpost
          have hys := MatchList.append h0 hmid
          obtain ⟨ts', hts', hy⟩ := ih hys
          refine ⟨ts', hts', ?_⟩
          subst heq
          rw [hy]
          simp [Tree.yieldForest_append, Tree.yield_node]

/-- **Completeness, leftmost form.** -/
theorem leftDerives_valid {A : N} {ws : List T} (h : LeftDerives G [Sym.var A] (toks ws)) :
    ∃ ts, Valid G (Tree.node A ts) ∧ Tree.yield (Tree.node A ts) = ws := by
  obtain ⟨ts', hm, hy⟩ := substitute_left h (MatchList.match_toks ws)
  obtain ⟨t, rhsA, rest, hts, hp, hchild, hrest⟩ := MatchList.eq_node_cons hm
  have hnil : rest = [] := MatchList.eq_nil hrest
  subst hnil
  refine ⟨t, Valid.mk hp hchild, ?_⟩
  rw [hts, Tree.yieldForest_map_leaf] at hy
  simpa [hts] using hy

/--
**Parse trees ↔ leftmost derivations.**  Together with `tree_iff_derives` this is
the leftmost-derivation lemma. -/
theorem tree_iff_leftDerives {A : N} {ws : List T} :
    (∃ ts, Valid G (Tree.node A ts) ∧ Tree.yield (Tree.node A ts) = ws) ↔
      LeftDerives G [Sym.var A] (toks ws) := by
  constructor
  · rintro ⟨ts, hv, hy⟩
    subst hy
    exact valid_leftDerives hv
  · intro h
    exact leftDerives_valid h

/--
**Leftmost-derivation lemma.**  Every derivable terminal word is *leftmost*
derivable.  This is not an extra assumption about the grammar: it is a theorem, and
it is what makes the Phase 3 completeness proof for a predictive parser possible
without assuming the parser is complete. -/
theorem derives_iff_leftDerives {A : N} {ws : List T} :
    Derives G [Sym.var A] (toks ws) ↔ LeftDerives G [Sym.var A] (toks ws) := by
  constructor
  · intro h; exact tree_iff_leftDerives.mp (derives_valid h)
  · intro h; exact tree_iff_derives.mp (leftDerives_valid h)

/-- Leftmost derivations are derivations (the forgetful direction, for later use). -/
theorem leftDerives_imp_derives {xs ys} (h : LeftDerives G xs ys) : Derives G xs ys := by
  induction h with
  | refl => exact derives_refl _
  | tail h' hstep ih =>
      obtain ⟨ws, A, rhs, post, hp, rfl, rfl⟩ := derivesLeft1_decompose hstep
      exact derives_trans ih (derives_single (Derives1.step (pre := toks ws) (post := post) hp))

end LeftCorrespondence

end VerifiedLL1
