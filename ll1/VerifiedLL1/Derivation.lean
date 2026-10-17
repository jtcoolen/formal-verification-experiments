/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.ParseTree

/-!
# Phase 1.3 — The derivation relation and its correspondence with parse trees

## The relations

`Derives1 G xs ys` is the *one-step* derivation relation: `ys` is obtained from
`xs` by replacing one occurrence of a nonterminal `A` by the right-hand side of
one of its productions.  `Derives G` is its reflexive-transitive closure, defined
here rather than through a generic closure so that the induction principle has
exactly the shape the correspondence proofs want (the last step exposed).

## The correspondence

The two directions are proved through two "transport" lemmas:

* `matchList_derives` (downwards): a matched forest can be derived from the
  symbol list it matches.
* `substitute` (upwards): along a derivation, any valid expansion of the reduct
  lifts to a valid expansion of the source with the *same yield*.  This is the
  key invariant: it says the tree structure is insensitive to the order in which
  the nonterminals of a sentential form are expanded, which is precisely why
  parse trees abstract over derivations.

Applying `substitute` to a derivation that ends in the purely terminal form
`toks ws` — expanded by the trivial forest `ws.map leaf` — gives completeness;
`matchList_derives` gives soundness.

## Why these statements are the strong ones

It would be easy to state a weaker "the parser's output is a tree" theorem.
Instead we prove, for every grammar `G`, nonterminal `A` and word `ws`:

```lean
(∃ ts, Valid G (node A ts) ∧ yield (node A ts) = ws) ↔ Derives G [var A] (toks ws)
```

The right-hand side mentions only the grammar; the left-hand side mentions only
parse trees.  Neither side mentions any algorithm, so this is a genuine semantic
characterisation.  `derives_toks_inj` additionally shows the relation is not
"junky": a derivation can never alter a terminal word.
-/

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v} {G : Grammar T N}

/-- One-step derivation: replace one occurrence of a nonterminal by the
right-hand side of one of its productions. -/
inductive Derives1 (G : Grammar T N) : List (Sym T N) → List (Sym T N) → Prop where
  | step : ∀ {A rhs pre post}, (A, rhs) ∈ G.productions →
      Derives1 G (pre ++ Sym.var A :: post) (pre ++ rhs ++ post)

/-- Derivation: the reflexive-transitive closure of `Derives1`. -/
inductive Derives (G : Grammar T N) : List (Sym T N) → List (Sym T N) → Prop where
  | refl (xs : List (Sym T N)) : Derives G xs xs
  | tail : ∀ {xs ys zs}, Derives G xs ys → Derives1 G ys zs → Derives G xs zs

section API

theorem derives_refl (xs : List (Sym T N)) : Derives G xs xs := Derives.refl xs

theorem derives_single (h : Derives1 G xs ys) : Derives G xs ys :=
  Derives.tail (Derives.refl xs) h

theorem derives_trans (h : Derives G xs ys) (h' : Derives G ys zs) : Derives G xs zs := by
  induction h' with
  | refl => exact h
  | tail h2 hstep ih => exact Derives.tail ih hstep

/-- Every one-step derivation rewrites exactly one nonterminal occurrence. -/
theorem derives1_decompose (h : Derives1 G xs ys) :
    ∃ A rhs pre post, (A, rhs) ∈ G.productions
      ∧ xs = pre ++ Sym.var A :: post ∧ ys = pre ++ rhs ++ post := by
  cases h with
  | @step A rhs pre post hp => exact ⟨A, rhs, pre, post, hp, rfl, rfl⟩

theorem derives1_cons (h : Derives1 G xs ys) (x : Sym T N) : Derives1 G (x :: xs) (x :: ys) := by
  cases h with
  | @step A rhs pre post hp => exact Derives1.step (pre := x :: pre) (post := post) hp

/-- Derivations are stable under arbitrary context. -/
theorem derives1_ctx (h : Derives1 G xs ys) (l r : List (Sym T N)) :
    Derives1 G (l ++ xs ++ r) (l ++ ys ++ r) := by
  cases h with
  | @step A rhs pre post hp =>
      have key := Derives1.step (pre := l ++ pre) (post := post ++ r) hp
      simpa [List.append_assoc] using key

theorem derives_ctx (h : Derives G xs ys) (l r : List (Sym T N)) :
    Derives G (l ++ xs ++ r) (l ++ ys ++ r) := by
  induction h with
  | refl => exact derives_refl _
  | tail h' hstep ih => exact Derives.tail ih (derives1_ctx hstep l r)

/-- Derivations are stable under prefixing a fixed context. -/
theorem derives_prefix (h : Derives G xs ys) (l : List (Sym T N)) :
    Derives G (l ++ xs) (l ++ ys) := by
  simpa [List.append_nil] using derives_ctx h l []

/-- **Head inversion.**  A non-trivial derivation can be split at its *first* step.
This is the mirror image of the inductive definition (which peels the last step) and is
what makes "look at the production used first" arguments available. -/
theorem derives_head_inv {xs ys : List (Sym T N)} (h : Derives G xs ys) (hne : xs ≠ ys) :
    ∃ zs, Derives1 G xs zs ∧ Derives G zs ys := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail mid fin hrec hstep ih =>
      by_cases hmid : xs = mid
      · subst hmid
        exact ⟨fin, hstep, derives_refl fin⟩
      · obtain ⟨zs, h1, h2⟩ := ih hmid
        exact ⟨zs, h1, Derives.tail h2 hstep⟩

/-- The first step of a derivation from a single nonterminal uses one of its
productions. -/
theorem derives_head_var {A : N} {ys : List (Sym T N)} (h : Derives G [Sym.var A] ys)
    (hne : ys ≠ [Sym.var A]) :
    ∃ rhs, (A, rhs) ∈ G.productions ∧ Derives G rhs ys := by
  obtain ⟨zs, h1, h2⟩ := derives_head_inv h (fun heq => absurd heq.symm hne)
  obtain ⟨B, rhs, pre, post, hp, e1, e2⟩ := derives1_decompose h1
  -- `[var A] = pre ++ var B :: post\' forces `pre = []\', `post = []\' and `B = A\'
  have hpre : pre = [] := by
    cases pre with
    | nil => rfl
    | cons a as =>
        rw [List.cons_append] at e1
        obtain ⟨_, hrest⟩ := List.cons.inj e1
        exact absurd hrest (by simp)
  subst hpre
  rw [List.nil_append] at e1
  obtain ⟨hAB, hpost⟩ := List.cons.inj e1
  subst hpost
  have hBA : B = A := by
    cases hAB
    rfl
  subst hBA
  rw [List.nil_append, List.append_nil] at e2
  exact ⟨rhs, hp, e2 ▸ h2⟩

theorem derives_cons (h : Derives G xs ys) (x : Sym T N) : Derives G (x :: xs) (x :: ys) := by
  have := derives_ctx h [x] []
  simpa using this

theorem derives_append (h : Derives G xs ys) (h' : Derives G xs' ys') :
    Derives G (xs ++ xs') (ys ++ ys') := by
  have h1 := derives_ctx h [] xs'
  have h2 := derives_ctx h' ys []
  simp only [List.nil_append, List.append_nil] at h1 h2
  exact derives_trans h1 h2

/-- A nonterminal derives the right-hand side of each of its productions. -/
theorem derives_production (A : N) (rhs : List (Sym T N)) (hp : (A, rhs) ∈ G.productions) :
    Derives G [Sym.var A] rhs := by
  have key : Derives1 G (([] : List (Sym T N)) ++ Sym.var A :: []) ([] ++ rhs ++ []) :=
    Derives1.step hp
  exact derives_single (by simpa using key)

end API

section NoJunk

/-- No terminal word contains a nonterminal. -/
theorem var_notin_toks (A : N) : ∀ (ws : List T), Sym.var A ∉ (toks ws : List (Sym T N)) := by
  intro ws
  induction ws with
  | nil => intro h; exact absurd h (by simp [toks])
  | cons w rest ih =>
      intro h
      simp only [toks, List.map_cons] at h
      rw [List.mem_cons] at h
      rcases h with hhead | htail
      · exact Sym.ne_tok_var w A hhead.symm
      · exact ih htail

/-- A one-step derivation from a variable-free sentential form does nothing. -/
theorem derives1_noVar (h : Derives1 G xs ys) (hnov : ∀ s ∈ xs, s.isVar = false) : xs = ys := by
  obtain ⟨A, rhs, pre, post, hp, rfl, rfl⟩ := derives1_decompose h
  have hmem : Sym.var A ∈ pre ++ (Sym.var A :: post) :=
    List.mem_append.mpr (Or.inr List.mem_cons_self)
  have : (Sym.var A).isVar = false := hnov _ hmem
  simp at this

/-- A derivation from a variable-free sentential form does nothing. -/
theorem derives_noVar (h : Derives G xs ys) (hnov : ∀ s ∈ xs, s.isVar = false) : xs = ys := by
  induction h with
  | refl => rfl
  | tail h' hstep ih =>
      -- `ih` identifies the intermediate sentential form with `xs`; substituting it
      -- makes the one-step hypothesis directly applicable.
      subst ih
      exact derives1_noVar hstep hnov

/-- **No junk.**  A derivation between two terminal words is trivial. -/
theorem derives_toks_inj : ∀ {ws vs : List T}, Derives G (toks ws) (toks vs) → ws = vs := by
  intro ws vs h
  have hnov : ∀ s ∈ (toks ws : List (Sym T N)), s.isVar = false := by
    intro s hs
    rw [toks, List.mem_map] at hs
    obtain ⟨w, _, hs⟩ := hs
    exact hs ▸ rfl
  exact toks_inj (derives_noVar h hnov)

end NoJunk

section Correspondence

/-- **Downwards transport.**  If the forest `ts` validly expands `rhs`, then
`rhs` derives the terminal word yielded by `ts`. -/
theorem matchList_derives : ∀ {rhs : List (Sym T N)} {ts : List (Tree T N)},
    MatchList G rhs ts → Derives G rhs (toks (Tree.yieldForest ts)) := by
  intro rhs ts h
  induction h with
  | nil => exact Derives.refl []
  | @tok rhs ts t hrec ih =>
      simp only [Tree.yieldForest_cons, Tree.yield_leaf, toks]
      exact derives_cons ih (Sym.tok t)
  | @var rhs ts A ts' rhsA hp hchild hrest ihchild ihrest =>
      have h1 : Derives G (Sym.var A :: rhs) (rhsA ++ rhs) := by
        have := derives_ctx (derives_production A rhsA hp) [] rhs
        simpa using this
      have h2 : Derives G (rhsA ++ rhs)
          (toks (Tree.yieldForest ts') ++ toks (Tree.yieldForest ts)) :=
        derives_append ihchild ihrest
      have h3 : Derives G (Sym.var A :: rhs)
          (toks (Tree.yieldForest ts') ++ toks (Tree.yieldForest ts)) :=
        derives_trans h1 h2
      simpa [Tree.yieldForest_cons, Tree.yield_node, Tree.yield_leaf, toks, List.map_append,
        List.map_cons] using h3

/-- **Soundness of parse trees.**  A valid parse tree rooted at `A` yields a word
derivable from `A`. -/
theorem valid_derives {A : N} {ts : List (Tree T N)} (h : Valid G (Tree.node A ts)) :
    Derives G [Sym.var A] (toks (Tree.yield (Tree.node A ts))) := by
  obtain ⟨rhs, hp, hm⟩ := h
  have h1 : Derives G [Sym.var A] rhs := derives_production A rhs hp
  have h2 : Derives G rhs (toks (Tree.yieldForest ts)) := matchList_derives hm
  simpa [Tree.yield_node] using derives_trans h1 h2

/-- **Upwards transport.**  Along a derivation, every valid expansion of the
reduct lifts to a valid expansion of the source with the same yield. -/
theorem substitute (h : Derives G xs ys) : ∀ {ts : List (Tree T N)},
    MatchList G ys ts → ∃ ts', MatchList G xs ts' ∧ Tree.yieldForest ts' = Tree.yieldForest ts := by
  induction h with
  | refl => intro ts hm; exact ⟨ts, hm, rfl⟩
  | tail h' hstep ih =>
      intro ts hm
      cases hstep with
      | @step A rhs pre post hp =>
          simp only [List.append_assoc] at hm
          obtain ⟨t1, t23, heq, h1, h23⟩ := MatchList.split pre (rhs ++ post) ts hm
          obtain ⟨t2, t3, heq2, h2, h3⟩ := MatchList.split rhs post t23 h23
          subst heq2
          have hmid : MatchList G (Sym.var A :: post) (Tree.node A t2 :: t3) :=
            MatchList.var hp h2 h3
          have hys := MatchList.append h1 hmid
          obtain ⟨ts', hts', hy⟩ := ih hys
          refine ⟨ts', hts', ?_⟩
          subst heq
          rw [hy]
          simp [Tree.yieldForest_append, Tree.yield_node]

/-- **Completeness of parse trees.**  Every derivation of a terminal word from
`A` is realised by a valid parse tree rooted at `A` with that yield. -/
theorem derives_valid {A : N} {ws : List T} (h : Derives G [Sym.var A] (toks ws)) :
    ∃ ts, Valid G (Tree.node A ts) ∧ Tree.yield (Tree.node A ts) = ws := by
  obtain ⟨ts', hm, hy⟩ := substitute h (MatchList.match_toks ws)
  obtain ⟨t, rhsA, rest, hts, hp, hchild, hrest⟩ := MatchList.eq_node_cons hm
  have hnil : rest = [] := MatchList.eq_nil hrest
  subst hnil
  refine ⟨t, Valid.mk hp hchild, ?_⟩
  rw [hts, Tree.yieldForest_map_leaf] at hy
  simpa [Tree.yieldForest_cons, Tree.yield_node] using hy

/-- **Forest completeness.**  Every derivation of a terminal word from an *arbitrary*
sentential form is realised by a forest of valid subtrees matching that form.  This is
the generalisation of `derives_valid` that the LL(1) argument needs: the parser's stack
continuation is not a single nonterminal. -/
theorem derives_forest {xs : List (Sym T N)} {ws : List T} (h : Derives G xs (toks ws)) :
    ∃ ts, MatchList G xs ts ∧ Tree.yieldForest ts = ws := by
  obtain ⟨ts, hm, hy⟩ := substitute h (MatchList.match_toks ws)
  exact ⟨ts, hm, by simpa using hy⟩
/--
**Phase 1 main theorem — correspondence between valid parse trees and grammar
derivations.**  For every grammar, every nonterminal and every terminal word, the
existence of a valid parse tree rooted at `A` with yield `ws` is equivalent to
`A` deriving `ws`.  Neither side mentions any algorithm. -/
theorem tree_iff_derives {A : N} {ws : List T} :
    (∃ ts, Valid G (Tree.node A ts) ∧ Tree.yield (Tree.node A ts) = ws) ↔
      Derives G [Sym.var A] (toks ws) := by
  constructor
  · rintro ⟨ts, hv, hy⟩
    subst hy
    exact valid_derives hv
  · intro h
    exact derives_valid h

/-- The **language** of a grammar: the terminal words derivable from its start
symbol. -/
def Grammar.language (G : Grammar T N) (ws : List T) : Prop :=
  Derives G [Sym.var G.start] (toks ws)

/-- The language, characterised by parse trees instead of derivations. -/
theorem Grammar.language_iff_tree (G : Grammar T N) (ws : List T) :
    G.language ws ↔ ∃ ts, Valid G (Tree.node G.start ts) ∧ Tree.yield (Tree.node G.start ts) = ws :=
  (@tree_iff_derives (G := G) (A := G.start) (ws := ws)).symm

end Correspondence

end VerifiedLL1
