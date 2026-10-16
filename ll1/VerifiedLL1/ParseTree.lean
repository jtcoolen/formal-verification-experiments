/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Grammar

/-!
# Phase 1.2 — Parse trees, their yield, and their validity

## Design notes

A parse tree is an ordered rooted tree whose internal nodes are labelled by
nonterminals and whose leaves are terminals:

```lean
inductive Tree T N where
  | leaf : T → Tree T N
  | node : N → List (Tree T N) → Tree T N
```

Tradeoffs of this representation:

* **Not indexed by the root nonterminal.**  An indexed type `Tree A` would make
  "this tree is rooted at `A`" free, but every node would then need a
  length-indexed vector of children whose types depend on the *chosen*
  production — a dependent heterogeneous list.  That buys little here: the root
  label is carried by the constructor, and every theorem we want (`yield`,
  `Valid`, the correspondence with derivations) is a statement *about* the label
  rather than something a type checker must enforce.  Keeping the representation
  simple means the Phase 2 parser can build trees without proving index
  arithmetic, and the proofs below stay first-order.
* **Productions are not recorded in the tree.**  A node stores only its label and
  its children; validity then *existentially* supplies the production that
  justifies it.  This is the right choice for a soundness statement: a parser is
  not required to report which production it guessed, and two identical subtrees
  justified by different productions are the same tree — which is what a user
  expects a parse tree to be.  Under the LL(1) condition of Phase 5 the
  production is in any case determined by the table entry.
* **A nonterminal position must be matched by a `node`, never by "nothing".**
  Consequently a nonterminal that derives `ε` is represented by `node A []`
  (using an epsilon production), never by an implicit skip.  Every validity
  proof therefore consumes exactly one production per node, which is what makes
  the termination argument of Phase 3 possible.
* **`MatchList` is a single non-mutual inductive.**  The naive presentation makes
  `Valid` and `MatchList` mutually recursive, and Lean's induction machinery for
  mutual propositions then forces a mutual proof script.  Instead `MatchList`
  inlines the node rule at a nonterminal position (it directly requires a
  production of `A` together with a match of its right-hand side), and `Valid`
  becomes a plain pattern-matching definition.  The two are equivalent — see
  `Valid.iff_mk` — and every induction below is a simple one-place induction.
-/

universe u v

namespace VerifiedLL1

/-- Parse trees over terminals `T` and nonterminals `N`. -/
inductive Tree (T : Type u) (N : Type v) where
  | leaf : T → Tree T N
  | node : N → List (Tree T N) → Tree T N
  deriving Repr, BEq

namespace Tree

variable {T : Type u} {N : Type v}

/-- The yield of a tree: its terminals, read left to right. -/
def yield : Tree T N → List T
  | leaf t => [t]
  | node _ ts => ts.flatMap yield

/-- The yield of a forest, i.e. of a list of trees. -/
def yieldForest (ts : List (Tree T N)) : List T := ts.flatMap yield

-- `Tree` is a *nested* inductive, so the defining equations of a structurally
-- recursive function on it are not definitional equalities; they are proved (and
-- registered as simp lemmas) below.
@[simp] theorem yield_leaf (t : T) : yield (leaf t : Tree T N) = [t] := by simp [yield]
@[simp] theorem yield_node (A : N) (ts : List (Tree T N)) :
    yield (node A ts) = yieldForest ts := by simp [yield, yieldForest]
@[simp] theorem yieldForest_nil : @yieldForest T N [] = [] := rfl
@[simp] theorem yieldForest_cons (t : Tree T N) (ts : List (Tree T N)) :
    yieldForest (t :: ts) = yield t ++ yieldForest ts := rfl

theorem yieldForest_append (ts us : List (Tree T N)) :
    yieldForest (ts ++ us) = yieldForest ts ++ yieldForest us := by
  induction ts with
  | nil => rfl
  | cons t rest ih => simp [yieldForest_cons, ih]

@[simp] theorem yieldForest_map_leaf (ws : List T) :
    yieldForest (ws.map leaf : List (Tree T N)) = ws := by
  induction ws with
  | nil => rfl
  | cons w rest ih => simp [List.map, yieldForest_cons, ih]

/-- The children of a tree. -/
def children : Tree T N → List (Tree T N)
  | leaf _ => []
  | node _ ts => ts

@[simp] theorem children_leaf (t : T) : children (leaf t : Tree T N) = [] := by simp [children]
@[simp] theorem children_node (A : N) (ts : List (Tree T N)) : children (node A ts) = ts := by
  simp [children]

/-- The root label of a tree, if it has one. -/
def root? : Tree T N → Option N
  | leaf _ => none
  | node A _ => some A

@[simp] theorem root?_leaf (t : T) : root? (leaf t : Tree T N) = none := by simp [root?]
@[simp] theorem root?_node (A : N) (ts : List (Tree T N)) : root? (node A ts) = some A := by
  simp [root?]

end Tree

/-- `MatchList G rhs ts` says the forest `ts` is a valid expansion of the symbol
list `rhs` in the grammar `G`:

* `[]` is matched only by `[]`;
* a terminal symbol `Sym.tok t` is matched only by the leaf `Tree.leaf t`;
* a nonterminal symbol `Sym.var A` is matched by a node `Tree.node A ts'` whose
  children `ts'` match the right-hand side of *some* production of `A`.
-/
inductive MatchList (G : Grammar T N) : List (Sym T N) → List (Tree T N) → Prop where
  | nil : MatchList G [] []
  | tok : ∀ {rhs ts t}, MatchList G rhs ts → MatchList G (Sym.tok t :: rhs) (Tree.leaf t :: ts)
  | var : ∀ {rhs ts A ts' rhsA}, (A, rhsA) ∈ G.productions → MatchList G rhsA ts' →
      MatchList G rhs ts → MatchList G (Sym.var A :: rhs) (Tree.node A ts' :: ts)

/-- `Valid G t`: `t` is a valid parse tree of `G`.  A bare leaf is never valid on
its own; a node is valid when its children match the right-hand side of one of
the productions of its label. -/
def Valid (G : Grammar T N) : Tree T N → Prop
  | Tree.leaf _ => False
  | Tree.node A ts => ∃ rhs, (A, rhs) ∈ G.productions ∧ MatchList G rhs ts

namespace MatchList

variable {T : Type u} {N : Type v} {G : Grammar T N}

/-- Matching preserves length. -/
@[simp] theorem length_eq {rhs : List (Sym T N)} {ts : List (Tree T N)} (h : MatchList G rhs ts) :
    rhs.length = ts.length := by
  induction h with
  | nil => rfl
  | tok _ ih => simp [ih]
  | var _ _ _ _ ih => simp [ih]

theorem eq_nil {ts : List (Tree T N)} (h : MatchList G [] ts) : ts = [] := by
  cases h with
  | nil => rfl

theorem eq_leaf_cons {t : T} {rhs ts} (h : MatchList G (Sym.tok t :: rhs) ts) :
    ∃ ts', ts = Tree.leaf t :: ts' ∧ MatchList G rhs ts' := by
  cases h with
  | tok hrest => exact ⟨_, rfl, hrest⟩

theorem eq_node_cons {A : N} {rhs ts} (h : MatchList G (Sym.var A :: rhs) ts) :
    ∃ ts' rhsA ts'', ts = Tree.node A ts' :: ts'' ∧ (A, rhsA) ∈ G.productions
      ∧ MatchList G rhsA ts' ∧ MatchList G rhs ts'' := by
  cases h with
  | var hp hchild hrest => exact ⟨_, _, _, rfl, hp, hchild, hrest⟩

/-- A forest of leaves matches a word viewed as a terminal sentential form. -/
theorem match_toks (ws : List T) : MatchList G (toks ws) (ws.map Tree.leaf) := by
  induction ws with
  | nil => exact MatchList.nil
  | cons w rest ih =>
      show MatchList G (Sym.tok w :: toks rest) (Tree.leaf w :: rest.map Tree.leaf)
      exact MatchList.tok ih

/-- The only forest matching a *terminal* sentential form is the forest of leaves. -/
theorem match_toks_unique {ws : List T} {ts : List (Tree T N)} (h : MatchList G (toks ws) ts) :
    ts = ws.map Tree.leaf := by
  induction ws generalizing ts with
  | nil => exact eq_nil h
  | cons w rest ih =>
      obtain ⟨ts', rfl, hrest⟩ := eq_leaf_cons h
      simp [ih hrest]

/-- Concatenation of matched forests. -/
theorem append {rhs rhs' : List (Sym T N)} {ts ts' : List (Tree T N)}
    (h : MatchList G rhs ts) (h' : MatchList G rhs' ts') :
    MatchList G (rhs ++ rhs') (ts ++ ts') := by
  induction h with
  | nil => simpa using h'
  | @tok rhs ts t hrec ih => exact MatchList.tok ih
  | @var rhs ts A ts' rhsA hp hchild hrest ihchild ihrest =>
      exact MatchList.var hp hchild ihrest

/-- Splitting: a forest matching a concatenation splits along that concatenation. -/
theorem split : ∀ (xs ys : List (Sym T N)) (ts : List (Tree T N)),
    MatchList G (xs ++ ys) ts →
      ∃ ts1 ts2, ts = ts1 ++ ts2 ∧ MatchList G xs ts1 ∧ MatchList G ys ts2 := by
  intro xs
  induction xs with
  | nil =>
      intro ys ts h
      exact ⟨[], ts, rfl, MatchList.nil, h⟩
  | cons x xs' ih =>
      intro ys ts h
      cases x with
      | tok t =>
          obtain ⟨ts', rfl, hrest⟩ := eq_leaf_cons h
          obtain ⟨a, b, heq, ha, hb⟩ := ih ys ts' hrest
          subst heq
          exact ⟨Tree.leaf t :: a, b, rfl, MatchList.tok ha, hb⟩
      | var A =>
          obtain ⟨ts', rhsA, b, rfl, hp, hchild, hrest⟩ := eq_node_cons h
          obtain ⟨a, c, heq, ha, hc⟩ := ih ys b hrest
          subst heq
          exact ⟨Tree.node A ts' :: a, c, rfl, MatchList.var hp hchild ha, hc⟩

/-- Every node occurring in a matched forest is valid. -/
theorem valid_of_mem {rhs ts : List _} (h : MatchList G rhs ts) {A : N} {ts' : List (Tree T N)}
    (ht : Tree.node A ts' ∈ ts) : Valid G (Tree.node A ts') := by
  induction h with
  | nil => exact absurd ht (by simp)
  | @tok rhs ts t hrec ih =>
      rw [List.mem_cons] at ht
      rcases ht with hhead | htail
      · exact absurd hhead (by simp)
      · exact ih htail
  | @var rhs ts B ts' rhsB hp hchild hrest ihchild ihrest =>
      rw [List.mem_cons] at ht
      rcases ht with hhead | htail
      · cases hhead
        exact ⟨rhsB, hp, hchild⟩
      · exact ihrest htail

end MatchList

namespace Valid

variable {T : Type u} {N : Type v} {G : Grammar T N}

theorem not_valid_leaf (t : T) : ¬ Valid G (Tree.leaf t) := by simp [Valid]

/-- A node whose children match a right-hand side of `A` is valid. -/
theorem mk {A : N} {ts : List (Tree T N)} {rhs : List (Sym T N)}
    (hp : (A, rhs) ∈ G.productions) (hm : MatchList G rhs ts) : Valid G (Tree.node A ts) :=
  ⟨rhs, hp, hm⟩

/-- The defining characterisation. -/
theorem iff_mk {A : N} {ts : List (Tree T N)} :
    Valid G (Tree.node A ts) ↔ ∃ rhs, (A, rhs) ∈ G.productions ∧ MatchList G rhs ts := Iff.rfl

/-- Inversion: a valid node carries a production and a matching forest. -/
theorem dest {A : N} {ts : List (Tree T N)} (h : Valid G (Tree.node A ts)) :
    ∃ rhs, (A, rhs) ∈ G.productions ∧ MatchList G rhs ts := h

/-- Validity is inherited by strict subtrees. -/
theorem subtree_valid {A : N} {ts : List (Tree T N)} (h : Valid G (Tree.node A ts))
    {B : N} {us : List (Tree T N)} (ht : Tree.node B us ∈ ts) : Valid G (Tree.node B us) := by
  obtain ⟨rhs, hp, hm⟩ := h
  exact MatchList.valid_of_mem hm ht

/-- A valid node has a production whose right-hand side has as many symbols as the
node has children. -/
theorem length_eq {A : N} {ts : List (Tree T N)} (h : Valid G (Tree.node A ts)) :
    ∃ rhs, (A, rhs) ∈ G.productions ∧ rhs.length = ts.length := by
  obtain ⟨rhs, hp, hm⟩ := h
  exact ⟨rhs, hp, hm.length_eq⟩

end Valid

end VerifiedLL1
