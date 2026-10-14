import Merkle.Proof

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Security bounds for Merkle trees

This file turns the qualitative claim "Merkle trees are collision resistant" into quantitative
bounds of two independent kinds.

## 1. Exact reductions (constructive, no probability)

Every attack on a tree is exhibited as a concrete collision in the hash algebra, together with
the witness that breaks it. There is no slack: the *only* way to break the scheme is to break
the algebra.

* `Collision` - the two ways an algebra can fail to be collision-free: two distinct messages
  with equal leaf digests, or two distinct digest pairs with equal node digests.
* `collision_or_eq` - **the main reduction**: equal roots imply the trees are equal *or* we can
  hand you a concrete collision. Decided without any classical case split.
* `collision_of_rootHash_eq`, `rootHash_ne_of_ne` - corollaries: distinct trees with equal
  roots refute collision-freeness; a collision-free algebra makes the root a perfect
  commitment.
* `Proof.verify_injective` - folding a fixed authentication path is injective on digests, so a
  proof cannot be used to mount a second-preimage attack.
* `accepting_value_unique` / `accepting_value_exists` - **the exact forgery count**: at each
  path exactly one value is accepted, no more and no less.

## 2. Counting bounds (no assumption on the hash at all)

* `length_allTrees` - there are exactly `2 ^ (2 ^ n)` distinct depth-`n` Boolean trees.
* `no_injection_trees` - any map from those trees into `Fin k` with `k < 2 ^ (2 ^ n)`
  identifies two distinct trees: a collision is *forced*.
* `digest_cannot_be_small` - consequently **no collision-free hash into a smaller digest set
  can exist**. This is the information-theoretic barrier behind the digest-size rule.
* `modThree_notInjective`, `no_injection_two_into_one` - the smallest concrete instances of
  the same obstruction.

## What is deliberately *not* claimed

A birthday bound (`~2^(k/2)` work for a `k`-bit digest) is a statement about the *expected
running time of a randomized algorithm*. Lean core has no probability theory, so this file
proves the deterministic counting facts a birthday argument would rest on, and stops short of
the probabilistic statement rather than faking it.
-/

namespace Merkle

section
variable {α β : Type}
variable {m : MerkleHash α β}

/-- **A concrete collision** in the hash algebra: evidence that the algebra is *not*
collision-free, packaged as a witness an adversary could publish.

The two constructors mirror the two operations the security proofs consume. A `Collision` is
exactly a refutation of those assumptions, so producing one is the only way to refute the
theorems of `Merkle/Proof.lean`. -/
inductive Collision : Prop where
  /-- Two distinct messages hash to the same leaf digest: `leafInjective` fails. -/
  | leaf : ∀ (a b : α), a ≠ b → m.leaf a = m.leaf b → Collision
  /-- Two distinct digest pairs combine to the same digest: `collFree` fails. -/
  | node : ∀ (a b c d : β), (a ≠ c ∨ b ≠ d) → m.node a b = m.node c d → Collision

/-- **The main reduction, constructively.** Two trees with the same root digest either are
distinct - in which case we hand you a concrete collision in the hash algebra - or they are
equal.

This is the constructive form of collision resistance: it does not merely say "if the hash is
collision-free then so is `rootHash`", it *exhibits* the collision by walking down to the
first level at which the two trees differ. Note that it decides `Collision ∨ t₁ = t₂` without
any classical case split on propositional equality, so the whole development stays constructive
apart from Lean's two standard proof-irrelevance axioms. -/
theorem collision_or_eq :
    ∀ (n : Nat) (t₁ t₂ : Tree α n), rootHash (m := m) t₁ = rootHash (m := m) t₂ →
      Collision (m := m) ∨ t₁ = t₂ := by
  intro n
  induction n with
  | zero =>
      intro t₁ t₂ heq
      cases t₁ with
      | leaf a =>
          cases t₂ with
          | leaf b => exact Or.inr (congrArg Tree.leaf (m.leafInjective heq))
  | succ n ih =>
      intro t₁ t₂ heq
      cases t₁ with
      | node l₁ r₁ =>
          cases t₂ with
          | node l₂ r₂ =>
              obtain ⟨hl, hr⟩ := m.collFree heq
              cases ih l₁ l₂ hl with
              | inl c => exact Or.inl c
              | inr e₁ =>
                  cases ih r₁ r₂ hr with
                  | inl c => exact Or.inl c
                  | inr e₂ => exact Or.inr (e₁ ▸ e₂ ▸ rfl)

/-- **The main reduction.** Two *distinct* trees with the same root digest yield a concrete
collision in the hash algebra: the left disjunct of `collision_or_eq`. -/
theorem collision_of_rootHash_eq :
    ∀ (n : Nat) (t₁ t₂ : Tree α n), rootHash (m := m) t₁ = rootHash (m := m) t₂ →
      t₁ ≠ t₂ → Collision (m := m) := by
  intro n t₁ t₂ heq hne
  cases collision_or_eq n t₁ t₂ heq with
  | inl c => exact c
  | inr h => exact absurd h hne

/-- **Collision resistance of `rootHash`.** If the algebra admits no collision then two
*distinct* trees have *distinct* roots: the root digest is a perfect commitment to the whole
tree, and nothing can be swapped inside it without the root noticing. -/
theorem rootHash_ne_of_ne :
    ∀ (n : Nat) (t₁ t₂ : Tree α n), ¬ Collision (m := m) →
      t₁ ≠ t₂ → rootHash (m := m) t₁ ≠ rootHash (m := m) t₂ := by
  intro n t₁ t₂ hnc hne heq
  exact hnc (collision_of_rootHash_eq n t₁ t₂ heq hne)

end


/-! ## Counting bounds -/

/-- Mapping a list by a function that is injective **on that list** preserves
duplicate-freeness. This is the weak, purely local form of injectivity that the counting
arguments below need. -/
theorem nodup_map_on {α β : Type} (f : α → β) (l : List α)
    (h : ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y)
    (hl : List.Nodup l) : List.Nodup (l.map f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      obtain ⟨hnot, hnt⟩ := List.nodup_cons.mp hl
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih ?_ hnt⟩
      · intro hy
        obtain ⟨x, hx, heq⟩ := List.mem_map.mp hy
        have hxa : x = a := h x a (by simp [hx]) (by simp) heq
        exact hnot (hxa ▸ hx)
      · intro x y hx hy hf
        exact h x y (by simp [hx]) (by simp [hy]) hf

/-- A duplicate-free list bound by a pairwise-disjointness condition on the fibres of `f`
stays duplicate-free when bound. -/
theorem nodup_flatMap {α β : Type} (l : List α) (f : α → List β)
    (hl : List.Nodup l)
    (hnd : ∀ a ∈ l, List.Nodup (f a))
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, ∀ y ∈ f b, x ≠ y) :
      List.Nodup (l.flatMap f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      obtain ⟨hnot, hnt⟩ := List.nodup_cons.mp hl
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hnd a (by simp),
        ih hnt (fun b hb => hnd b (by simp [hb]))
          (fun b hb c hc hab => hdisj b (by simp [hb]) c (by simp [hc]) hab), ?_⟩
      intro x hx y hy
      obtain ⟨c, hc, heq⟩ := List.mem_flatMap.mp hy
      have hne : a ≠ c := fun he => hnot (he ▸ hc)
      exact hdisj a (by simp) c (by simp [hc]) hne x hx y heq

private theorem filter_eq_self {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true) → l.filter p = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      rw [List.filter_cons_of_pos (h a (by simp)), ih (fun x hx => h x (by simp [hx]))]

/-- Removing one value from a duplicate-free list of naturals drops the length by at most
one. Phrased with `filter` rather than `erase` so that no decidability of propositional
equality is needed. -/
theorem length_filter_le_one :
    ∀ (l : List Nat) (j : Nat), List.Nodup l →
      l.length ≤ (l.filter (fun x => decide (x ≠ j))).length + 1 := by
  intro l
  induction l with
  | nil => intro j _; simp
  | cons a t ih =>
      intro j hnd
      obtain ⟨hnot, hnt⟩ := List.nodup_cons.mp hnd
      by_cases haj : a = j
      · subst haj
        have hjt : ∀ x ∈ t, decide (x ≠ a) = true := fun x hx =>
          decide_eq_true (fun he : x = a => hnot (he ▸ hx))
        have hneg : ¬ (fun x => decide (x ≠ a)) a = true := by
          show ¬ decide (a ≠ a) = true
          exact fun he => of_decide_eq_true he (by rfl)
        rw [List.filter_cons_of_neg (p := fun x => decide (x ≠ a)) hneg,
          filter_eq_self _ t hjt, List.length_cons]
        omega
      · have hpa : (fun x => decide (x ≠ j)) a = true :=
            decide_eq_true (fun he : a = j => haj he)
        rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ j)) hpa]
        have := ih j hnt
        rw [List.length_cons, List.length_cons]
        omega

/-- **Pigeonhole.** A duplicate-free list of natural numbers all below `k` has length at most
`k`. Proved by induction on the bound `k`, peeling off the value `k - 1` with `filter`. -/
theorem nodup_bounded_length :
    ∀ (k : Nat) (l : List Nat), List.Nodup l →
      (∀ x ∈ l, x < k) → l.length ≤ k := by
  intro k
  induction k with
  | zero =>
      intro l _ hall
      cases l with
      | nil => simp
      | cons a _ => exact absurd (hall a (by simp)) (by omega)
  | succ j ih =>
      intro l hnd hall
      have hlt : ∀ x ∈ l.filter (fun x => decide (x ≠ j)), x < j := by
        intro x hx
        obtain ⟨hx', hne⟩ := List.mem_filter.mp hx
        have hxk : x < j + 1 := hall x hx'
        have hne' : x ≠ j := of_decide_eq_true hne
        omega
      have hndf : List.Nodup (l.filter (fun x => decide (x ≠ j))) :=
        List.Pairwise.filter (fun x => decide (x ≠ j)) hnd
      have hlen := ih (l.filter (fun x => decide (x ≠ j))) hndf hlt
      have hle := length_filter_le_one l j hnd
      omega

/-- **Pigeonhole, function form.** If `f` maps a duplicate-free list `l` into values below
`k` and is injective on `l`, then `l.length ≤ k`. Contrapositively: more than `k` distinct
inputs mapped into `k` values force a collision. -/
theorem pigeonhole {α : Type} (f : α → Nat) (l : List α) (k : Nat)
    (hlt : ∀ x ∈ l, f x < k)
    (hinj : ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y)
    (hl : List.Nodup l) : l.length ≤ k := by
  have hmap := nodup_bounded_length k (l.map f)
    (nodup_map_on f l hinj hl)
    (fun y hy => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hlt x hx)
  rwa [List.length_map] at hmap

/-- **The complete enumeration of depth-`n` Boolean trees.** `allTrees n` lists every
`Tree Bool n`, each exactly once: `nodup_allTrees` says no duplicates, `complete_allTrees`
says nothing is missing. -/
def allTrees : (n : Nat) → List (Tree Bool n)
  | 0 => [Tree.leaf false, Tree.leaf true]
  | n + 1 => (allTrees n).flatMap (fun l => (allTrees n).map (fun r => Tree.node l r))

private theorem leaf_false_ne_leaf_true :
    (Tree.leaf (α := Bool) false : Tree Bool 0) ≠ Tree.leaf true := by
  intro h
  exact Bool.noConfusion (congrArg Tree.unleaf h)

theorem nodup_allTrees : ∀ n : Nat, List.Nodup (allTrees n)
  | 0 => by
      show List.Nodup [Tree.leaf false, Tree.leaf true]
      rw [List.nodup_cons]
      refine ⟨?_, by simp⟩
      intro h
      exact leaf_false_ne_leaf_true (List.mem_singleton.mp h)
  | n + 1 => by
      show List.Nodup ((allTrees n).flatMap (fun l => (allTrees n).map (fun r => Tree.node l r)))
      refine nodup_flatMap _ _ (nodup_allTrees n) ?_ ?_
      · intro l hl
        exact nodup_map_on (fun r => Tree.node l r) (allTrees n)
          (fun _ _ _ _ h => Tree.node.inj h |>.2) (nodup_allTrees n)
      · intro l hl r hr hne x hx y hy
        rw [List.mem_map] at hx hy
        obtain ⟨p, _, rfl⟩ := hx
        obtain ⟨q, _, rfl⟩ := hy
        exact fun he => hne (Tree.node.inj he |>.1)

theorem complete_allTrees : ∀ (n : Nat) (t : Tree Bool n), t ∈ allTrees n
  | 0, Tree.leaf a => by
      cases a <;> simp [allTrees]
  | n + 1, Tree.node l r => by
      show Tree.node l r ∈ (allTrees n).flatMap (fun a => (allTrees n).map (fun b => Tree.node a b))
      rw [List.mem_flatMap]
      exact ⟨l, complete_allTrees n l, List.mem_map.mpr ⟨r, complete_allTrees n r, rfl⟩⟩

private theorem length_map_const {α : Type} :
    ∀ (l : List α) (k : Nat), (l.map (fun _ => k)).sum = l.length * k
  | [], _ => by simp
  | a :: t, k => by
      show k + (t.map (fun _ => k)).sum = (a :: t).length * k
      rw [length_map_const t k, List.length_cons]
      show k + t.length * k = (t.length + 1) * k
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- **There are exactly `2 ^ (2 ^ n)` distinct depth-`n` Boolean trees.** A depth-`n` tree has
`2 ^ n` leaves, each independently `false` or `true`. -/
theorem length_allTrees : ∀ n : Nat,
    (allTrees n).length = 2 ^ (2 ^ n)
  | 0 => rfl
  | n + 1 => by
      have key : ∀ a ∈ allTrees n,
          ((allTrees n).map (fun r => Tree.node a r)).length = 2 ^ (2 ^ n) := by
        intro a ha
        rw [List.length_map (f := fun r => Tree.node a r), length_allTrees n]
      calc (allTrees (n + 1)).length
          = ((allTrees n).flatMap (fun a => (allTrees n).map (fun r => Tree.node a r))).length := rfl
        _ = ((allTrees n).map (fun a => ((allTrees n).map (fun r => Tree.node a r)).length)).sum := by
            rw [List.length_flatMap]
        _ = ((allTrees n).map (fun _ => 2 ^ (2 ^ n))).sum :=
            congrArg List.sum (List.map_congr_left key)
        _ = (allTrees n).length * 2 ^ (2 ^ n) :=
            length_map_const (allTrees n) (2 ^ (2 ^ n))
        _ = 2 ^ (2 ^ n) * 2 ^ (2 ^ n) := by rw [length_allTrees n]
        _ = 2 ^ (2 ^ n + 2 ^ n) := (Nat.pow_add 2 _ _).symm
        _ = 2 ^ (2 ^ (n + 1)) := by
            rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [Nat.pow_succ, Nat.mul_two]]

/-- **The information-theoretic barrier.** There is no injection from the set of depth-`n`
Boolean trees into `Fin k` when `k < 2 ^ (2 ^ n)`.

This is a pure counting statement: it constrains *no* property of the function, so it applies
to every hash construction whatsoever, including one designed specifically to be collision-free
on these trees. A collision-free commitment to `2 ^ n` bits of data needs at least `2 ^ (2 ^ n)`
digest values, i.e. at least `2 ^ n` bits of digest. -/
theorem no_injection_trees (n k : Nat) (f : Tree Bool n → Fin k)
    (h : k < 2 ^ (2 ^ n)) : ¬ Function.Injective f := by
  intro hinj
  have hlt : ∀ t ∈ allTrees n, (f t).val < k := fun t _ => (f t).isLt
  have hinj' : ∀ x y, x ∈ allTrees n → y ∈ allTrees n →
      (f x).val = (f y).val → x = y := fun x y _ _ he => hinj (Fin.eq_of_val_eq he)
  have := pigeonhole (fun t => (f t).val) (allTrees n) k hlt hinj' (nodup_allTrees n)
  rw [length_allTrees] at this
  omega

/-- A digest type with fewer than `2 ^ (2 ^ n)` elements cannot carry a collision-free
commitment at depth `n`: there is no injection into it at all. -/
theorem not_injective_into_small (n k : Nat) (f : Tree Bool n → Fin k)
    (h : k < 2 ^ (2 ^ n)) : ¬ Function.Injective f :=
  no_injection_trees n k f h

/-- **Applied to the Merkle hash: the digest set cannot be small.** Suppose `MerkleHash Bool β`
satisfies its axioms (it does, by assumption) and that `β` embeds into `Fin k`, i.e. `β` has at
most `k` elements. Then `k ≥ 2 ^ (2 ^ n)`.

Read the other way round: a collision-free commitment to a depth-`n` Boolean tree - `2 ^ n`
bits of data - needs at least `2 ^ (2 ^ n)` digest values, i.e. at least `2 ^ n` bits of
digest. **No compressing collision-free hash exists.** This is not a limitation of the
formalization but a theorem about any hash whatsoever, and it is why `Merkle/Free.lean`
instantiates the axioms with the non-compressing free algebra `Dig` instead of a fixed-width
digest, and why a production instantiation must *assume* an ideal hash rather than construct
one. -/
theorem digest_cannot_be_small {β : Type} [hsh : MerkleHash Bool β]
    (n k : Nat) (f : β → Fin k)
    (hf : Function.Injective f) (h : k < 2 ^ (2 ^ n)) : False := by
  have finj : Function.Injective (fun t : Tree Bool n => f (rootHash (m := hsh) t)) :=
    fun t₁ t₂ heq => rootHash_injective (m := hsh) t₁ t₂ (hf heq)
  exact absurd finj
    (no_injection_trees n k (fun t => f (rootHash (m := hsh) t)) h)

/-- The smallest instance of the barrier: no function from two values to one value is
injective, because the codomain has only one element. This is the base case of the pigeonhole
argument that rules out every finite compressing digest type. -/
theorem no_injection_two_into_one : ∀ f : Fin 2 → Fin 1, ¬ Function.Injective f := by
  intro f h
  have h₀ : f ⟨0, by omega⟩ = f ⟨1, by omega⟩ := Subsingleton.elim _ _
  have h₁ : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := h h₀
  have h₂ : (0 : Nat) = 1 := congrArg Fin.val h₁
  omega

/-- A concrete compressing candidate, *proved* not to be injective: reducing four values modulo
three identifies two of them. The general statement - no injection `Fin (n + 1) → Fin n` -
needs a cardinality theory, so we record the smallest instance that shows the shape of the
obstruction, next to the fully general tree-counting version above. -/
def modThree : Fin 4 → Fin 3 := fun i => ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

/-- `modThree` collides: `0` and `3` are identified. -/
theorem modThree_notInjective : ¬ Function.Injective modThree := by
  intro h
  have h₀ : modThree ⟨0, by omega⟩ = modThree ⟨3, by omega⟩ := rfl
  have h₁ : (⟨0, by omega⟩ : Fin 4) = ⟨3, by omega⟩ := h h₀
  have h₂ : (0 : Nat) = 3 := congrArg Fin.val h₁
  omega

/-! ## The exact forgery count -/

/-- **A fixed authentication path does not collapse values.** For a given proof `h`, the map
`d ↦ verify h d` is injective: folding a path up to a root loses no information about the leaf
digest it started from. An adversary who holds a valid proof for one value cannot substitute a
different value and still reach the same root. -/
theorem Proof.verify_injective {β : Type} [m : NodeAlgebra β] :
    ∀ (n : Nat) (h : Proof β n), Function.Injective (verify (m := m) h) := by
  intro n
  induction n with
  | zero =>
      intro h
      cases h
      exact fun _ _ he => he
  | succ n ih =>
      intro h
      cases h with
      | left h' b =>
          intro d₁ d₂ he
          obtain ⟨hsub, _⟩ := m.collFree
            (show m.node (verify h' d₁) b = m.node (verify h' d₂) b from he)
          exact ih h' hsub
      | right h' b =>
          intro d₁ d₂ he
          obtain ⟨_, hsub⟩ := m.collFree
            (show m.node b (verify h' d₁) = m.node b (verify h' d₂) from he)
          exact ih h' hsub

section
variable {α β : Type}
variable {m : MerkleHash α β}

/-- **At most one value is accepted at a given path.** If two proofs that select the same path
both verify against the root of `t`, they certify the *same* value.

This is the exact counting form of the forgery bound: for a fixed tree `t` and a fixed path
`p`, the set of values `a` for which *some* proof selecting `p` verifies `a` against
`rootHash t` has **at most one** element. An adversary who fixes a target leaf cannot have two
different winning values, so a random guess succeeds with probability at most `1 / |α|` - and
the theorem behind that bound is this one. -/
theorem accepting_value_unique :
    ∀ (n : Nat) (t : Tree α n) (p : Path n) (a₁ a₂ : α) (h₁ h₂ : Proof β n),
      Proof.pathOf h₁ = p → Proof.pathOf h₂ = p →
      verify h₁ (m.leaf a₁) = rootHash (m := m) t →
      verify h₂ (m.leaf a₂) = rootHash (m := m) t → a₁ = a₂ := by
  intro n t p a₁ a₂ h₁ h₂ hp₁ hp₂ hv₁ hv₂
  have h₁' : t.get (Proof.pathOf h₁) = a₁ := verify_sound n t h₁ a₁ hv₁
  have h₂' : t.get (Proof.pathOf h₂) = a₂ := verify_sound n t h₂ a₂ hv₂
  rw [hp₁] at h₁'
  rw [hp₂] at h₂'
  rw [← h₂', h₁']

/-- **Every value that is really in the tree is accepted** - so the bound above is tight, and
the number of winning values at path `p` is *exactly* one. -/
theorem accepting_value_exists :
    ∀ (n : Nat) (t : Tree α n) (p : Path n),
      ∃ (a : α) (h : Proof β n), Proof.pathOf h = p ∧
        verify h (m.leaf a) = rootHash (m := m) t := by
  intro n t p
  exact ⟨t.get p, ofTree t p, Proof.pathOf_ofTree n t p,
    verify_complete (α := α) (β := β) (m := m) n t p⟩

end

end Merkle
