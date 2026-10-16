/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Merkle trees: shapes, digests, and collision resistance

This file fixes the *shape* of a binary Merkle tree and an **abstract** Merkle hash algebra.
Nothing here commits to a concrete hash function: every security theorem in `Merkle/Proof.lean`
is proved for *all* hash algebras satisfying the two axioms of `Merkle.MerkleHash`, and each of
them reduces the collision resistance of the tree to collision resistance of the two combiners.

Everything is developed in **pure Lean core** - no Mathlib dependency, so `lake build` finishes
in seconds.

## Main results

* `Merkle.Tree` - a *perfect* binary tree of depth `n` whose leaves carry values of type `α`.
  The depth is a `Nat` index, so a tree can never be the wrong height, and it has exactly
  `2 ^ n` leaves (`Merkle.Tree.leaves_length`).
* `Merkle.Path` - root-to-leaf paths indexed by their length. `allPaths_complete` and
  `allPaths_nodup` show there are exactly `2 ^ n` of them. No `Path n` addresses a leaf of a
  `Tree α m` for `m ≠ n`.
* `Merkle.MerkleHash` - the algebra a Merkle scheme needs: a leaf encoder, a node combiner,
  and their collision-freeness assumptions.
* `Merkle.rootHash_injective` - two trees of the same depth with equal root digests are equal,
  i.e. a Merkle root is a collision-resistant commitment to its whole leaf vector.
* `Merkle.Tree.get_injective` - a tree is completely determined by its leaf map `Path n → α`.

## Design notes

* Leaves are *not* run through the node combiner; they go through `MerkleHash.leaf`. This is
  what makes the second-preimage argument in `Merkle/Proof.lean` go through without extra
  domain-separation hypotheses.
* Everything is stated for an arbitrary depth index, so "wrong tree height", "path outside the
  tree", and "proof for a tree of another size" are untypeable rather than merely unprovable.
-/

namespace Merkle

/-! ### Perfect binary trees and indexed paths -/

/-- A **perfect** binary tree of depth `n` whose leaves carry `α`.

`leaf` is the base case (depth `0`); `node` increases the depth by one. Hence a `Tree α n`
has exactly `2 ^ n` leaves and every root-to-leaf path has length `n`. -/
inductive Tree (α : Type) : Nat → Type where
  /-- A tree of depth zero: a single leaf. -/
  | leaf : α → Tree α 0
  | node : Tree α n → Tree α n → Tree α (n + 1)

/-- A root-to-leaf path of length `n`. The outermost constructor names the *topmost* branch,
so a `Path n` is read from the root downwards. -/
inductive Path : Nat → Type where
  | nil : Path 0
  | left : Path n → Path (n + 1)
  | right : Path n → Path (n + 1)

/-- Mapping an injective function over a duplicate-free list stays duplicate-free. -/
theorem nodup_map {α β : Type} {f : α → β} (h : ∀ x y, f x = f y → x = y) :
    ∀ (l : List α), List.Nodup l → List.Nodup (l.map f) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro hl
      obtain ⟨hnot, hnt⟩ := List.nodup_cons.mp hl
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hnt⟩
      rw [List.mem_map]
      intro hy
      obtain ⟨b, hb, heq⟩ := hy
      have hba : b = a := h b a heq
      cases hba
      exact hnot hb


namespace Path

/-- The branch choices of a path, root first. -/
def toBits : Path n → List Bool
  | nil => []
  | left p => false :: toBits p
  | right p => true :: toBits p

/-- The leaf index addressed by a path, in left-to-right order (most significant bit first). -/
def toNat : Path n → Nat
  | nil => 0
  | left p => p.toNat
  | @right n p => 2 ^ n + p.toNat

/-- A path addresses an index strictly below `2 ^ n`. -/
theorem toNat_lt : ∀ (n : Nat) (p : Path n), p.toNat < 2 ^ n
  | _, nil => by simp [toNat]
  | n + 1, left p => by
      have h := toNat_lt n p
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      show p.toNat < 2 ^ (n + 1)
      omega
  | n + 1, right p => by
      have h := toNat_lt n p
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      show 2 ^ n + p.toNat < 2 ^ (n + 1)
      omega

theorem left_ne_right : ∀ {n : Nat} (p q : Path n), Path.left p ≠ Path.right q := by
  intro n p q h
  cases h

/-- A path is determined by the leaf index it addresses. -/
theorem toNat_injective : ∀ {n : Nat}, Function.Injective (toNat (n := n)) := by
  intro n
  induction n with
  | zero => intro p q _; cases p; cases q; rfl
  | succ n ih =>
      intro p q h
      cases p with
      | left p =>
          cases q with
          | left q => exact congrArg Path.left (ih h)
          | right q =>
              have hp := toNat_lt n p
              change p.toNat = 2 ^ n + q.toNat at h
              exfalso
              omega
      | right p =>
          cases q with
          | left q =>
              have hq := toNat_lt n q
              change 2 ^ n + p.toNat = q.toNat at h
              exfalso
              omega
          | right q =>
              apply congrArg Path.right
              apply ih
              change 2 ^ n + p.toNat = 2 ^ n + q.toNat at h
              omega

instance : DecidableEq (Path n) := fun p q =>
  if h : p.toNat = q.toNat then isTrue (toNat_injective h)
  else isFalse (fun h' => h (congrArg toNat h'))

instance : ToString (Path n) where
  toString p := String.ofList (p.toBits.map fun b => if b then 'R' else 'L')

/-- All `2 ^ n` paths of length `n`, in left-to-right order. -/
def allPaths : (n : Nat) → List (Path n)
  | 0 => [nil]
  | n + 1 => (allPaths n).map Path.left ++ (allPaths n).map Path.right

/-- Every path of length `n` occurs in `allPaths n`. -/
theorem allPaths_complete : ∀ (n : Nat) (p : Path n), p ∈ allPaths n
  | _, nil => by simp [allPaths]
  | n + 1, left p => by
      rw [allPaths, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨p, allPaths_complete n p, rfl⟩)
  | n + 1, right p => by
      rw [allPaths, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨p, allPaths_complete n p, rfl⟩)

/-- `allPaths n` has no duplicates. -/
theorem allPaths_nodup : ∀ (n : Nat), List.Nodup (allPaths n)
  | 0 => by simp [allPaths]
  | n + 1 => by
      rw [allPaths, List.nodup_append]
      refine ⟨nodup_map (fun _ _ => Path.left.inj) (allPaths n) (allPaths_nodup n),
        nodup_map (fun _ _ => Path.right.inj) (allPaths n) (allPaths_nodup n), ?_⟩
      intro x hx y hy hxy
      rw [List.mem_map] at hx hy
      obtain ⟨p, _, rfl⟩ := hx
      obtain ⟨q, _, hq⟩ := hy
      exact Path.left_ne_right p q (hq ▸ hxy)

/-- Hence there are exactly `2 ^ n` paths of length `n`. -/
theorem allPaths_length : ∀ (n : Nat), (allPaths n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      rw [allPaths, List.length_append, List.length_map (f := Path.left),
        List.length_map (f := Path.right), allPaths_length]
      have h : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
      omega


end Path

/-! ### Reading, writing, and shape facts -/ 

namespace Tree

/-- The value stored in the unique leaf of a depth-zero tree. -/
def unleaf : Tree α 0 → α
  | leaf a => a

/-- The two subtrees of a tree of positive depth. -/
def unnode : Tree α (n + 1) → Tree α n × Tree α n
  | node l r => (l, r)

/-- The leaves of a tree, left to right. -/
def leaves : Tree α n → List α
  | leaf a => [a]
  | node l r => l.leaves ++ r.leaves

/-- The leaf addressed by `p`. -/
def get : Tree α n → Path n → α
  | Tree.leaf a, Path.nil => a
  | Tree.node l _, Path.left p => get l p
  | Tree.node _ r, Path.right p => get r p

/-- Write `a` at the leaf addressed by `p`, leaving the rest of the tree untouched. -/
def update : Tree α n → Path n → α → Tree α n
  | Tree.leaf _, Path.nil, a => Tree.leaf a
  | Tree.node l r, Path.left p, a => Tree.node (update l p a) r
  | Tree.node l r, Path.right p, a => Tree.node l (update r p a)

/-- The leaf map of a tree. -/
def leafMap : Tree α n → (Path n → α) := fun t p => t.get p

/-- A tree of depth `n` has exactly `2 ^ n` leaves. -/
theorem leaves_length : ∀ (n : Nat) (t : Tree α n), t.leaves.length = 2 ^ n
  | 0, leaf _ => rfl
  | n + 1, node l r => by
      show (l.leaves ++ r.leaves).length = 2 ^ (n + 1)
      rw [List.length_append, leaves_length, leaves_length]
      have h : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
      omega

/-- `update` writes the requested value at `p`. -/
theorem get_update_same (a : α) : ∀ (n : Nat) (t : Tree α n) (p : Path n),
    (t.update p a).get p = a := by
  intro n
  induction n with
  | zero => intro t p; cases t with | leaf b => cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p => show (l.update p a).get p = a; exact ih l p
          | right p => show (r.update p a).get p = a; exact ih r p

/-- `update` at `p` leaves every *other* leaf untouched. -/
theorem get_update_other (a : α) : ∀ {n : Nat} (t : Tree α n) {p q : Path n}, p ≠ q →
    (t.update p a).get q = t.get q := by
  intro n t p q hne
  induction n with
  | zero => cases p with
      | nil => cases q with
          | nil => exact absurd rfl hne
  | succ n ih =>
      cases t with
      | node l r =>
          cases p with
          | left p =>
              cases q with
              | left q =>
                  show (l.update p a).get q = l.get q
                  by_cases h : p = q
                  · exact absurd (congrArg Path.left h) hne
                  · exact ih l h
              | right q => rfl
          | right p =>
              cases q with
              | right q =>
                  show (r.update p a).get q = r.get q
                  by_cases h : p = q
                  · exact absurd (congrArg Path.right h) hne
                  · exact ih r h
              | left q => rfl

/-- Writing the value that is already there changes nothing. -/
theorem update_get_idem : ∀ (n : Nat) (t : Tree α n) (p : Path n), t.update p (t.get p) = t := by
  intro n
  induction n with
  | zero => intro t p; cases t with | leaf b => cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p => show Tree.node (l.update p (l.get p)) r = Tree.node l r; rw [ih]
          | right p => show Tree.node l (r.update p (r.get p)) = Tree.node l r; rw [ih]

/-- `update` at `p` is idempotent as an operation. -/
theorem update_update (a b : α) : ∀ (n : Nat) (t : Tree α n) (p : Path n),
    (t.update p a).update p b = t.update p b := by
  intro n
  induction n with
  | zero => intro t p; cases t with | leaf c => cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p =>
              show Tree.node ((l.update p a).update p b) r = Tree.node (l.update p b) r
              rw [ih]
          | right p =>
              show Tree.node l ((r.update p a).update p b) = Tree.node l (r.update p b)
              rw [ih]

/-- A tree is completely determined by its leaf map. This is the formal reason that
"off-tree" paths are not expressible: there is no `p` at which to state a forgery. -/
theorem get_injective : ∀ {n : Nat} (t₁ t₂ : Tree α n), (∀ p, t₁.get p = t₂.get p) → t₁ = t₂ := by
  intro n t₁ t₂ h
  induction n with
  | zero => cases t₁ with | leaf a => cases t₂ with | leaf b => have := h Path.nil; subst this; rfl
  | succ n ih =>
      cases t₁ with
      | node l₁ r₁ => cases t₂ with
        | node l₂ r₂ => rw [ih l₁ l₂ (fun p => h (Path.left p)), ih r₁ r₂ (fun p => h (Path.right p))]

end Tree

/-! ### The Merkle hash algebra -/

/-- A collision-free binary combiner on digests: `node a b = node c d` forces `a = c` and
`b = d`. This is exactly the absence of collisions for the internal-node hash. -/
class NodeAlgebra (β : Type) where
  node : β → β → β
  collFree : ∀ {a b c d : β}, node a b = node c d → a = c ∧ b = d

/-- The data and assumptions of a Merkle hash scheme over leaf values `α` and digests `β`.

* `leaf` encodes a leaf value as a digest and `node` combines two child digests;
* `leafInjective` - leaf values are recoverable from their digest, so a prover cannot swap one
  leaf value for another without changing the root;
* `collFree` - the node combiner has no collisions.

A concrete instantiation must supply proofs of these two fields. See `Merkle/Free.lean` for
a fully proved one. Absolute injectivity cannot hold for a nontrivial fixed-width digest;
real hashes use the assumption-free functions in `Merkle/Signature.lean`. -/
class MerkleHash (α β : Type) extends NodeAlgebra β where
  leaf : α → β
  leafInjective : Function.Injective leaf

/-- The root digest of a tree: `leaf` at the leaves, `node` on the way up. -/
def rootHash {α β : Type} [m : MerkleHash α β] : Tree α n → β
  | Tree.leaf a => m.leaf a
  | Tree.node l r => m.node (rootHash l) (rootHash r)

/-- The digest of the subtree rooted at `p`. -/
def subtreeHash {α β : Type} [m : MerkleHash α β] : Tree α n → Path n → β
  | Tree.leaf a, Path.nil => m.leaf a
  | Tree.node l _, Path.left p => subtreeHash l p
  | Tree.node _ r, Path.right p => subtreeHash r p

/-- **Collision resistance of the root digest.** Two trees of the same depth with equal root
digests are equal.

This is the theorem that makes a Merkle root a collision-resistant commitment to its whole leaf
vector: producing a second tree with the same root requires a collision in `node` (at some
internal node) or in `leaf` (at depth zero). -/
theorem rootHash_injective {α β : Type} [m : MerkleHash α β] :
    ∀ {n : Nat} (t₁ t₂ : Tree α n), rootHash (m := m) t₁ = rootHash (m := m) t₂ → t₁ = t₂ := by
  intro n t₁ t₂ h
  induction n with
  | zero =>
      cases t₁ with
      | leaf a => cases t₂ with
        | leaf b =>
            have : a = b := m.leafInjective h
            subst this; rfl
  | succ n ih =>
      cases t₁ with
      | node l₁ r₁ => cases t₂ with
        | node l₂ r₂ =>
            obtain ⟨hl, hr⟩ := m.collFree h
            rw [ih l₁ l₂ hl, ih r₁ r₂ hr]

/-- The two-sided form: equal roots if and only if equal trees. -/
theorem rootHash_eq_iff {α β : Type} [m : MerkleHash α β] {n : Nat}
    (t₁ t₂ : Tree α n) : rootHash (m := m) t₁ = rootHash (m := m) t₂ ↔ t₁ = t₂ :=
  ⟨fun h => rootHash_injective (m := m) t₁ t₂ h, fun h => h ▸ rfl⟩

end Merkle
