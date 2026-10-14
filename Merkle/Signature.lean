import Merkle.Proof

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# The signature layer: Merkle trees without collision assumptions

`Merkle.MerkleHash` bundles two *functions* (`leaf`, `node`) together with two *assumptions*
about them (`collFree`, `leafInjective`). That bundling is convenient for stating security
theorems, but it makes the functions unusable on their own: you cannot even *compute* a Merkle
root with SHA3-256 unless you also hand Lean proofs that SHA3-256 is collision-free - and by
`Merkle.digest_cannot_be_small` those proofs cannot exist.

This file separates the two concerns along exactly that seam:

* `Merkle.NodeSig` / `Merkle.MerkleSig` - the operations, no axioms.
* `Merkle.SigCollisionFree` - the assumptions, stated separately as a `Prop`.

Everything that is *correctness* rather than *security* is proved here, over an arbitrary
signature, with no assumptions at all:

* `Sig.complete` - the honest path verifies.
* `Sig.update` - the incremental root equals the full rehash.
* `Sig.root_eq_rootHash` - this layer agrees with `Merkle.rootHash` whenever the axioms do hold,
  so nothing is duplicated or re-proved differently.
* `merkleHashOfSig` - adding `SigCollisionFree` recovers a full `MerkleHash`, so every theorem
  in `Merkle/Proof.lean` and `Merkle/Security.lean` applies unchanged.
-/

namespace Merkle

/-- A **combiner signature**: an internal-node hash, with no assumptions about it. -/
class NodeSig (β : Type) where
  node : β → β → β

/-- A **Merkle signature**: a leaf hash and a node combiner, with no assumptions about either.

This is the level at which a real hash function - SHA3-256, BLAKE3, whatever - can actually be
installed. Contrast with `MerkleHash`, which additionally demands collision-freeness and so
admits no fixed-width instantiation. -/
class MerkleSig (α β : Type) extends NodeSig β where
  leaf : α → β

/-- **The assumptions, stated separately.** A signature is collision-free when the combiner is
injective on pairs and the leaf hash is injective.

Keeping this a separate class is the whole point of the split: correctness theorems never ask
for it, and security theorems ask for it explicitly, so it is always visible which is which. -/
class SigCollisionFree {α β : Type} [s : MerkleSig α β] : Prop where
  /-- The combiner has no collisions: equal outputs force equal inputs. -/
  nodeInjective : ∀ {a b c d : β}, s.node a b = s.node c d → a = c ∧ b = d
  /-- The leaf hash is injective. -/
  leafInjective : Function.Injective s.leaf

namespace Sig
open Merkle

/-- Fold a tree to its root digest, over a bare signature. -/
def root {α β : Type} [s : MerkleSig α β] : Tree α n → β
  | Tree.leaf a => s.leaf a
  | Tree.node l r => s.node (root l) (root r)

/-- Fold an authentication path up to a candidate root, over a bare combiner. -/
def fold {β : Type} [s : NodeSig β] : Proof β n → β → β
  | Proof.nil => fun d => d
  | Proof.left p b => fun d => s.node (fold p d) b
  | Proof.right p b => fun d => s.node b (fold p d)

/-- The honest authentication path for leaf `p`, over a bare signature. -/
def ofTree {α β : Type} [s : MerkleSig α β] : Tree α n → Path n → Proof β n
  | Tree.leaf _, Path.nil => Proof.nil
  | Tree.node l r, Path.left p => Proof.left (ofTree l p) (root r)
  | Tree.node l r, Path.right p => Proof.right (ofTree r p) (root l)

/-- **Completeness, with no assumptions.** The honest path of leaf `p` verifies. Note the
statement mentions no collision-freeness: this is a property of how the functions are *composed*,
not of the functions themselves, so it holds equally for a deliberately colliding hash. -/
theorem complete {α β : Type} [s : MerkleSig α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n),
      fold (ofTree t p) (s.leaf (t.get p)) = root t := by
  intro n
  induction n with
  | zero => intro t p; cases t with | leaf a => cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p =>
              show s.node (fold (ofTree l p) (s.leaf (l.get p))) (root r)
                = root (Tree.node l r)
              rw [ih l p]; rfl
          | right p =>
              show s.node (root l) (fold (ofTree r p) (s.leaf (r.get p)))
                = root (Tree.node l r)
              rw [ih r p]; rfl

/-- **Incremental update, with no assumptions.** Recomputing the root after a write equals
folding the old path against the new leaf digest. Again purely definitional bookkeeping. -/
theorem update {α β : Type} [s : MerkleSig α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n) (a : α),
      root (t.update p a) = fold (ofTree t p) (s.leaf a) := by
  intro n
  induction n with
  | zero => intro t p a; cases t with | leaf b => cases p; rfl
  | succ n ih =>
      intro t p a
      cases t with
      | node l r =>
          cases p with
          | left p =>
              show s.node (root (l.update p a)) (root r)
                = fold (ofTree (Tree.node l r) (Path.left p)) (s.leaf a)
              rw [ih l p a]; rfl
          | right p =>
              show s.node (root l) (root (r.update p a))
                = fold (ofTree (Tree.node l r) (Path.right p)) (s.leaf a)
              rw [ih r p a]; rfl

/-- The honest path selects the path it was built for - no assumptions needed. -/
theorem pathOf_ofTree {α β : Type} [s : MerkleSig α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n),
      Proof.pathOf (ofTree (β := β) t p) = p := by
  intro n
  induction n with
  | zero => intro t p; cases t with | leaf a => cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p =>
              show Path.left (Proof.pathOf (ofTree (β := β) l p)) = Path.left p
              rw [ih l p]
          | right p =>
              show Path.right (Proof.pathOf (ofTree (β := β) r p)) = Path.right p
              rw [ih r p]

end Sig

/-- A collision-free signature is a full `MerkleHash`, so every theorem elsewhere in the
library applies to it unchanged. This is the bridge back to the bundled formulation. -/
instance merkleHashOfSig {α β : Type} [s : MerkleSig α β]
    [cf : @SigCollisionFree α β s] :
    MerkleHash α β where
  node := s.node
  collFree := @SigCollisionFree.nodeInjective α β s cf
  leaf := s.leaf
  leafInjective := @SigCollisionFree.leafInjective α β s cf

/-- With the axioms present, the signature layer agrees with `rootHash` definitionally, so
nothing is proved twice in two different ways. -/
theorem sigRoot_eq_rootHash {α β : Type} [s : MerkleSig α β]
    [cf : @SigCollisionFree α β s] :
    ∀ (n : Nat) (t : Tree α n),
      Sig.root (α := α) (β := β) t =
        rootHash (α := α) (β := β) (m := @merkleHashOfSig α β s cf) t := by
  intro n
  induction n with
  | zero => intro t; cases t with | leaf a => rfl
  | succ n ih =>
      intro t
      cases t with
      | node l r =>
          show s.node (Sig.root (α := α) (β := β) l)
            (Sig.root (α := α) (β := β) r)
            = rootHash (α := α) (β := β)
              (m := @merkleHashOfSig α β s cf) (Tree.node l r)
          rw [ih l, ih r]
          rfl

end Merkle
