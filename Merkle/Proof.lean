import Merkle.Basic

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Merkle inclusion proofs and the no-forgery theorem

This file defines Merkle authentication paths and proves the two properties that make them
useful: **completeness** (an honest inclusion proof always verifies) and **soundness** (no
adversary can produce a proof for a value that is not in the tree at the addressed leaf).

## Main results

* `Merkle.Proof` - an authentication path: at each level the sibling digest plus a direction
  bit. The direction bits *are* the path, so a proof cannot be re-used at a different leaf.
* `Merkle.verify` - fold a proof up to a candidate root digest.
* `Merkle.verify_complete` - completeness: `verify (ofTree t p) (leaf (get t p)) = rootHash t`.
* `Merkle.verify_sound` - **the no-forgery theorem**: if `verify h (leaf a) = rootHash t` then
  `get t (pathOf h) = a`. Any proof that verifies against a root commits to the value that is
  really stored at the path the proof itself selects.
* `Merkle.no_forgery` - contrapositive form: if `get t p ≠ a` then no proof selecting `p`
  verifies `a` against `rootHash t`.
* `Merkle.rootHash_update` - incremental update: `rootHash (t.update p a) =`
  `verify (ofTree t p) (leaf a)`. Recomputing a root from an authentication path costs `O(n)`
  node hashes once the path is available. Generating it with `ofTree` rehashes uncached sibling
  subtrees; `Tree.proofGenerationCost_add_depth` accounts for that cost.

Note that `verify_sound` needs no domain-separation axiom beyond leaf injectivity: because the
path is read out of the proof's own direction bits, the "wrong branch" forgeries that require
leaf/node tag separation cannot even be stated here.
-/

namespace Merkle

/-- A Merkle authentication path for a tree of depth `n` over digests `β`.

The recursive argument comes first so that a proof is read from the leaf upwards. The
constructor name records which branch the *path* took at that level, and the payload is the
sibling digest that must be combined with it. -/
inductive Proof (β : Type) : Nat → Type where
  /-- At depth zero there is nothing to prove: the leaf digest is already the subtree digest. -/
  | nil : Proof β 0
  /-- The path went left at this level; `β` is the right sibling's digest. -/
  | left : Proof β n → β → Proof β (n + 1)
  /-- The path went right at this level; `β` is the left sibling's digest. -/
  | right : Proof β n → β → Proof β (n + 1)

namespace Proof

/-- The leaf path selected by a proof, read off its direction bits. -/
def pathOf : Proof β n → Path n
  | nil => Path.nil
  | left h _ => Path.left (pathOf h)
  | right h _ => Path.right (pathOf h)

end Proof

/-- Fold an authentication path up to a candidate root digest, starting from digest `d`. -/
def verify {β : Type} [m : NodeAlgebra β] : Proof β n → β → β
  | Proof.nil => fun d => d
  | Proof.left h b => fun d => m.node (verify h d) b
  | Proof.right h b => fun d => m.node b (verify h d)

/-- The honest authentication path for leaf `p` of tree `t`: collect the sibling digest at
every level on the way down. -/
def ofTree {α β : Type} [m : MerkleHash α β] : Tree α n → Path n → Proof β n
  | Tree.leaf _, Path.nil => Proof.nil
  | Tree.node l r, Path.left p => Proof.left (ofTree l p) (rootHash r)
  | Tree.node l r, Path.right p => Proof.right (ofTree r p) (rootHash l)

/-- The honest proof selects the path it was built for. -/
theorem Proof.pathOf_ofTree {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n), Proof.pathOf (ofTree (β := β) t p) = p
  | 0, Tree.leaf _, Path.nil => rfl
  | n + 1, Tree.node l r, Path.left p => by
      show Path.left (Proof.pathOf (ofTree l p)) = Path.left p
      rw [Proof.pathOf_ofTree n l p]
  | n + 1, Tree.node l r, Path.right p => by
      show Path.right (Proof.pathOf (ofTree r p)) = Path.right p
      rw [Proof.pathOf_ofTree n r p]

/-- **Completeness.** The honest proof of leaf `p` verifies. -/
theorem verify_complete {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n),
      verify (ofTree t p) (m.leaf (t.get p)) = rootHash t := by
  intro n
  induction n with
  | zero => intro t p; cases t with | leaf a => cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p =>
              show m.node (verify (ofTree l p) (m.leaf (l.get p))) (rootHash r) = rootHash (l.node r)
              rw [ih l p]
              rfl
          | right p =>
              show m.node (rootHash l) (verify (ofTree r p) (m.leaf (r.get p))) = rootHash (l.node r)
              rw [ih r p]
              rfl

/-- **The no-forgery theorem.** If a proof verifies a claimed leaf value `a` against the root
of `t`, then `a` is the value actually stored at the path the proof itself selects.

Read as an adversarial game: the attacker sees `rootHash t`, then outputs a proof `h` and a
value `a`; they win iff `verify h (leaf a) = rootHash t` while `t` does not store `a` at the
path `h` selects. This theorem says the winning set is empty - unconditionally, for every
collision-free hash algebra. -/
theorem verify_sound {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (h : Proof β n) (a : α),
      verify h (m.leaf a) = rootHash t → t.get (Proof.pathOf h) = a := by
  intro n
  induction n with
  | zero =>
      intro t h a hv
      cases t with
      | leaf b =>
          cases h
          show b = a
          exact (m.leafInjective hv).symm
  | succ n ih =>
      intro t h a hv
      cases t with
      | node l r =>
          cases h with
          | left h b =>
              obtain ⟨h₁, _⟩ := m.collFree hv
              show l.get (Proof.pathOf h) = a
              exact ih l h a h₁
          | right h b =>
              obtain ⟨_, h₂⟩ := m.collFree hv
              show r.get (Proof.pathOf h) = a
              exact ih r h a h₂

/-- **No forgery, contrapositive form.** If `t` does not store `a` at `p`, then no proof that
selects `p` can verify `a` against `rootHash t`. -/
theorem no_forgery {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n) (a : α), t.get p ≠ a →
      ∀ (h : Proof β n), Proof.pathOf h = p → verify h (m.leaf a) ≠ rootHash t := by
  intro n t p a hne h hp
  intro hvalid
  have h₂ : t.get (Proof.pathOf h) = a := verify_sound n t h a hvalid
  rw [hp] at h₂
  exact hne h₂

/-- A proof that verifies a value at two different paths forces the two leaves to agree. -/
theorem verify_two_paths {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (a : α) (h₁ h₂ : Proof β n),
      verify h₁ (m.leaf a) = rootHash t → verify h₂ (m.leaf a) = rootHash t →
      t.get (Proof.pathOf h₁) = t.get (Proof.pathOf h₂) := by
  intro n t a h₁ h₂ hv₁ hv₂
  rw [verify_sound n t h₁ a hv₁, verify_sound n t h₂ a hv₂]

/-- **Incremental root update.** Recomputing the root after writing `a` at `p` is exactly
verifying the honest path of `t` against `leaf a`. Folding an available proof costs `n` node
hashes plus one leaf hash; generating it with `ofTree` from an uncached tree has a separate cost. -/
theorem rootHash_update {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n) (a : α),
      rootHash (t.update p a) = verify (ofTree t p) (m.leaf a) := by
  intro n
  induction n with
  | zero => intro t p a; cases t with | leaf b => cases p; rfl
  | succ n ih =>
      intro t p a
      cases t with
      | node l r =>
          cases p with
          | left p =>
              show m.node (rootHash (l.update p a)) (rootHash r) = verify (ofTree (l.node r) (Path.left p)) (m.leaf a)
              rw [ih]
              rfl
          | right p =>
              show m.node (rootHash l) (rootHash (r.update p a)) = verify (ofTree (l.node r) (Path.right p)) (m.leaf a)
              rw [ih]
              rfl

/-- Writing a value that is already there leaves the root unchanged. -/
theorem rootHash_update_get {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (p : Path n),
      rootHash (m := m) (t.update p (t.get p)) = rootHash (m := m) t := by
  intro n t p
  rw [rootHash_update (α := α) (β := β) (m := m) n t p (t.get p), verify_complete (α := α) (β := β) (m := m) n t p]

end Merkle
