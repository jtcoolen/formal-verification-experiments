import Merkle
/-!
# Review probes for the Merkle library  (not part of the build)

Run with:   lake env lean scratch/merkle_review_probes.lean

Probe 1 exhibits a legitimate model of the two `MerkleHash` axioms in which a depth-0 root
equals a depth-1 root: the axioms do not bind the tree depth (number of leaves) into the
published digest. Probe 2 shows the one extra axiom that closes the gap, and that the free
algebra `Dig` already satisfies it.
-/

/-! Review probe: do the two MerkleHash axioms bind the tree DEPTH into the root digest?
Below is a fully legitimate model of the axioms in which a depth-0 root equals a depth-1 root. -/
open Merkle

/-- An injective pairing on `Nat → Nat`: split the argument by parity. -/
def vNode (f g : Nat → Nat) : Nat → Nat := fun n => if n % 2 = 0 then f (n / 2) else g (n / 2)

/-- The constant function: an injective leaf encoder whose image lies inside `vNode`'s range. -/
def vLeaf (a : Nat) : Nat → Nat := fun _ => a

theorem vNode_even (f g : Nat → Nat) (m : Nat) : vNode f g (2 * m) = f m := by
  show (if (2 * m) % 2 = 0 then f (2 * m / 2) else g (2 * m / 2)) = f m
  rw [show (2 * m) % 2 = 0 from by omega, show 2 * m / 2 = m from by omega]
  exact if_pos rfl

theorem vNode_odd (f g : Nat → Nat) (m : Nat) : vNode f g (2 * m + 1) = g m := by
  show (if (2 * m + 1) % 2 = 0 then f ((2 * m + 1) / 2) else g ((2 * m + 1) / 2)) = g m
  rw [if_neg (show ¬((2 * m + 1) % 2 = 0) from by omega),
    show (2 * m + 1) / 2 = m from by omega]

theorem vNode_injective : ∀ {f g f' g' : Nat → Nat}, vNode f g = vNode f' g' → f = f' ∧ g = g' := by
  intro f g f' g' h
  refine ⟨funext (fun m => ?_), funext (fun m => ?_)⟩
  · rw [← vNode_even f g m, ← vNode_even f' g' m, congrFun h (2 * m)]
  · rw [← vNode_odd f g m, ← vNode_odd f' g' m, congrFun h (2 * m + 1)]

/-- `MerkleHash Nat (Nat → Nat)`: both axioms hold, using no axioms of its own. -/
instance badHash : MerkleHash Nat (Nat → Nat) where
  node := vNode
  collFree {a b c d} h := vNode_injective h
  leaf := vLeaf
  leafInjective {x y} h := show x = y from congrFun h 0

/-- **The axioms do not bind the depth.** A depth-0 tree and a depth-1 tree share one root. -/
theorem cross_depth_root_collision :
    rootHash (m := badHash) (Tree.leaf 1 : Tree Nat 0)
      = rootHash (m := badHash) (Tree.node (Tree.leaf 1) (Tree.leaf 1) : Tree Nat 1) := by
  show vLeaf 1 = vNode (vLeaf 1) (vLeaf 1)
  funext n
  by_cases h : n % 2 = 0 <;> simp [vNode, vLeaf, h]

/-- Leaf digests sit inside the range of the node combiner: no domain separation is enforced. -/
theorem leaf_in_node_range : ∃ (a : Nat) (x y : Nat → Nat), vLeaf a = vNode x y :=
  ⟨1, vLeaf 1, vLeaf 1, cross_depth_root_collision⟩

/-- Same root, different number of leaves. -/
theorem same_root_different_leaf_count :
    ∃ (n m : Nat) (t : Tree Nat n) (u : Tree Nat m),
      n ≠ m ∧ t.leaves.length ≠ u.leaves.length ∧
        rootHash (m := badHash) t = rootHash (m := badHash) u :=
  ⟨0, 1, Tree.leaf 1, Tree.node (Tree.leaf 1) (Tree.leaf 1), by omega, by
    show 1 ≠ 2; omega, cross_depth_root_collision⟩

/-- What the library *does* prove about this model: injectivity at each fixed depth. -/
example : ∀ (t₁ t₂ : Tree Nat 1), rootHash (m := badHash) t₁ = rootHash (m := badHash) t₂ → t₁ = t₂ :=
  fun t₁ t₂ h => rootHash_injective (m := badHash) t₁ t₂ h



/-! Review probe #2: the missing axiom, and a checked sketch of the fix. -/
open Merkle

/-- The one thing MerkleHash does not assume: leaf digests are never node digests. -/
class DomainSeparated {α β : Type} [m : MerkleHash α β] : Prop where
  noCross : ∀ (a : α) (x y : β), m.leaf a ≠ m.node x y

/-- With domain separation the root pins the depth — the property probe #1 shows is missing. -/
theorem cross_depth_eq_imp_depth_eq {α β : Type} [m : MerkleHash α β]
    [ds : DomainSeparated (m := m)] :
    ∀ (n : Nat) (t₁ : Tree α n) (mm : Nat) (t₂ : Tree α mm),
      rootHash (m := m) t₁ = rootHash (m := m) t₂ → n = mm := by
  intro n
  induction n with
  | zero =>
      intro t₁ mm t₂ h
      cases t₁ with | leaf a =>
      cases mm with
      | zero => rfl
      | succ k =>
          cases t₂ with | node l r =>
          exact absurd h (ds.noCross a (rootHash (m := m) l) (rootHash (m := m) r))
  | succ k ih =>
      intro t₁ mm t₂ h
      cases t₁ with | node l r =>
      cases mm with
      | zero =>
          cases t₂ with | leaf a =>
          exact absurd h.symm (ds.noCross a (rootHash (m := m) l) (rootHash (m := m) r))
      | succ j =>
          cases t₂ with | node l₂ r₂ =>
          obtain ⟨h₁, h₂⟩ := m.collFree h
          have hn := ih l j l₂ h₁
          omega

theorem cross_depth_same_data {α β : Type} [m : MerkleHash α β]
    [ds : DomainSeparated (m := m)]
    (n mm : Nat) (t₁ : Tree α n) (t₂ : Tree α mm)
    (h : rootHash (m := m) t₁ = rootHash (m := m) t₂) :
    n = mm ∧ t₁.leaves.length = t₂.leaves.length := by
  have e := cross_depth_eq_imp_depth_eq n t₁ mm t₂ h
  cases e
  exact ⟨rfl, ((Tree.leaves_length n t₁).trans (Tree.leaves_length n t₂).symm)⟩

-- The free algebra satisfies the extra axiom for free (constructor distinctness).
section
open Merkle.Free
theorem dig_domain_separated (α : Type) :
    DomainSeparated (m := (inferInstance : MerkleHash α (Dig α))) where
  noCross a x y h := by cases h
end



/-! Probe 3: a strengthening the library does not currently state — the accepting
authentication path is *unique*, i.e. no proof malleability. Sketch that it is provable
from the existing axioms, in the same two-line induction shape as verify_sound. -/
theorem proof_unique {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (h : Proof β n) (a : α),
      verify h (m.leaf a) = rootHash (m := m) t → h = ofTree (β := β) t (Proof.pathOf h) := by
  intro n
  induction n with
  | zero =>
      intro t h a hv; cases h; cases t; rfl
  | succ n ih =>
      intro t h a hv
      cases t with
      | node l r =>
          cases h with
          | left h b =>
              obtain ⟨h₁, h₂⟩ := m.collFree hv
              have target : ofTree (β := β) (Tree.node l r) (Proof.pathOf (Proof.left h b))
                  = Proof.left (ofTree (β := β) l (Proof.pathOf h)) (rootHash (m := m) r) := rfl
              rw [target, ih l h a h₁, h₂, Proof.pathOf_ofTree n l (Proof.pathOf h)]
          | right h b =>
              obtain ⟨h₁, h₂⟩ := m.collFree hv
              have target : ofTree (β := β) (Tree.node l r) (Proof.pathOf (Proof.right h b))
                  = Proof.right (ofTree (β := β) r (Proof.pathOf h)) (rootHash (m := m) l) := rfl
              rw [target, ih r h a h₂, h₁, Proof.pathOf_ofTree n r (Proof.pathOf h)]

#print axioms proof_unique

#print axioms cross_depth_root_collision
#print axioms same_root_different_leaf_count
#print axioms cross_depth_eq_imp_depth_eq
#print axioms dig_domain_separated
