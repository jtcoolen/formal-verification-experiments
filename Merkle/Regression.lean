import Merkle.Security
import Merkle.Usage

/-! Regression witnesses for collisions in finite signatures and numeric leaf addressing.
These examples elaborate as part of the default build and are included in the axiom audit. -/

namespace Merkle.Regression

-- The extraction theorem must work even when the leaf hash actually collides.
@[reducible] private def collidingLeaf : MerkleSig Bool Bool where
  leaf := fun _ => false
  node := Bool.and

theorem extracts_leaf_collision : Collision (s := collidingLeaf) :=
  collision_of_rootHash_eq (s := collidingLeaf) 0 (Tree.leaf false) (Tree.leaf true) rfl
    (by intro h; cases h)

-- A non-injective node combiner is supported without an injectivity hypothesis.
@[reducible] private def collidingNode : MerkleSig Bool Bool where
  leaf := id
  node := fun _ _ => false

private def t₁ : Tree Bool 1 := Tree.node (Tree.leaf false) (Tree.leaf false)
private def t₂ : Tree Bool 1 := Tree.node (Tree.leaf true) (Tree.leaf false)

theorem extracts_node_collision : Collision (s := collidingNode) :=
  collision_of_rootHash_eq (s := collidingNode) 1 t₁ t₂ rfl (by
    intro h
    have he := congrArg (fun t => t.get (Path.left Path.nil)) h
    cases he)

-- A false opening against the same root must yield a collision as well.
theorem extracts_forgery_collision : Collision (s := collidingNode) :=
  collision_of_forgery (s := collidingNode) t₁ (Proof.left Proof.nil false) true rfl (by decide)

-- Non-palindromic paths detect reversal of the index bits.
theorem indices_depth_two : (Path.allPaths 2).map Path.toNat = [0, 1, 2, 3] := rfl
theorem indices_depth_three : (Path.allPaths 3).map Path.toNat = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
theorem index_to_path : Usage.pathOfIndex 1 2 (by decide) = Path.left (Path.right Path.nil) := rfl

-- Account for path generation even for the depth-zero and empty-batch cases.
theorem proof_generation_depth_zero : (Tree.leaf 7).proofGenerationCost Path.nil = 0 := rfl
theorem empty_batch_cost : Usage.batchHashCost (Tree.leaf 7) [] = 1 := rfl
theorem singleton_batch_cost : Usage.batchHashCost (Tree.leaf 7) [(Path.nil, 8)] = 2 := rfl

end Merkle.Regression
