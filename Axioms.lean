import Merkle

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

-- Axiom audit: run `lake env lean Axioms.lean`.
-- Every theorem below should report only `propext` and `Quot.sound` - Lean's standard logical
-- axioms - and never `Classical.choice` or `sorryAx`.

#print axioms Merkle.rootHash_injective
#print axioms Merkle.rootHash_eq_iff
#print axioms Merkle.verify_complete
#print axioms Merkle.verify_sound
#print axioms Merkle.no_forgery
#print axioms Merkle.verify_two_paths
#print axioms Merkle.rootHash_update
#print axioms Merkle.rootHash_update_get
#print axioms Merkle.Proof.pathOf_ofTree
#print axioms Merkle.Tree.get_injective
#print axioms Merkle.Tree.get_update_same
#print axioms Merkle.Tree.get_update_other
#print axioms Merkle.Tree.update_get_idem
#print axioms Merkle.Tree.update_update
#print axioms Merkle.Tree.leaves_length
#print axioms Merkle.Path.toNat_injective
#print axioms Merkle.Path.toNat_lt
#print axioms Merkle.Path.left_ne_right
#print axioms Merkle.Path.allPaths_complete
#print axioms Merkle.Path.allPaths_nodup
#print axioms Merkle.Path.allPaths_length
#print axioms Merkle.Examples.modThree_notInjective
#print axioms Merkle.Examples.no_injection_two_into_one
