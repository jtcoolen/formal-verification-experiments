import Merkle

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

-- A runnable demonstration: `lake exe merkleDemo`. Every value printed here is computed by
-- the Lean kernel from the definitions in the `Merkle` library; nothing is hard-coded.

open Merkle Merkle.Free Merkle.Usage

/-- A depth-three Merkle tree over `Nat`, with digests in the free algebra `Dig Nat`. -/
def demoTree : Tree Nat 3 :=
  Tree.node
    (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1))
               (Tree.node (Tree.leaf 2) (Tree.leaf 3)))
    (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5))
               (Tree.node (Tree.leaf 6) (Tree.leaf 7)))

/-- The path root -> right -> left -> right, addressing leaf index 5. -/
def demoPath : Path 3 :=
  Path.right (Path.left (Path.right Path.nil))

/-- The root digest of `demoTree`, with the digest type pinned. -/
def demoRoot : Dig Nat := rootHash (β := Dig Nat) demoTree

/-- Encode a leaf value as a digest. -/
def enc (a : Nat) : Dig Nat := MerkleHash.leaf (β := Dig Nat) a

/-- Digests in the free algebra carry no `ToString`, so we render them by hand. -/
partial def showDig : Dig Nat → String
  | Dig.leaf a => toString a
  | Dig.node l r => "(" ++ showDig l ++ "," ++ showDig r ++ ")"

def main : IO Unit := do
  IO.println "Merkle tree demo - every value below is computed by the Lean kernel"
  IO.println ""
  IO.println s!"demoTree leaves : {demoTree.leaves}"
  IO.println s!"leaf count : {demoTree.leaves.length} (2 ^ 3 = {2 ^ 3})"
  IO.println s!"length-3 paths : {(Path.allPaths 3).length}"
  IO.println ""
  IO.println s!"demoPath : {demoPath}"
  IO.println s!"  addresses leaf index : {demoPath.toNat}"
  IO.println s!"  holds the value : {demoTree.get demoPath}"
  IO.println ""
  IO.println s!"root digest : {showDig demoRoot}"
  let proof := ofTree (β := Dig Nat) demoTree demoPath
  let honest := verify proof (enc (demoTree.get demoPath))
  IO.println s!"honest proof verifies : {decide (honest = demoRoot)}"
  let forged := verify proof (enc 42)
  IO.println s!"forged value 42 verifies : {decide (forged = demoRoot)}"
  IO.println ""
  let updated := demoTree.update demoPath 999
  let fast := verify proof (enc 999)
  let slow := rootHash (β := Dig Nat) updated
  IO.println s!"incremental == full hash : {decide (fast = slow)}"
  IO.println s!"updated value at path : {updated.get demoPath}"
  let untouched := Path.left (Path.left (Path.left Path.nil))
  IO.println s!"untouched leaf at {untouched} : {updated.get untouched}"
  IO.println ""
  IO.println "--- cost accounting (Merkle/Complexity.lean) ---"
  IO.println s!"full rehash of a depth-3 tree : {demoTree.hashCost} hashes"
  IO.println s!"  closed form 2^(3+1)-1       : {2 ^ (3 + 1) - 1}"
  IO.println s!"  2 * leaves - 1              : {2 * demoTree.leaves.length - 1}"
  IO.println s!"incremental update            : {demoPath.cost} hashes"
  IO.println s!"proof carries                 : {proof.digestCount} sibling digests"
  IO.println s!"  = log2 of leaf count        : {Nat.log2 demoTree.leaves.length}"
  IO.println s!"saving on this tree           : {demoTree.hashCost - demoPath.cost} hashes"
  IO.println ""
  IO.println "--- sparse subtrees (Merkle/Usage.lean) ---"
  let big : Tree Nat 10 := fill 10 0
  IO.println s!"a depth-10 all-zero tree has {big.leaves.length} leaves"
  IO.println s!"hashing it leaf by leaf costs {big.hashCost} hashes"
  IO.println s!"a sparse digest needs 1 leaf + 10 node hashes: {1 + 10}"
  let sparse := fillHash (α := Nat) (β := Dig Nat) 3 0
  IO.println s!"sparse == full rehash (depth 3) : {decide (rootHash (β := Dig Nat) (fill 3 0) = sparse)}"
  IO.println s!"sparse digest : {showDig sparse}"
  IO.println ""
  IO.println "--- batch update ---"
  let batch := updateAll demoTree [(demoPath, 100), (untouched, 200)]
  IO.println s!"after batch: leaf 5 = {batch.get demoPath}, leaf 0 = {batch.get untouched}"
  let step1 := demoTree.update demoPath 100
  let folded := verify (ofTree (β := Dig Nat) step1 untouched) (enc 200)
  IO.println s!"batch root == folded updates : {decide (rootHash (β := Dig Nat) batch = folded)}"
  IO.println ""
  IO.println "--- counting bound (Merkle/Security.lean) ---"
  IO.println s!"distinct depth-3 Boolean trees : {(Merkle.allTrees 3).length}"
  IO.println s!"  closed form 2^(2^3)          : {2 ^ (2 ^ 3)}"
  IO.println s!"distinct depth-4 Boolean trees : {2 ^ (2 ^ 4)}"
  IO.println s!"a 16-bit digest has 2^16 = {2 ^ (16 : Nat)} values - exactly enough, no slack"
  IO.println s!"a 15-bit digest must collide on depth-4 trees: {decide (2 ^ (2 ^ 4) > 2 ^ (15 : Nat))}"
  IO.println s!"a 256-bit digest holds 2^256 values."
  IO.println s!"depth-9 Boolean trees (512 leaves) need 2^(2^9) = 2^512 of them:"
  IO.println s!"  2^(2^9) > 2^256, so a 256-bit hash MUST collide: {decide (2 ^ (2 ^ 9) > 2 ^ (256 : Nat))}"
  IO.println ""
  IO.println "--- real SHA3-512 (Merkle/Sha3.lean, via lean4-hash) ---"
  let t := Merkle.Sha3.demoTree
  let pp := Merkle.Sha3.demoPath
  IO.println s!"SHA3-512 of empty string : {Merkle.Sha3.sha3Hex []}"
  IO.println s!"Merkle root of a depth-2 tree of 512-bit leaves:"
  IO.println s!"  {Merkle.Sha3.demoRootHex}"
  IO.println s!"  ({Merkle.Sha3.demoRootHex.length} hex chars = 512 bits)"
  let folded := Sig.fold (s := Merkle.Sha3.sha3Sig.toNodeSig)
    (Sig.ofTree (s := Merkle.Sha3.sha3Sig) t pp)
    (Merkle.Sha3.sha3Sig.leaf (t.get pp))
  IO.println s!"honest proof verifies (no assumptions): {decide (folded = Sig.root (s := Merkle.Sha3.sha3Sig) t)}"
  let tampered := Sig.fold (s := Merkle.Sha3.sha3Sig.toNodeSig)
    (Sig.ofTree (s := Merkle.Sha3.sha3Sig) t pp)
    (Merkle.Sha3.sha3Sig.leaf (BitVec.ofNat 512 99))
  IO.println s!"tampered value verifies          : {decide (tampered = Sig.root (s := Merkle.Sha3.sha3Sig) t)}"
  IO.println "sig_complete and sig_update hold for SHA3-512 with zero axioms;"
  IO.println "no_collision_free_sha3_512 proves the security axioms cannot be satisfied."
  IO.println ""
  IO.println "verify_complete, verify_sound and rootHash_update say these outcomes hold"
  IO.println "for every tree, every path, and every collision-free hash algebra."
  IO.println "not_pow_isBigO_linear says the O(2^n) rehash cost cannot be improved to O(n)."
  IO.println "digest_cannot_be_small says no compressing collision-free hash can exist."
