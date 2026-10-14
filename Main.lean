import Merkle

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

-- A runnable demonstration: `lake exe merkleDemo`. Every value printed here is computed by
-- the Lean kernel from the definitions in the `Merkle` library; nothing is hard-coded.

open Merkle Merkle.Examples

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
  IO.println "verify_complete, verify_sound and rootHash_update say these outcomes hold"
  IO.println "for every tree, every path, and every collision-free hash algebra."
