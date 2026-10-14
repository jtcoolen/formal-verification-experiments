import Merkle.Signature
import Merkle.Security

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Instantiating the library with SHA3-256

Types chosen to match `Spec.SHA3_256` from <https://github.com/ayhon/sha3.lean>, whose signature
is

    Spec.SHA3_256 : Array Bit -> Bitstring 256

with `Spec.Bit := Bool` and `Spec.Bitstring n := Vector Bool n`.

That library is *not* a dependency here: it pins Lean v4.19.0 and pulls in Aeneas and Mathlib,
whereas this project is zero-dependency on v4.34.1. Instead this file fixes the interface so
plugging it in is a one-liner, and proves what that one-liner does and does not buy you.

* `Hash256` - the type of a SHA3-256-shaped hash: `Array Bool -> Vector Bool 256`, i.e. exactly
  `Spec.SHA3_256`'s type.
* `vecToBv` - the one boundary conversion, `Vector Bool w -> BitVec w`, so the digest can be the
  `BitVec` that the counting barrier in `Merkle/Security.lean` is stated over.
* `ofHash` - **any** such function makes a `MerkleSig`. No axioms, no assumptions.
* `sig_complete`, `sig_update` - the correctness theorems instantiated at SHA3-256, proved with
  no assumptions at all.
* `no_bundle_256` - and the limit: no `MerkleHash` over a 256-bit digest exists, so the security
  theorems stay conditional.
-/

namespace Merkle.Sha3

/-- A SHA3-256-shaped hash: bits in, 256 bits out. Matches `Spec.SHA3_256`'s type exactly. -/
abbrev Hash256 := Array Bool → Vector Bool 256

/-- Read a fixed-width bit vector as a natural, most significant bit first. -/
def vecToNat (w : Nat) : Vector Bool w → Nat :=
  List.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 ∘ List.ofFn ∘ Vector.get

/-- The boundary conversion `Vector Bool w → BitVec w`. -/
def vecToBv (w : Nat) (v : Vector Bool w) : BitVec w := BitVec.ofNat w (vecToNat w v)

/-- The reverse boundary conversion, `BitVec w -> Vector Bool w`, reading most significant
bit first. -/
def bvToVec (w : Nat) (b : BitVec w) : Vector Bool w :=
  Vector.ofFn fun i : Fin w => b.getLsbD (w - 1 - i.val)

/-- Concatenate two bit vectors as an `Array Bool`, for the sponge's input. -/
def catBits {m n : Nat} (a : Vector Bool m) (b : Vector Bool n) : Array Bool :=
  a.toArray ++ b.toArray

/-- One bit of domain separation, prepended to distinguish leaf from node hashing. -/
def sepBit (b : Bool) : Array Bool := #[b]

/-- **Any** SHA3-256-shaped hash yields a Merkle signature, given an encoder for leaf values.

This is the compatibility layer: pass `Spec.SHA3_256` and a leaf encoder and you get a
`MerkleSig` outright. Nothing is assumed about the hash - not injectivity, not collision
resistance - because the correctness theorems never need it.

The `sepBit` prefixes are not required by any proof in this library (`leaf` and `node` are
already separate operations) but they are what a real deployment should emit, so that a leaf
encoding can never be mistaken for an internal node. -/
@[reducible] def ofHash {α : Type} (enc : α → Array Bool) (h : Hash256) :
    MerkleSig α (BitVec 256) where
  leaf := fun a => vecToBv 256 (h (sepBit false ++ enc a))
  node := fun a b => vecToBv 256 (h (catBits (bvToVec 256 a) (bvToVec 256 b)))

section

/-- 256-bit leaves, so that `leaf` is at least not trivially non-injective. -/
abbrev Leaf := BitVec 256

def encLeaf : Leaf → Array Bool := fun b => (bvToVec 256 b).toArray

/-- The signature obtained from an arbitrary SHA3-256 implementation. -/
abbrev sha3Sig (h : Hash256) : MerkleSig Leaf (BitVec 256) := ofHash (enc := encLeaf) h

/-- **Completeness at SHA3-256, with no assumptions.** Whatever `h` is, the honest path
verifies. -/
theorem sig_complete (h : Hash256) (n : Nat) (t : Tree Leaf n) (p : Path n) :
    Sig.fold (s := (sha3Sig h).toNodeSig) (Sig.ofTree (s := sha3Sig h) t p)
      ((sha3Sig h).leaf (t.get p)) = Sig.root (s := sha3Sig h) t := by
  exact Sig.complete (s := sha3Sig h) n t p

/-- **Incremental update at SHA3-256, with no assumptions.** -/
theorem sig_update (h : Hash256) (n : Nat) (t : Tree Leaf n) (p : Path n) (a : Leaf) :
    Sig.root (s := sha3Sig h) (t.update p a) =
      Sig.fold (s := (sha3Sig h).toNodeSig) (Sig.ofTree (s := sha3Sig h) t p)
        ((sha3Sig h).leaf a) := by
  exact Sig.update (s := sha3Sig h) n t p a

end

/-- **The limit.** No `MerkleHash` over a 256-bit digest exists, so `SigCollisionFree` cannot be
discharged here, and the security theorems (`verify_sound`, `rootHash_injective`, `no_forgery`)
cannot be applied to SHA3-256 unconditionally.

They remain available *conditionally*: were the hash collision-free, they would follow by
`merkleHashOfSig`. That hypothesis is exactly what cryptographers cannot prove of SHA3-256
either. This file records the fact rather than papering over it with an axiom - postulating
`SigCollisionFree` at this width would make the theory inconsistent, since its negation is the
theorem above. -/
theorem no_bundle_256 : ¬ Nonempty (MerkleHash Bool (BitVec 256)) :=
  Merkle.no_collision_free_bitvec 9 256 (by decide)

/-! ## Worked instantiation -/

/-- A toy hash with the *exact* type of `Spec.SHA3_256`, used only to show the bridge computes.
Replace `toyHash` with `Spec.SHA3_256` and everything below is unchanged. -/
def toyHash : Hash256 := fun bs =>
  Vector.ofFn fun i : Fin 256 => bs.toList.getD i.val false

/-- Two 256-bit leaves and a depth-two tree over them. -/
def leaf0 : BitVec 256 := BitVec.ofNat 256 0
def leaf1 : BitVec 256 := BitVec.ofNat 256 1

def demoTree : Tree Leaf 2 :=
  Tree.node (Tree.node (Tree.leaf leaf0) (Tree.leaf leaf1))
            (Tree.node (Tree.leaf leaf0) (Tree.leaf leaf1))

/-- The path to the last leaf. -/
def demoPath : Path 2 := Path.right (Path.right Path.nil)

/-- **Completeness, checked on concrete data.** The honest proof of `demoPath` verifies against
the root - proved by `sig_complete`, i.e. with no assumption about `toyHash` whatsoever. -/
example : Sig.fold (s := (sha3Sig toyHash).toNodeSig)
    (Sig.ofTree (s := sha3Sig toyHash) demoTree demoPath)
    ((sha3Sig toyHash).leaf (demoTree.get demoPath)) =
    Sig.root (s := sha3Sig toyHash) demoTree :=
  sig_complete toyHash 2 demoTree demoPath

/-- **Incremental update, checked on concrete data.** -/
example : Sig.root (s := sha3Sig toyHash)
      (demoTree.update demoPath (BitVec.ofNat 256 99)) =
    Sig.fold (s := (sha3Sig toyHash).toNodeSig)
      (Sig.ofTree (s := sha3Sig toyHash) demoTree demoPath)
      ((sha3Sig toyHash).leaf (BitVec.ofNat 256 99)) :=
  sig_update toyHash 2 demoTree demoPath (BitVec.ofNat 256 99)

end Merkle.Sha3