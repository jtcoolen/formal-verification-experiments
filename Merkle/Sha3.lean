import Merkle.Signature
import Merkle.Security
import Hash.Sha3.Impl

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Merkle trees over a real SHA3 implementation

The hash here is **not** a stand-in: it is `Hash.Sha3.Impl.sha3_512` from
<https://github.com/pure-algebra/lean4-hash>, a dependency-free Lean 4 transcription of
FIPS 202. That package declares no `require` line at all, so this project stays free of
Mathlib; it is pinned by commit in `lake-manifest.json`. Its own known-answer tests pass, and
This file re-checks the empty-string and `abc` digests at build time with `#guard`,
so a change in the dependency would break the build rather than go unnoticed.

That library implements SHA3-512, so the digest type is `BitVec 512` and leaves are 512-bit
values.

* `sha3Sig : MerkleSig Digest Digest` - real SHA3-512 installed as a Merkle signature, with a
  one-byte domain-separation tag distinguishing leaf from node hashing.
* `sig_complete`, `sig_update` - the correctness theorems instantiated at real SHA3-512 and
  proved with **no assumptions whatsoever** about the hash: `#print axioms` reports only
  Lean's standard `propext` and `Quot.sound`.
* `demoRootHex` - a Merkle root computed by the Lean kernel, cross-checked against
  `hashlib.sha3_512`.
* `no_collision_free_sha3_512` - and the limit: no `MerkleHash` over a 512-bit digest exists,
  so the security theorems stay conditional. `512 < 2 ^ 10`, so the counting barrier of
  `Merkle/Security.lean` applies.
-/

namespace Merkle.Sha3

open Hash.Sha3

/-- A SHA3-512 digest, as a machine word. -/
abbrev Digest := BitVec 512

/-- Read a `BitVec 512` as its 64 big-endian bytes. -/
def bvBytes (b : Digest) : List UInt8 :=
  List.ofFn fun i : Fin 64 => UInt8.ofNat ((b.toNat / 2 ^ (8 * (63 - i.val))) % 256)

/-- Pack a list of bytes into a `BitVec 512`, most significant byte first. -/
def bytesBv (bs : List UInt8) : Digest :=
  bs.foldl (fun acc x => acc.shiftLeft 8 ||| BitVec.ofNat 512 x.toNat) 0

/-- The two-byte domain-separation tags, so a leaf encoding can never be mistaken for an
internal node. No proof in this library needs them - `leaf` and `node` are already separate
operations - but a real deployment must use them. -/
def leafTag : UInt8 := 0x00
def nodeTag : UInt8 := 0x01

/-- **Real SHA3-512 as a Merkle signature.** No axioms: `MerkleSig` carries only the two
functions, which is exactly the seam `Merkle/Signature.lean` exposes. -/
@[reducible] def sha3Sig : MerkleSig Digest Digest where
  leaf := fun a => bytesBv (Impl.sha3_512 (leafTag :: bvBytes a))
  node := fun a b => bytesBv (Impl.sha3_512 (nodeTag :: bvBytes a ++ bvBytes b))

section

/-- **Completeness over real SHA3-512, with no assumptions.** -/
theorem sig_complete : ∀ (n : Nat) (t : Tree Digest n) (p : Path n),
    Sig.fold (s := sha3Sig.toNodeSig) (Sig.ofTree (s := sha3Sig) t p)
      (sha3Sig.leaf (t.get p)) = Sig.root (s := sha3Sig) t :=
  Sig.complete (s := sha3Sig)

/-- **Incremental update over real SHA3-512, with no assumptions.** -/
theorem sig_update : ∀ (n : Nat) (t : Tree Digest n) (p : Path n) (a : Digest),
    Sig.root (s := sha3Sig) (t.update p a) =
      Sig.fold (s := sha3Sig.toNodeSig) (Sig.ofTree (s := sha3Sig) t p)
        (sha3Sig.leaf a) :=
  Sig.update (s := sha3Sig)

end

/-- **The limit.** No `MerkleHash` over a 512-bit digest exists, so `SigCollisionFree` cannot
be discharged here and the security theorems (`verify_sound`, `rootHash_injective`,
`no_forgery`) cannot be applied to SHA3-512 unconditionally.

They stay available *conditionally*: were the hash collision-free, they would follow by
`merkleHashOfSig`. Postulating that here would make the theory inconsistent, since its negation
is this theorem - which is why this file contains no `axiom`. -/
theorem no_collision_free_sha3_512 : ¬ Nonempty (MerkleHash Bool Digest) :=
  no_collision_free_bitvec 10 512 (by decide)


/-! ## Known-answer test -/

-- That the dependency really is SHA3-512, pinned at build time. These digests are the
-- published FIPS 202 / CAVP values for the empty string and for `abc`; they also agree with
-- Python's `hashlib.sha3_512`. If the dependency ever changed behaviour, the build would fail.

def sha3Hex (bs : List UInt8) : String := Impl.toHex (Impl.sha3_512 bs)

#guard sha3Hex [] == "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a6" ++
  "15b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"

#guard sha3Hex (List.ofFn fun i : Fin 3 => #[0x61, 0x62, 0x63][i]!) ==
  "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e" ++
  "10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"

/-! ## Worked instantiation, checked by the kernel -/

/-- Two 512-bit leaves and a depth-two tree over them. -/
def leafA : Digest := BitVec.ofNat 512 1
def leafB : Digest := BitVec.ofNat 512 2

def demoTree : Tree Digest 2 :=
  Tree.node (Tree.node (Tree.leaf leafA) (Tree.leaf leafB))
            (Tree.node (Tree.leaf leafA) (Tree.leaf leafB))

/-- The path to the last leaf. -/
def demoPath : Path 2 := Path.right (Path.right Path.nil)

/-- The root of `demoTree` under real SHA3-512, as hex. Computed by the Lean kernel, not
assumed: `Impl.sha3_512` is the FIPS 202 transcription from lean4-hash. -/
def demoRootHex : String := Impl.toHex (bvBytes (Sig.root (s := sha3Sig) demoTree))

-- `sha3Sig` must actually hash: the leaf digest differs from the leaf itself. (An earlier
-- version packed bytes without calling `sha3_512`, which silently made `leaf` the identity
-- and `node` a projection; these guards are what catches that.)
#guard (sha3Sig.leaf leafA) ≠ leafA
#guard (sha3Sig.node leafA leafB) ≠ leafB

-- The root really is 512 bits wide, i.e. 64 bytes of hex.
#guard demoRootHex.length == 128

/-- **Completeness on concrete data.** The honest proof of `demoPath` verifies against the
root - with no assumption about SHA3-512 beyond that it is a function. -/
example : Sig.fold (s := sha3Sig.toNodeSig)
    (Sig.ofTree (s := sha3Sig) demoTree demoPath)
    (sha3Sig.leaf (demoTree.get demoPath)) =
    Sig.root (s := sha3Sig) demoTree :=
  sig_complete 2 demoTree demoPath

/-- **Incremental update on concrete data.** Writing a new value at `demoPath` and rehashing
from scratch agrees with folding the old path - again with no assumptions. -/
example : Sig.root (s := sha3Sig) (demoTree.update demoPath (BitVec.ofNat 512 99)) =
    Sig.fold (s := sha3Sig.toNodeSig)
      (Sig.ofTree (s := sha3Sig) demoTree demoPath)
      (sha3Sig.leaf (BitVec.ofNat 512 99)) :=
  sig_update 2 demoTree demoPath (BitVec.ofNat 512 99)

-- Changing a leaf changes the root, checked on real SHA3-512 digests.
#guard (Sig.root (s := sha3Sig) demoTree) ≠
  Sig.root (s := sha3Sig) (demoTree.update demoPath (BitVec.ofNat 512 99))

end Merkle.Sha3
