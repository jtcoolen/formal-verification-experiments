import Merkle.Sha3
import Merkle.Usage
import Merkle.Complexity

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Worked examples: Merkle trees over real SHA3-512

Applications built on the real SHA3-512 from lean4-hash, installed through the signature layer
of `Merkle/Signature.lean`. Every example is a proved theorem or a build-time-checked
computation (`#guard`), and **none of them assumes anything about SHA3** - not collision
resistance, not injectivity, not even that the output is hard to invert.

That is the point of the split: the correctness half of a Merkle tree is unconditional, and
these examples exercise it end to end over the installed hash. The security reductions below
turn accepted false claims and equal-root distinct trees into hash collisions without assuming
absolute injectivity.

* `bytesSig` - SHA3-512 over byte-string leaves, the shape a real deployment uses.
* `kvRoot` and the key-value examples - a four-entry store: pinned root, independent lookups,
  inclusion proof, tamper rejection.
* `sparseSigRoot_eq` - a sparse all-default subtree, digested in `n` hashes instead of `2 ^ n`,
  with the cheap and expensive routes proved equal.
* `log` and the ledger examples - a 16-entry authenticated log snapshot: pinned root, inclusion, tamper
  detection, and batch writes.
* `cert` - a multi-inclusion certificate for three entries at once, checked against one root.
* `binding_reduction` / `inclusion_reduction` - equal-root distinct trees and accepted
  false claims produce hash collisions, without any injectivity assumption.
-/

namespace Merkle.Sha3.Examples

open Merkle Merkle.Sha3 Merkle.Usage Hash.Sha3

/-- Byte-string leaves: the shape a real deployment uses, where the tree commits to messages
rather than to pre-hashed words. -/
abbrev Msg := List UInt8

@[reducible] def bytesSig : MerkleSig Msg Digest where
  leaf := fun m => bytesBv (Impl.sha3_512 (leafTag :: m))
  node := fun a b => bytesBv (Impl.sha3_512 (nodeTag :: bvBytes a ++ bvBytes b))

/-- Shorthands so the examples read as one layer. -/
abbrev sroot {n : Nat} : Tree Msg n → Digest := Sig.root (s := bytesSig)
abbrev sfold : Proof Digest n → Digest → Digest :=
  Sig.fold (s := bytesSig.toNodeSig)
abbrev sofTree {n : Nat} : Tree Msg n → Path n → Proof Digest n :=
  Sig.ofTree (s := bytesSig)
abbrev sleaf : Msg → Digest := bytesSig.leaf

/-! ## A key-value commitment -/

/-- Four short messages: `alice`, `bob`, `carol`, `dave`. -/
def entries : List Msg :=
  [List.ofFn fun i : Fin 5 => #[0x61, 0x6c, 0x69, 0x63, 0x65][i]!,
   List.ofFn fun i : Fin 3 => #[0x62, 0x6f, 0x62][i]!,
   List.ofFn fun i : Fin 5 => #[0x63, 0x61, 0x72, 0x6f, 0x6c][i]!,
   List.ofFn fun i : Fin 4 => #[0x64, 0x61, 0x76, 0x65][i]!]

#guard entries.length = 4

/-- The tree, built from the flat vector. -/
def kv : Tree Msg 2 := ofLeaves 2 entries (by decide)

/-- The committed root, computed and pinned against an independent
implementation, so a change in the dependency or the tagging breaks the build. -/
def kvRoot : String := Impl.toHex (bvBytes (sroot kv))

#guard kvRoot = "5f2cf7f5c131aa39dd192637274fe5e19c1a9c328d7b9516e5ffaa4e2aaf5037" ++
  "be86b30ea7d81fc77ce58bc49e00372ecb82a3ac31a4c6694215357720cc7712"

/-- Paths to entries 1 and 3. `leafIndex` numbers leaves left-to-right with the *topmost*
branch as the most significant bit, so index 1 is `L R` and index 3 is `R R`. -/
def p1 : Path 2 := Path.left (Path.right Path.nil)
def p3 : Path 2 := Path.right (Path.right Path.nil)

-- The tree really holds the entries we put in.
#guard kv.get p1 = entries[1]!
#guard kv.get p3 = entries[3]!

/-- **Lookups are independent.** Overwriting one entry leaves every other entry alone - the
property a key-value store needs, and it holds with no assumptions about SHA3. -/
example : (kv.update p1 entries[0]!).get p3 = entries[3]! :=
  Tree.get_update_other entries[0]! kv (Path.left_ne_right _ _)

/-- **Completeness.** The honest proof of entry 3 verifies against the pinned root. -/
example : sfold (sofTree kv p3) (sleaf (kv.get p3)) = sroot kv :=
  Sig.complete (s := bytesSig) 2 kv p3

-- **Tamper detection on real digests.** Claiming a different value at the same path does not
-- verify. This computation checks that the honest proof produces a different digest.
-- This finite check does not establish universal absence of forgeries. The theorem
-- `inclusion_reduction` below shows that any accepted false claim would yield a hash collision.
#guard sfold (sofTree kv p3) (sleaf entries[2]!) ≠ sroot kv


/-! ## Sparse subtrees -/

/-- The digest of an all-default subtree, computed **without** building the tree: one leaf
hash plus `n` node hashes, instead of `2 ^ n` leaf hashes and `2 ^ n - 1` node hashes. This is
the signature-level analogue of `Merkle.Usage.fillHash`. -/
def sparseHash : Nat → Msg → Digest
  | 0, a => sleaf a
  | n + 1, a => bytesSig.node (sparseHash n a) (sparseHash n a)

/-- A depth-3 all-empty tree, and the cheap digest of it. -/
def sparseTree : Tree Msg 3 := fill 3 []

/-- The digest of the sparse subtree, as hex. -/
def sparseRoot : String := Impl.toHex (bvBytes (sroot sparseTree))

/-- **The cheap route and the expensive route agree.** Proved by induction on the depth, with
no assumptions about SHA3. -/
theorem sroot_fill : ∀ (n : Nat) (a : Msg), sroot (fill n a) = sparseHash n a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
      intro a
      show bytesSig.node (sroot (fill n a)) (sroot (fill n a)) =
        bytesSig.node (sparseHash n a) (sparseHash n a)
      rw [ih a]

-- Concretely, for the depth-3 all-empty tree, pinned against the independent implementation.
#guard Impl.toHex (bvBytes (sroot sparseTree)) =
  "a303f8fbac93f4d3c0aeb35b530bb380dd15aa10b2c5296b34b2df4c425c4c48" ++
  "8f5cd37578f50689b6c92cbd163f9c42e06713ca1ece29dda2c741c5ce19a405"

#guard sroot sparseTree = sparseHash 3 []

/-- **Every leaf of a sparse subtree reads back the default**, whatever path you pick. -/
example : ∀ (q : Path 3), sparseTree.get q = [] := fun q => get_fill 3 [] q

-- The cost gap, made concrete: 15 hashes the naive way, 4 the sparse way.
#guard sparseTree.hashCost = 15
#guard (3 : Nat) + 1 = 4

/-! ## An authenticated log snapshot -/

/-- A 16-entry log; entry `i` is the single byte `i`. -/
def logEntries : List Msg := List.ofFn fun i : Fin 16 => [UInt8.ofNat i.val]

#guard logEntries.length = 16

def log : Tree Msg 4 := ofLeaves 4 logEntries (by decide)

def logRoot : String := Impl.toHex (bvBytes (sroot log))

#guard logRoot = "ae92be9b48fbca02d370418eeec5a4f8f2eb4a389b373d2ed7da6227a79dfbfd" ++
  "af9489018bc32bf5b895824cf51d468063522322132e4f0fcdbdb83a31efc833"

/-- The path addressing entry 11: `leafIndex` reads the topmost branch as the most
significant bit, so 11 = 8 + 2 + 1 is `R L R R`. -/
def logPath : Path 4 := Path.right (Path.left (Path.right (Path.right Path.nil)))

#guard log.get logPath = logEntries[11]!

example : sfold (sofTree log logPath) (sleaf (log.get logPath)) = sroot log :=
  Sig.complete (s := bytesSig) 4 log logPath

-- The leaf digest a client would check, pinned.
#guard Impl.toHex (bvBytes (sleaf logEntries[11]!)) =
  "7aa2cda5ef48c31aba34790231bfb37640b6de2abf7eb614027d8f5ef0993bc8" ++
  "9d4bcd5d57c8519ed4d5958772eabf8ab1a6abab1eac779206c56c284bf8592a"

-- **Tampering with an entry changes the root** - a pure computation over SHA3-512.
#guard sroot (log.update logPath [UInt8.ofNat 12]) ≠ sroot log

/-- Writing back the value already present leaves the root alone. -/
example : sroot (log.update logPath (log.get logPath)) = sroot log :=
  ((Sig.update (s := bytesSig) 4 log logPath (log.get logPath)).trans
    (Sig.complete (s := bytesSig) 4 log logPath))


/-! ## Batch writes -/

/-- Two writes applied as one batch: entry 11 and entry 0. -/
def logPath0 : Path 4 := Path.left (Path.left (Path.left (Path.left Path.nil)))

def batch : Tree Msg 4 := updateAll log [(logPath, [UInt8.ofNat 100]),
  (logPath0, [UInt8.ofNat 200])]

#guard (batch.get logPath) = [UInt8.ofNat 100]
#guard (batch.get logPath0) = [UInt8.ofNat 200]

/-- **An untouched entry is unchanged by the batch.** -/
def pUntouched : Path 4 := Path.left (Path.left (Path.left (Path.right Path.nil)))

example : batch.get pUntouched = log.get pUntouched :=
  get_updateAll_notMem (t := log)
    (l := [(logPath, [UInt8.ofNat 100]), (logPath0, [UInt8.ofNat 200])])
    pUntouched (by decide)

/-! ## A multi-inclusion certificate -/

/-- Three entries opened together against the one root. `Usage.Claim` is stated over
`MerkleHash`, so the certificate is spelled out at the signature level instead. -/
def certPaths : List (Path 4) := [logPath0,
  Path.left (Path.right (Path.left (Path.right Path.nil))), logPath]

structure SigClaim (n : Nat) where
  path : Path n
  value : Msg
  proof : Proof Digest n

def verifiesAt (root : Digest) (c : SigClaim n) : Prop :=
  Proof.pathOf c.proof = c.path ∧ sfold c.proof (sleaf c.value) = root

def cert : List (SigClaim 4) :=
  certPaths.map (fun p => SigClaim.mk p (log.get p) (sofTree log p))

theorem cert_verifies : ∀ c ∈ cert, verifiesAt (sroot log) c := by
  intro c hc
  have hc' : c ∈ certPaths.map (fun p => SigClaim.mk p (log.get p) (sofTree log p)) := hc
  rw [List.mem_map] at hc'
  obtain ⟨p, hp, rfl⟩ := hc'
  exact ⟨Sig.pathOf_ofTree (s := bytesSig) 4 log p,
    Sig.complete (s := bytesSig) 4 log p⟩

/-- The certificate is decidable, so a client can check it without a proof assistant. -/
def allVerifyB (root : Digest) (cs : List (SigClaim 4)) : Bool :=
  cs.all (fun c => decide (c.proof.pathOf = c.path ∧
    sfold c.proof (sleaf c.value) = root))

/-- The executable SHA3 checker establishes the complete claim predicate. -/
theorem allVerifyB_eq (root : Digest) (cs : List (SigClaim 4)) :
    allVerifyB root cs = true ↔ ∀ c ∈ cs, verifiesAt root c := by
  unfold allVerifyB
  rw [List.all_eq_true]
  constructor
  · intro h c hc
    change c.proof.pathOf = c.path ∧ sfold c.proof (sleaf c.value) = root
    exact of_decide_eq_true (h c hc)
  · intro h c hc
    exact decide_eq_true (show c.proof.pathOf = c.path ∧
      sfold c.proof (sleaf c.value) = root from h c hc)

#guard allVerifyB (sroot log) cert = true

-- A certificate with one tampered value is rejected.
def tampered : SigClaim 4 :=
  { path := logPath0, value := [UInt8.ofNat 999], proof := sofTree log logPath0 }

#guard allVerifyB (sroot log) (tampered :: cert) = false

-- A proof with only its claimed position changed is also rejected.
def mislabeled : SigClaim 4 :=
  { path := logPath, value := log.get logPath0, proof := sofTree log logPath0 }

#guard allVerifyB (sroot log) [mislabeled] = false

/-! ## Security reductions over the installed hash -/

/-- Distinct snapshots with equal SHA3 roots produce a collision in `bytesSig`.
No collision-freeness hypothesis is assumed. This is a deterministic reduction, without a
probabilistic bound on the difficulty of finding such snapshots. -/
theorem binding_reduction {n : Nat} (t₁ t₂ : Tree Msg n)
    (heq : sroot t₁ = sroot t₂) (hne : t₁ ≠ t₂) : Collision (s := bytesSig) :=
  collision_of_rootHash_eq (s := bytesSig) n t₁ t₂ heq hne

/-- An accepted false claim yields a SHA3 collision. The claim's path must match the proof,
which is checked by `verifiesAt` and the Boolean verifier. -/
theorem inclusion_reduction {n : Nat} (t : Tree Msg n) (c : SigClaim n)
    (hv : verifiesAt (sroot t) c) (hne : t.get c.path ≠ c.value) :
    Collision (s := bytesSig) := by
  apply collision_of_forgery (s := bytesSig) t c.proof c.value hv.2
  rw [hv.1]
  exact hne

/-- End-to-end reduction: an executable accepted certificate containing a false claim
produces a collision, with no assumptions about SHA3. -/
theorem allVerifyB_false_claim_collision (t : Tree Msg 4) (cs : List (SigClaim 4))
    (h : allVerifyB (sroot t) cs = true) (c : SigClaim 4) (hc : c ∈ cs)
    (hne : t.get c.path ≠ c.value) : Collision (s := bytesSig) :=
  inclusion_reduction t c ((allVerifyB_eq _ _).mp h c hc) hne

/-- Absolute injectivity is impossible for this fixed-width signature. The reductions above
therefore avoid using it as a premise. -/
theorem bytesSig_not_collision_free : ¬ SigCollisionFree (s := bytesSig) := by
  intro cf
  exact no_collision_free_bitvec_of_two (α := Msg) [] [UInt8.ofNat 1]
    (by decide) 10 512 (by decide) ⟨
    { node := bytesSig.node,
      collFree := @SigCollisionFree.nodeInjective Msg Digest bytesSig cf,
      leaf := bytesSig.leaf,
      leafInjective := @SigCollisionFree.leafInjective Msg Digest bytesSig cf }⟩

end Merkle.Sha3.Examples
