# Formally verified Merkle trees in Lean 4

> One of the projects in this repository — see the [index](../README.md). The build files for
> this project (`lakefile.lean`, `Main.lean`, `Axioms.lean`, `lean-toolchain`) live in the
> repository root, so run the commands below from the repository root.

A from-scratch, machine-checked development of binary Merkle trees in **Lean 4 on pure core
only** - no Mathlib, no `sorry`, no custom axioms.

The only dependency is [lean4-hash](https://github.com/pure-algebra/lean4-hash), a proved
FIPS 202 SHA3-512 used by `Merkle/Sha3.lean` to demonstrate the library over a real hash
function. lean4-hash declares no dependencies of its own, so Mathlib stays out of the build.

```bash
lake --wfail build  # compiles the library, examples, and regression witnesses
lake exe merkleDemo # runs a worked demonstration
lake env lean Axioms.lean   # audits every Merkle theorem for hidden axioms
lake env leanchecker --fresh Merkle # independent kernel replay
```

Requires [elan](https://github.com/leanprover/elan); the pinned toolchain is in
`lean-toolchain` (Lean 4.34.1).

## What is verified

### Correctness and security of the scheme

`rootHash_injective`, `verify_sound`, and the other bundled security theorems assume
`MerkleHash`: absolute injectivity of both hash operations. The free algebra satisfies those
assumptions; SHA3 does not. For real hashes, completeness and update correctness hold over
`MerkleSig`, and the collision reductions below need no injectivity assumptions.

| Theorem | Meaning |
|---|---|
| `Merkle.rootHash_injective` | Equal root digests imply equal trees: a root is a collision-resistant commitment to its whole leaf vector. |
| `Merkle.verify_complete` | **Completeness.** The honest authentication path of every leaf verifies. |
| `Merkle.verify_sound` | **No forgery.** If a proof verifies value `a` against `rootHash t`, then `t` really stores `a` at the path the proof itself selects. |
| `Merkle.no_forgery` | Contrapositive form: if `t` does not store `a` at `p`, no proof selecting `p` verifies `a`. |
| `Merkle.verify_two_paths` | One value cannot verify at two different paths with different contents. |
| `Merkle.rootHash_update` | **Incremental update is correct.** `rootHash (t.update p a) = verify (ofTree t p) (leaf a)` - folding an available proof agrees with rehashing. Path generation has a separate cost. |
| `Merkle.rootHash_update_get` | Writing the value already present leaves the root unchanged. |
| `Merkle.Tree.get_injective` | A tree is fully determined by its leaf map `Path n -> α`. |
| `Merkle.Tree.leaves_length` | A depth-`n` tree has exactly `2^n` leaves. |
| `Merkle.Path.allPaths_nodup` / `allPaths_length` | There are exactly `2^n` distinct paths of length `n`. |
| `Merkle.Usage.get_eq_leaves_get` | `t.get p` is the `p.toNat`-th entry of `t.leaves`; numeric indices follow left-to-right order. |
| `Merkle.Usage.allVerifyB_sound` | Executable certificate acceptance implies every value is at its claimed position, under `MerkleHash`. |
| `Merkle.Usage.allVerifyB_complete` | Honest certificates pass the executable checker. |

### Complexity (Merkle/Complexity.lean)

Lean core has no asymptotic library, so costs are stated as **exact closed forms** over a
structural model that counts hash invocations, and the big-O classification is derived from
them. These are counts for the specified recursion, not a formal semantics of generated code.
An update with an available proof needs one leaf hash and `n` node hashes. Generating that
proof with `ofTree` rehashes the sibling subtrees, so generating and folding together costs
exactly as many hash invocations as a full rehash. The tree representation has no digest cache.

| Theorem | Meaning |
|---|---|
| `Merkle.IsBigO` | Big-O on `Nat -> Nat`: `∃ c N₀, ∀ n ≥ N₀, f n ≤ c * g n`, with `refl`, `trans`, `const_mul`, `mono`. |
| `Merkle.Tree.hashCost_eq_pow` | A full rehash costs exactly `2^(n+1) - 1` hashes: `2^n` leaf hashes and `2^n - 1` node hashes. |
| `Merkle.Tree.hashCost_eq_leaves` | The same cost is `2 * t.leaves.length - 1` - **linear in the number of leaves**, which is the honest form of `O(N)`. |
| `Merkle.Path.cost_eq` | Addressing a leaf costs exactly `n` branch steps. |
| `Merkle.Proof.cost_eq` | Folding an available proof costs exactly `n` node hashes, excluding the leaf hash. |
| `Merkle.Tree.proofGenerationCost_add_depth` | Generating the proof, hashing a new leaf, and folding it costs exactly `t.hashCost`. |
| `Merkle.Usage.batchHashCost_eq` | Uncached folded batches, including their initial root, cost `(batch.length + 1) * (2^(n+1) - 1)` hashes. |
| `Merkle.Proof.digestCount_eq` | This proof format carries exactly `n` sibling digests; alternative encodings are not compared. |
| `Merkle.not_pow_isBigO_linear` | **`2^n` is not `O n`.** Full rehashing grows faster than folding an already available authentication path. |
| `Merkle.isBigO_log2_pow` / `isBigO_pow_log2` | Depth is `Θ(log N)` in the number of leaves `N = 2^n`. |

### Security bounds (Merkle/Security.lean)

| Theorem | Meaning |
|---|---|
| `Merkle.collision_or_eq` | **The main reduction, constructively.** Over any `MerkleSig`, equal roots imply equal trees or a hash collision. Requires decidable equality, without injectivity assumptions. |
| `Merkle.collision_of_rootHash_eq` | Distinct trees with equal roots yield a collision for a bare signature, including SHA3. |
| `Merkle.rootHash_ne_of_ne` | Absence of signature collisions implies distinct trees have distinct roots. |
| `Merkle.collision_of_forgery` | An accepted value that disagrees with the tree at the proof's path yields a hash collision, without injectivity assumptions. |
| `Merkle.Proof.verify_injective` | Folding a fixed path is injective on digests: no second-preimage attack through a proof. |
| `Merkle.accepting_value_unique` / `accepting_value_exists` | **The exact forgery count**: at each path exactly one value is accepted, no more and no less. No probability distribution or adversary bound is formalized. |
| `Merkle.length_allTrees` | There are exactly `2^(2^n)` distinct depth-`n` Boolean trees. |
| `Merkle.no_injection_trees` | Any map from those trees into `Fin k` with `k < 2^(2^n)` identifies two of them: a collision is **forced**, for any function whatsoever. |
| `Merkle.digest_cannot_be_small` | **No compressing collision-free hash exists.** A collision-free commitment to `2^n` bits needs at least `2^(2^n)` digest values. |
| `Merkle.modThree_notInjective` | A concrete compressing candidate, *proved* not to be injective. |
| `Merkle.no_collision_free_bitvec` | No `MerkleHash Bool (BitVec w)` exists once `w < 2^n`: fixed-width digests are ruled out by counting. |
| `Merkle.sha3_256_not_collision_free` | SHA3-256 specifically: `256 < 2^9`, so it cannot satisfy the axioms. A theorem, not a gap. |

### The signature layer (Merkle/Signature.lean)

| Theorem | Meaning |
|---|---|
| `Merkle.MerkleSig` / `Merkle.NodeSig` | The hash *functions* alone, with no assumptions - the level at which a real fixed-width hash can be installed. |
| `Merkle.SigCollisionFree` | The two collision assumptions, stated separately as a `Prop`. |
| `Merkle.Sig.complete` | Completeness over any signature, with no assumptions about the hash. |
| `Merkle.Sig.update` | Incremental update equality over any signature, with no assumptions about the hash. |
| `Merkle.merkleHashOfSig` | Adding `SigCollisionFree` recovers a full `MerkleHash`, so every other theorem applies unchanged. |
| `Merkle.sigRoot_eq_rootHash` | The two recursively defined root functions agree once the injectivity assumptions are supplied. |

### Worked applications (Merkle/Usage.lean)

`ofLeaves` / `get_ofLeaves` (build a tree from a flat vector, with both round trips proved),
`fill` / `fillHash` (sparse all-default subtrees, digested in `n` hashes instead of `2^n`),
`commit` / `commit_inj` (binding commitments to vectors), `updateAll` with
`get_updateAll_notMem` / `get_updateAll_last` / `rootHash_updateAll` (batch updates), a
fixed-size authenticated log snapshot with `history_binding` and `extension_changes_root`,
a `Claim` structure with `multi_inclusion` and `allVerifyB_sound` (set certificates), and kernel-checked scenarios over `Dig Nat`,
`Dig String` and `Dig (Fin 256)`.

A certificate's Boolean checker tests both the root digest and
`Proof.pathOf c.proof = c.path`. `allVerifyB_eq` relates it to `certificateValid`, which includes
both conditions. `allVerify` remains available as the root-only predicate. Checked examples
show that a proof relabeled as a different position fails the complete checker.

The log examples establish snapshot binding and detection of changed entries. They do not
define append, growth, or prefix consistency between successive log heads.

## How it is put together

### Types make the wrong cases untypeable

```lean
inductive Tree (α : Type) : Nat → Type where
  | leaf : α → Tree α 0
  | node : Tree α n → Tree α n → Tree α (n + 1)

inductive Path : Nat → Type where
  | nil : Path 0
  | left : Path n → Path (n + 1)
  | right : Path n → Path (n + 1)
```

Both are **indexed by depth**. `t.get p` therefore requires `t : Tree α n` and `p : Path n` for
the *same* `n`: there is no way to address a leaf of the wrong tree, to hand a proof a path from
a bigger tree, or to compare trees of different heights. Those are not unprovable lemmas that
you must remember to state - they are ill-typed expressions.

### The hash algebra is abstract

```lean
class NodeAlgebra (β : Type) where
  node : β → β → β
  collFree : ∀ {a b c d : β}, node a b = node c d → a = c ∧ b = d

class MerkleHash (α β : Type) extends NodeAlgebra β where
  leaf : α → β
  leafInjective : Function.Injective leaf
```

The ideal-algebra security theorems quantify over all instances of this class. The signature
collision reductions do not require this class. Two design points matter:

* **Proofs and trees share a fixed depth.** `verify_sound` uses node injectivity at each level
  and leaf injectivity at the base. It needs no additional disjointness assumption between
  leaf and node digest ranges; it makes no claim about comparisons across tree depths.
* **`collFree` is injectivity of the combiner**, which is exactly "no collisions for the internal
  node hash" as an absolute property. This idealized assumption is stronger than computational
  collision resistance and is impossible for nontrivial finite digest types.

### The no-forgery theorem, read as a game

```lean
theorem verify_sound {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (h : Proof β n) (a : α),
      verify h (m.leaf a) = rootHash t → t.get (Proof.pathOf h) = a
```

The attacker sees `rootHash t` and outputs a proof `h` plus a value `a`; they win if it
verifies while the tree disagrees. `pathOf` reads the target leaf out of the proof's own
direction bits, so the attacker cannot aim a proof at a leaf it does not claim to open. The
proof is a two-line induction: `collFree` splits the top node, `leafInjective` closes the base
case.

### The honest limitation

A deployment wants short digests. But collision-freeness *is* injectivity, so `leaf : α → β`
needs `|α| ≤ |β|` and `node : β → β → β` needs `|β|² ≤ |β|` - which fails for any finite `β`
with `|β| ≥ 2`. **No finite digest type can satisfy `MerkleHash` for an unbounded leaf type.**

The library proves a related counting obstruction:
`digest_cannot_be_small` derives a contradiction from a collision-free `MerkleHash Bool β`
together with an injection `β → Fin k` for any `k < 2^(2^n)`, by enumerating all `2^(2^n)`
depth-`n` Boolean trees (`allTrees`, with `nodup_allTrees` and `complete_allTrees`) and
applying a pigeonhole argument.

A concrete fixed-width instantiation must not postulate this absolute injectivity: it would
contradict the counting results. Real hashes use `MerkleSig` and the assumption-free collision
reductions. `Merkle/Free.lean` instantiates the ideal theorems over the **free** algebra

```lean
inductive Dig (α : Type) : Type where
  | leaf : α → Dig α
  | node : Dig α → Dig α → Dig α
```

whose two axioms hold by constructor injectivity. This makes the security theorems non-vacuous:
they apply to a concrete, computable algebra whose collision-freeness is a *theorem*.

## Using a real hash: the signature layer

`MerkleHash` bundles the two hash *functions* with the two collision *assumptions*. That is
great for stating security theorems and useless for installing SHA3, because the assumptions are
false for every fixed-width digest - so you could not even *compute* a SHA3 Merkle root.
`Merkle/Signature.lean` splits the bundle along exactly that seam:

```lean
class NodeSig (β : Type) where
  node : β → β → β

class MerkleSig (α β : Type) extends NodeSig β where
  leaf : α → β

class SigCollisionFree {α β : Type} [s : MerkleSig α β] : Prop where
  nodeInjective : ∀ {a b c d : β}, s.node a b = s.node c d → a = c ∧ b = d
  leafInjective : Function.Injective s.leaf
```

`Sig.root`, `Sig.fold`, `Sig.ofTree`, `Sig.complete` and `Sig.update` live at the signature level
and hold for **any** pair of functions, with no assumptions about the hash.
`merkleHashOfSig` adds `SigCollisionFree` back to recover a full `MerkleHash` for ideal models.
The separate collision reductions operate directly over `MerkleSig`.

`Merkle/Sha3.lean` installs a **real** hash: `Hash.Sha3.Impl.sha3_512` from
[lean4-hash](https://github.com/pure-algebra/lean4-hash), a dependency-free Lean 4 transcription
of FIPS 202, pinned by commit in `lake-manifest.json`.

```lean
abbrev Digest := BitVec 512

@[reducible] def sha3Sig : MerkleSig Digest Digest where
  leaf := fun a => bytesBv (Impl.sha3_512 (leafTag :: bvBytes a))
  node := fun a b => bytesBv (Impl.sha3_512 (nodeTag :: bvBytes a ++ bvBytes b))
```

That gives a working Merkle tree over SHA3-512 - root, proofs, verification, incremental
updates - with **zero assumptions about the hash**. `sig_complete` and `sig_update` audit to
`propext` and `Quot.sound` only.

Two things keep the dependency honest at build time. The SHA3-512 known-answer vectors for the
empty string and for `abc` are pinned with `#guard`, so a change in the dependency fails the
build rather than going unnoticed; and the file guards that `sha3Sig` actually hashes
(`leaf a ≠ a`, `node a b ≠ b`), which caught a real bug during development - an earlier version
packed bytes into `BitVec 512` without calling `sha3_512`, silently making `leaf` the identity
and `node` a projection. The computed Merkle root also agrees byte-for-byte with Python's
`hashlib.sha3_512` under the same tagging scheme.

What it deliberately does **not** do is postulate `SigCollisionFree` for a 512-bit digest. That
would make the theory inconsistent, because the library proves it impossible:

```lean
theorem no_collision_free_bitvec (n w : Nat) (h : w < 2 ^ n) :
    ¬ Nonempty (MerkleHash Bool (BitVec w))

theorem no_collision_free_sha3_512 : ¬ Nonempty (MerkleHash Bool (BitVec 512)) :=   -- 512 < 2^10
  no_collision_free_bitvec 10 512 (by decide)
```

A 512-bit digest holds `2^512` values; depth-10 Boolean trees number `2^(2^10) = 2^1024`.

### Worked examples over SHA3-512

`Merkle/Sha3/Examples.lean` drives the application layer of `Merkle/Usage.lean` with the real
hash. Sample digests are pinned with `#guard` (compiled build-time evaluation); the theorem
proofs are checked by the Lean kernel:

| Example | What it shows |
|---|---|
| `kv` / `kvRoot` | A four-name key-value commitment; the root is pinned against an independent implementation. |
| `get_update_other` | Overwriting one entry provably leaves every other entry alone. |
| `sparseTree` / `sroot_fill` | A depth-3 all-default subtree: 15 hashes the naive way, 4 the sparse way, proved equal by induction. |
| `log` / `logRoot` | A 16-entry authenticated log snapshot with a pinned root and leaf digest. |
| `batch` / `get_updateAll_notMem` | Batch writes; untouched entries provably unchanged. |
| `cert` / `cert_verifies` / `allVerifyB` | A three-entry multi-inclusion certificate, verified and decidable - a client needs no proof assistant. |
| `tampered` / `mislabeled` | Wrong values and relabeled positions are rejected by the executable check. |
| `binding_reduction` | Distinct snapshots with equal roots produce a collision in `bytesSig`. |
| `allVerifyB_false_claim_collision` | Executable acceptance of a false claim produces a collision in `bytesSig`. |
| `bytesSig_not_collision_free` | Absolute injectivity is impossible for this fixed-width signature. |

The SHA3 reductions make no impossible injectivity assumption. They do not prove that finding
a collision is infeasible, and do not formalize adversary running time or success probability.
## Axiom audit

`Axioms.lean` does not list theorem names by hand - it walks every theorem in the `Merkle`
namespace in the compiled environment, so it cannot silently rot as the library grows:

```
$ lake env lean Axioms.lean
theorems audited in Merkle.* / Sha3.*: 283
OK - every theorem depends only on propext and Quot.sound
      (no sorryAx, no Classical.choice)
```

The absence of `Classical.choice` is worth pointing at: it means no proof quietly used excluded
middle or a decidability-of-propositional-equality instance. In particular `collision_or_eq`
proves the dichotomy `Collision ∨ t₁ = t₂` using explicit decidable comparisons of values and
digests, and the pigeonhole argument filters lists by `decide (x ≠ j)`
instead of `erase`, which in Lean core does use choice.

## Layout

```
Merkle/Basic.lean      trees, paths, the hash algebra, rootHash_injective
Merkle/Proof.lean      authentication paths, verify, verify_sound, rootHash_update
Merkle/Free.lean       the free algebra Dig - the model that discharges the axioms
Merkle/Complexity.lean exact cost closed forms, IsBigO, not_pow_isBigO_linear
Merkle/Signature.lean  MerkleSig / SigCollisionFree - the axiom seam
Merkle/Security.lean   collision extractor, forgery counts, digest-size barrier
Merkle/Usage.lean      vectors, sparse trees, uncached batches, snapshots, complete certificates
Merkle/Regression.lean checked colliding signatures, numeric addressing, and boundary costs
Merkle/Sha3.lean       real SHA3-512 (via lean4-hash) installed as a signature
Merkle/Sha3/Examples.lean  those applications driven by SHA3-512, with pinned digests
Main.lean              `lake exe merkleDemo`
Axioms.lean            `lake env lean Axioms.lean` - the axiom audit
```

## Demo output

```
$ lake exe merkleDemo
demoTree leaves : [0, 1, 2, 3, 4, 5, 6, 7]
leaf count : 8 (2 ^ 3 = 8)
demoPath : RLR - addresses leaf index 5, holds the value 5
root digest : (((0,1),(2,3)),((4,5),(6,7)))
honest proof verifies : true
forged value 42 verifies : false

--- cost accounting ---
full rehash of a depth-3 tree : 15 hashes
folding an available proof    : 3 node hashes
update with available proof   : 4 hashes (including the leaf)
generating the uncached proof : 11 hashes
generate proof + update       : 15 hashes
proof carries                 : 3 sibling digests (= log2 of leaf count)
saving with available proof   : 11 hashes

--- sparse subtrees ---
a depth-10 all-zero tree has 1024 leaves
hashing it leaf by leaf costs 2047 hashes
a sparse digest needs 1 leaf + 10 node hashes: 11

--- counting bound ---
distinct depth-4 Boolean trees : 65536
a 15-bit digest must collide on depth-4 trees: true
depth-9 Boolean trees (512 leaves) need 2^(2^9) = 2^512 values:
  2^(2^9) > 2^256, so a 256-bit hash MUST collide: true
```

## API changes from the reviewed version

* `Path.toNat` now uses left-to-right indices, matching `Tree.leaves`; `leafIndex` is an alias.
* `allVerifyB` checks claimed positions as well as root digests. `allVerifyB_eq` now targets
  `certificateValid`; `allVerify` retains its root-only meaning.
* `Collision` and the extraction theorems take a `MerkleSig` parameter named `s`, use
  `Sig.root`, and require decidable equality for extraction. They no longer require `MerkleHash`.
* The vacuous SHA3 `binding_conditional` example is replaced by `binding_reduction` and
  `inclusion_reduction`, with an executable-checker reduction as well.

## License

MIT. See [LICENSE](../LICENSE).
