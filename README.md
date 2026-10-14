# Formally verified Merkle trees in Lean 4

A from-scratch, machine-checked development of binary Merkle trees in **Lean 4 with no
dependencies** - pure Lean core, no Mathlib, no `sorry`, no custom axioms.

```bash
lake build          # compiles the whole library in a few seconds
lake exe merkleDemo # runs a worked demonstration
lake env lean Axioms.lean   # audits every theorem for hidden axioms
```

Requires [elan](https://github.com/leanprover/elan); the pinned toolchain is in
`lean-toolchain` (Lean 4.34.1).

## What is verified

### Correctness and security of the scheme

| Theorem | Meaning |
|---|---|
| `Merkle.rootHash_injective` | Equal root digests imply equal trees: a root is a collision-resistant commitment to its whole leaf vector. |
| `Merkle.verify_complete` | **Completeness.** The honest authentication path of every leaf verifies. |
| `Merkle.verify_sound` | **No forgery.** If a proof verifies value `a` against `rootHash t`, then `t` really stores `a` at the path the proof itself selects. |
| `Merkle.no_forgery` | Contrapositive form: if `t` does not store `a` at `p`, no proof selecting `p` verifies `a`. |
| `Merkle.verify_two_paths` | One value cannot verify at two different paths with different contents. |
| `Merkle.rootHash_update` | **Incremental update is correct.** `rootHash (t.update p a) = verify (ofTree t p) (leaf a)` - the `O(n)` shortcut agrees with the `O(2^n)` rehash. |
| `Merkle.rootHash_update_get` | Writing the value already present leaves the root unchanged. |
| `Merkle.Tree.get_injective` | A tree is fully determined by its leaf map `Path n -> α`. |
| `Merkle.Tree.leaves_length` | A depth-`n` tree has exactly `2^n` leaves. |
| `Merkle.Path.allPaths_nodup` / `allPaths_length` | There are exactly `2^n` distinct paths of length `n`. |

### Complexity (Merkle/Complexity.lean)

Lean core has no asymptotic library, so costs are stated as **exact closed forms** over a
model that counts hash invocations, and the big-O classification is derived from them.

| Theorem | Meaning |
|---|---|
| `Merkle.IsBigO` | Big-O on `Nat -> Nat`: `∃ c N₀, ∀ n ≥ N₀, f n ≤ c * g n`, with `refl`, `trans`, `const_mul`, `mono`. |
| `Merkle.Tree.hashCost_eq_pow` | A full rehash costs exactly `2^(n+1) - 1` hashes: `2^n` leaf hashes and `2^n - 1` node hashes. |
| `Merkle.Tree.hashCost_eq_leaves` | The same cost is `2 * t.leaves.length - 1` - **linear in the number of leaves**, which is the honest form of `O(N)`. |
| `Merkle.Path.cost_eq` | Addressing a leaf costs exactly `n` branch steps. |
| `Merkle.Proof.cost_eq` | Verifying a proof costs exactly `n` node hashes. |
| `Merkle.Proof.digestCount_eq` | A proof carries exactly `n` sibling digests - the optimal authentication-path size, not merely a bound. |
| `Merkle.not_pow_isBigO_linear` | **`2^n` is not `O n`.** The rehash cost cannot be improved to linear, so the incremental update is an asymptotic separation, not a constant-factor win. |
| `Merkle.isBigO_log2_pow` / `isBigO_pow_log2` | Depth is `Θ(log N)` in the number of leaves `N = 2^n`. |

### Security bounds (Merkle/Security.lean)

| Theorem | Meaning |
|---|---|
| `Merkle.collision_or_eq` | **The main reduction, constructively.** Equal roots imply the trees are equal *or* a concrete collision in the hash algebra is exhibited. No classical case split. |
| `Merkle.collision_of_rootHash_eq` | Distinct trees with equal roots refute collision-freeness, with the witness. |
| `Merkle.rootHash_ne_of_ne` | A collision-free algebra makes the root a perfect commitment. |
| `Merkle.Proof.verify_injective` | Folding a fixed path is injective on digests: no second-preimage attack through a proof. |
| `Merkle.accepting_value_unique` / `accepting_value_exists` | **The exact forgery count**: at each path exactly one value is accepted, no more and no less. This is the theorem behind the `1/|α|` guessing bound. |
| `Merkle.length_allTrees` | There are exactly `2^(2^n)` distinct depth-`n` Boolean trees. |
| `Merkle.no_injection_trees` | Any map from those trees into `Fin k` with `k < 2^(2^n)` identifies two of them: a collision is **forced**, for any function whatsoever. |
| `Merkle.digest_cannot_be_small` | **No compressing collision-free hash exists.** A collision-free commitment to `2^n` bits needs at least `2^(2^n)` digest values. |
| `Merkle.modThree_notInjective` | A concrete compressing candidate, *proved* not to be injective. |

### Worked applications (Merkle/Usage.lean)

`ofLeaves` / `get_ofLeaves` (build a tree from a flat vector, with both round trips proved),
`fill` / `fillHash` (sparse all-default subtrees, digested in `n` hashes instead of `2^n`),
`commit` / `commit_inj` (binding commitments to vectors), `updateAll` with
`get_updateAll_notMem` / `get_updateAll_last` / `rootHash_updateAll` (batch updates), a
transparency log with `history_binding` and `extension_changes_root`, a `Claim` structure with
`multi_inclusion` (set certificates), and kernel-checked scenarios over `Dig Nat`,
`Dig String` and `Dig (Fin 256)`.

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

Every security theorem is quantified over *all* instances, so the proofs are reusable and the
assumptions are visible in one place. Two design points matter:

* **Leaves go through `leaf`, not `node`.** This is what makes `verify_sound` close without any
  domain-separation hypothesis. If leaves were hashed with the same combiner, an attacker could
  re-bracket digests and the induction would not pin down the leaf.
* **`collFree` is injectivity of the combiner**, which is exactly "no collisions for the internal
  node hash" - the standard assumption, stated in the weakest form the proofs actually need.

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

Unlike most formalizations, this one *proves* that rather than remarking it:
`digest_cannot_be_small` derives a contradiction from a collision-free `MerkleHash Bool β`
together with an injection `β → Fin k` for any `k < 2^(2^n)`, by enumerating all `2^(2^n)`
depth-`n` Boolean trees (`allTrees`, with `nodup_allTrees` and `complete_allTrees`) and
applying a pigeonhole argument.

So a real instantiation must `axiomatize` collision-freeness of its compression function; that
is the ordinary status of hash assumptions, not an artifact of this formalization. Rather than
smuggle in an axiom, `Merkle/Free.lean` instantiates the theorems over the **free** algebra

```lean
inductive Dig (α : Type) : Type where
  | leaf : α → Dig α
  | node : Dig α → Dig α → Dig α
```

whose two axioms hold by constructor injectivity. This makes the security theorems non-vacuous:
they apply to a concrete, computable algebra whose collision-freeness is a *theorem*.

## Axiom audit

`Axioms.lean` does not list theorem names by hand - it walks every theorem in the `Merkle`
namespace in the compiled environment, so it cannot silently rot as the library grows:

```
$ lake env lean Axioms.lean
theorems audited in Merkle.*: 230
OK - every theorem depends only on propext and Quot.sound
      (no sorryAx, no Classical.choice)
```

The absence of `Classical.choice` is worth pointing at: it means no proof quietly used excluded
middle or a decidability-of-propositional-equality instance. In particular `collision_or_eq`
proves the dichotomy `Collision ∨ t₁ = t₂` constructively rather than by case-splitting on
whether the trees are equal, and the pigeonhole argument filters lists by `decide (x ≠ j)`
instead of `erase`, which in Lean core does use choice.

## Layout

```
Merkle/Basic.lean      trees, paths, the hash algebra, rootHash_injective
Merkle/Proof.lean      authentication paths, verify, verify_sound, rootHash_update
Merkle/Free.lean       the free algebra Dig - the model that discharges the axioms
Merkle/Complexity.lean exact cost closed forms, IsBigO, not_pow_isBigO_linear
Merkle/Security.lean   collision extractor, forgery counts, digest-size barrier
Merkle/Usage.lean      worked applications: vectors, sparse trees, batches, logs
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
incremental update            : 3 hashes
proof carries                 : 3 sibling digests (= log2 of leaf count)
saving on this tree           : 12 hashes

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

## License

MIT. See [LICENSE](LICENSE).
