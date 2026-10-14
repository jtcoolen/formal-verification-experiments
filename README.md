# Formally verified Merkle trees in Lean 4

A from-scratch, machine-checked development of binary Merkle trees in **Lean 4 with no
dependencies** - pure Lean core, no Mathlib, no `sorry`, no custom axioms.

```bash
lake build          # compiles the whole library in a few seconds
lake exe merkleDemo # runs a worked demonstration
```

Requires [elan](https://github.com/leanprover/elan); the pinned toolchain is in
`lean-toolchain` (Lean 4.34.1).

## What is verified

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
| `Merkle.Examples.modThree_notInjective` | A concrete compressing candidate, *proved* not to be injective. |
| `Merkle.Examples.no_injection_two_into_one` | The counting fact that rules out finite compressing digests. |

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

So a real instantiation must `axiomatize` collision-freeness of its compression function; that
is the ordinary status of hash assumptions, not an artifact of this formalization. Rather than
smuggle in an axiom, `Merkle/Examples.lean` instantiates the theorems over the **free** algebra

```lean
inductive Dig (α : Type) : Type where
  | leaf : α → Dig α
  | node : Dig α → Dig α → Dig α
```

whose two axioms hold by constructor injectivity. This makes the security theorems non-vacuous:
they apply to a concrete, computable algebra whose collision-freeness is a *theorem*. The same
file proves `modThree_notInjective`, a concrete compressing map with an explicit collision.

## Axiom audit

```
$ lake env lean Axioms.lean
'Merkle.verify_sound'        depends on axioms: [propext]
'Merkle.rootHash_injective'  depends on axioms: [propext]
'Merkle.rootHash_update'     depends on axioms: [propext]
...
```

Every theorem depends only on Lean's standard logical axioms (`propext`, `Quot.sound`). No
`Classical.choice`, no `sorryAx`, no hash axioms. Reproduce with `lake env lean Axioms.lean`.

## Layout

```
Merkle/Basic.lean     trees, paths, the hash algebra, rootHash_injective
Merkle/Proof.lean     authentication paths, verify, verify_sound, rootHash_update
Merkle/Examples.lean  the free algebra instantiation, the compressing-hash barrier
Main.lean             `lake exe merkleDemo`
Axioms.lean           `lake env lean Axioms.lean` - the axiom audit
```

## Demo output

```
demoTree leaves : [0, 1, 2, 3, 4, 5, 6, 7]
leaf count : 8 (2 ^ 3 = 8)
demoPath : RLR
  addresses leaf index : 5
  holds the value : 5
root digest : (((0,1),(2,3)),((4,5),(6,7)))
honest proof verifies : true
forged value 42 verifies : false
incremental == full hash : true
```

## License

MIT. See [LICENSE](LICENSE).
