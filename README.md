# Formally verified algorithms in Lean 4

A collection of independent, machine-checked algorithm developments.  Each project is a
self-contained Lake package with its own toolchain pin, its own build, and its own axiom
audit — nothing here contains `sorry`, `admit`, `unsafe` or user-declared axioms.

| Project | What is verified | Depends on | Documentation |
|---|---|---|---|
| **Merkle trees** | Indexed binary Merkle trees: collision resistance of the root digest, authentication-path completeness and soundness, no-forgery, incremental-update correctness, complexity bounds, and a signature layer instantiated at SHA3-512. | Lean core + [lean4-hash](https://github.com/pure-algebra/lean4-hash) (no Mathlib) | [`Merkle/README.md`](Merkle/README.md) |
| **Dijkstra shortest paths** | Dijkstra's algorithm on finite directed `ℕ`-weighted graphs: termination, relaxation correctness, finalization (cut) correctness, global optimality against an independent `WithTop ℕ` specification, path reconstruction, and determinism of the answer. | Lean core + Mathlib `v4.34.1` | [`dijkstra/README.md`](dijkstra/README.md) |

## Layout

```text
.
├── lakefile.lean, Main.lean, Axioms.lean, lean-toolchain   # Merkle package (repo root)
├── Merkle/            # Merkle library: Basic, Proof, Complexity, Security,
│   │                  #   Signature, Sha3, Usage, Free
│   └── README.md      # ← Merkle documentation, theorem table, demo output
└── dijkstra/          # Dijkstra package (its own Lake project)
    ├── lakefile.toml, Main.lean, Axioms.lean, lean-toolchain
    ├── Dijkstra/      # Graph, Paths, Algorithm, Correctness, Examples
    └── README.md      # ← Dijkstra documentation, theorem table, build steps
```

The two projects deliberately do **not** share a build: Merkle is a pure-core development
(Mathlib would slow it down for no benefit), while Dijkstra uses Mathlib's order, `Finset`
and `WithTop` theory.  Each directory therefore has its own `lean-toolchain` and lakefile.

## Quick start

### Merkle trees (from the repository root)

```sh
lake build                 # compiles the whole library in seconds
lake exe merkleDemo        # worked demonstration
lake env lean Axioms.lean  # axiom audit
```

Requires [elan](https://github.com/leanprover/elan); the pinned toolchain is in
`lean-toolchain`.

### Dijkstra's algorithm

```sh
cd dijkstra
lake update                # resolves Mathlib (pinned to release v4.34.1)

# Optional but strongly recommended: fetch Mathlib's prebuilt .olean files
# (a few minutes) instead of compiling Mathlib from source (hours).
mkdir -p .mathlibcache
MATHLIB_CACHE_DIR="$PWD/.mathlibcache" lake exe cache get

lake build                 # library + demo executable
lake exe dijkstra          # run the demonstration
lake env lean Axioms.lean  # axiom audit
```

Without the cache step `lake build` still succeeds, but it compiles all of Mathlib from
source.  See [`dijkstra/README.md`](dijkstra/README.md) for the exact theorem names behind
each verified guarantee.

## What each project README contains

1. the model and the mathematical specification, defined independently of the code;
2. the implementation and why it terminates;
3. a table mapping every required property to the Lean theorem that proves it;
4. executable examples checked by the kernel (`decide`), with sample output;
5. the axiom-audit command and what it reports.

## License

MIT — see [LICENSE](LICENSE).
