# Formally verified algorithms in Lean 4

A collection of independent, machine-checked algorithm developments.  Each project is a
self-contained Lake package with its own toolchain pin, its own build, and its own axiom
audit — nothing here contains `sorry`, `admit`, `unsafe` or user-declared axioms.

| Project | What is verified | Depends on | Documentation |
|---|---|---|---|
| **Merkle trees** | Indexed binary Merkle trees: collision resistance of the root digest, authentication-path completeness and soundness, no-forgery, incremental-update correctness, complexity bounds, and a signature layer instantiated at SHA3-512. | Lean core + [lean4-hash](https://github.com/pure-algebra/lean4-hash) (no Mathlib) | [`Merkle/README.md`](Merkle/README.md) |
| **Quantum circuit optimizer** | Deeply embedded quantum circuits with an independent matrix semantics over `Matrix (Fin n → Bool) (Fin n → Bool) ℂ`; equivalence modulo global phase; 35 machine-checked rewrite rules; an OptiSat equality-saturation engine; an **independent executable certificate checker** with a proved soundness theorem; end-to-end `optimize_sound`; a bug-regression suite built from documented quantum-compiler defects. | Lean core + Mathlib `v4.26.0` + vendored OptiSat | [`quantum/README.md`](quantum/README.md) |
| **Dijkstra shortest paths** | Dijkstra's algorithm on finite directed `ℕ`-weighted graphs: termination, relaxation correctness, finalization (cut) correctness, global optimality against an independent `WithTop ℕ` specification, path reconstruction, and determinism of the answer. | Lean core + Mathlib `v4.34.1` | [`dijkstra/README.md`](dijkstra/README.md) |
| **LL(1) parser generator** | Context-free grammars, parse trees and derivations with a proved correspondence (`tree_iff_derives`); a fuelled table-driven parser with proved soundness, completeness (under an explicit progress condition), rejection of non-members and a counterexample showing the progress condition is necessary. Generator and `FIRST`/`FOLLOW` analyses in progress. | Lean core only (no Mathlib) | [`ll1/README.md`](ll1/README.md) |

## Layout

```text
.
├── lakefile.lean, Main.lean, Axioms.lean, lean-toolchain   # Merkle package (repo root)
├── Merkle/            # Merkle library: Basic, Proof, Complexity, Security,
│   │                  #   Signature, Sha3, Usage, Free
│   └── README.md      # ← Merkle documentation, theorem table, demo output
├── quantum/           # Quantum circuit optimizer package (its own Lake project)
│   ├── Quantum/       #   Syntax, Angle, Gates, Embed, Rotations, Semantics, Equivalence,
│   │                  #   Contexts, Rewrites, Certificates, Cost, QuantumEGraph, Optimizer,
│   │                  #   Correctness, ControlPhase, Examples, BugRegression
│   ├── LambdaSat/     #   vendored OptiSat (unmodified)
│   ├── Main.lean      #   command-line demonstration
│   └── README.md      # ← quantum documentation, theorem inventory, trust boundary
├── dijkstra/          # Dijkstra package (its own Lake project)
│   ├── lakefile.toml, Main.lean, Axioms.lean, lean-toolchain
│   ├── Dijkstra/      # Graph, Paths, Algorithm, Correctness, Examples
│   └── README.md      # ← Dijkstra documentation, theorem table, build steps
└── ll1/               # LL(1) parser generator package (its own Lake project)
    ├── lakefile.toml, Main.lean, Axioms.lean, lean-toolchain
    ├── VerifiedLL1/   # Grammar, ParseTree, Derivation, Examples/{Toy,Circuits}
    └── README.md      # ← LL(1) documentation, phase status, theorem inventory
```

The three projects deliberately do **not** share a build: Merkle is a pure-core development
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

### LL(1) parser generator (Phases 1–3)

```sh
cd ll1
lake build                 # library + demo + axiom audit, a few seconds, no dependencies
lake exe verifiedLL1Demo   # worked demonstration
lake env lean Axioms.lean  # axiom audit
```

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

## Knowledge base

See [`KB/README.md`](KB/README.md): pinned notes on OptiSat, equality saturation for quantum
circuits, the documented quantum-compiler bugs that drive the regression suite, formal
verification of Shor/RSA/ECDLP, and the phase-by-phase development log in
[`KB/PROGRESS.md`](KB/PROGRESS.md).
