# Formally verified algorithms in Lean 4

A collection of independent, machine-checked algorithm developments.  Each project is a
self-contained Lake package with its own toolchain pin, its own build, and its own axiom
audit — nothing here contains `sorry`, `admit`, `unsafe` or user-declared axioms.

| Project | What is verified | Depends on | Documentation |
|---|---|---|---|
| **Merkle trees** | Indexed binary Merkle trees: collision resistance of the root digest, authentication-path completeness and soundness, no-forgery, incremental-update correctness, complexity bounds, and a signature layer instantiated at SHA3-512. | Lean core + [lean4-hash](https://github.com/pure-algebra/lean4-hash) (no Mathlib) | [`Merkle/README.md`](Merkle/README.md) |
| **Quantum circuit optimizer** | Deeply embedded quantum circuits with an independent matrix semantics over `Matrix (Fin n → Bool) (Fin n → Bool) ℂ`; equivalence modulo global phase; 35 machine-checked rewrite rules; an OptiSat equality-saturation engine; an **independent executable certificate checker** with a proved soundness theorem; end-to-end `optimize_sound`; a bug-regression suite built from documented quantum-compiler defects. | Lean core + Mathlib `v4.26.0` + vendored OptiSat | [`quantum/README.md`](quantum/README.md) |
| **Dijkstra shortest paths** | Dijkstra's algorithm on finite directed `ℕ`-weighted graphs: termination, relaxation correctness, finalization (cut) correctness, global optimality against an independent `WithTop ℕ` specification, path reconstruction, and determinism of the answer. | Lean core + Mathlib `v4.34.1` | [`dijkstra/README.md`](dijkstra/README.md) |
| **LL(1) parser generator** | Context-free grammars, parse trees and derivations with a proved correspondence (`tree_iff_derives`); a fuelled table-driven parser with proved soundness, completeness (under an explicit progress condition), rejection of non-members and a counterexample showing the progress condition is necessary. All four grammar analyses (`NULLABLE`, `REACH`, `FIRST`, `FOLLOW`) with proved soundness, completeness and termination, plus a memoized Boolean-list backend proved to compute the same approximants (and measured: 2x on the circuit grammars, up to 4.9x on a scaled family). A SELECT-based LL(1) table generator that refuses conflicted grammars, proved correct, and proved to *reconstruct the supplied parse tree exactly* — giving parser-output uniqueness, grammar unambiguity, and the end-to-end "accepts exactly the language" theorem from LL(1) alone; LL(1) plus reduced is then proved to imply no left recursion (counted head-expansion traces, with formal counterexamples for both structural hypotheses). The derivation-level classical characterization is now proved equivalent to the check for reduced grammars (`ll1Check_iff_classicalLL1`); LL(1) is proved to exclude every *reachable* selected left-corner cycle (the lookahead-indexed relation Vermillion uses), with the unreachable `U -> U b | eps` divergence kernel-checked as a counterexample to any unrestricted version; and generation is wrapped in a checked API that returns either a table or a named conflicting pair of productions. A quantum circuit DSL (qubit payloads, AST, pretty-printer) with canonical-tree inversion, a total extractor, and a proved parser-printer-extractor round trip. | Lean core only (no Mathlib) | [`ll1/README.md`](ll1/README.md) |
| **ProtSat: SAT-based protocol analyser** | A symbolic Dolev-Yao analyser whose central theorem is a *proved correspondence* between bounded protocol attacks and satisfying assignments of a generated CNF: message algebra with constructors and destructors, an 11-rule inductive adversary plus an executable saturation over a finite universe (soundness, completeness on the universe, monotonicity, constructor/destructor laws), a protocol DSL with an independent small-step operational semantics (Rel/Runs, secrecy leaks and non-injective agreement), a compositional Tseitin encoding in eleven clause groups with linear-size one-hot constraints, a verified DPLL solver with proved soundness and completeness, an attack-certificate checker that imports neither the CNF nor the solver, and the end-to-end theorem that an attack verdict yields a checked certificate. Six protocol examples, including a kernel-verified Lowe attack on Needham-Schroeder and its rejection on Needham-Schroeder-Lowe. | Lean core + Mathlib `v4.34.1` | [`protosat/README.md`](protosat/README.md) |

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
├── protosat/          # SAT-based protocol analyser package (its own Lake project)
│   ├── ProtSat/       #   Syntax, Protocol, Attacker, Deduce, Operational, Bounded,
│   │                  #   CNF, OneHot, Encode, Clauses, Encoding, Complete, DPLL,
│   │                  #   Certificate, Analyzer, Examples
│   ├── Main.lean      #   the command-line analyser (lake exe protosatDemo)
│   └── README.md      # ← ProtSat documentation, theorem inventory, guarantees
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

### LL(1) parser generator (Phases 1–6)

```sh
cd ll1
lake build                 # library + demo + axiom audit, a few seconds, no dependencies
lake exe verifiedLL1Demo   # worked demonstration
lake env lean Axioms.lean  # axiom audit
```

### ProtSat: the SAT-based protocol analyser

```sh
cd protosat
lake build                 # library + demo, ~10 s once Mathlib is cached
lake exe protosatDemo      # the six protocol examples with their verdicts
lake env lean Axioms.lean  # axiom audit
```

Mathlib `v4.34.1` is required; prebuilt objects are in `protosat/.mathlibcache`.  See
[`protosat/README.md`](protosat/README.md) for the model, the correspondence theorems and
what the bounds do and do not prove.

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
