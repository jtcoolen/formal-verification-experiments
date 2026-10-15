# OptiSat (LambdaSat) — verified equality saturation in Lean 4

**Source.** <https://github.com/lambdaclass/optisat_lean>, commit `f34ebd1`
("fix: add integration-tests executable target to lakefile (#8)"), cloned into
`optisat_lean/` and vendored verbatim into `quantum/LambdaSat/` (`diff -rq` reports no
differences). Lean toolchain of the vendored copy: `leanprover/lean4:v4.26.0`.

**What it is.** A domain-agnostic e-graph / equality-saturation engine in Lean 4,
parameterised by type classes:

| Class | Role |
|---|---|
| `NodeOps Op` | children / mapChildren / replaceChildren of an e-node skeleton |
| `NodeSemantics Op Val` | `evalOp : Op -> (Nat -> Val) -> (EClassId -> Val) -> Val` plus extensionality laws |
| `Extractable Op Expr` | reconstruct a concrete expression from an e-node and its children's expressions |
| `EvalExpr Expr Val` | semantics of concrete expressions |
| `PatternSoundRule Op Val` | a rewrite rule proved to preserve the semantics in the value domain |

**Verified core used by this project.** The *total*, fuel-based pipeline (not the `partial`
convenience pipeline):

* `LambdaSat.UnionFind` — union-find with `merge`, `root`, path compression; 44 theorems,
  no `sorry`.
* `LambdaSat.Core` — `EGraph`, `add`, `merge`, hash-consing (`HashconsChildrenBounded`).
* `LambdaSat.SemanticSpec` — the invariant quadruple used as the e-graph's `WellFormed`
  predicate: `ConsistentValuation` (every e-class has a value equal to the semantics of its
  nodes), `PostMergeInvariant`, `SemanticHashconsInv`, `HashconsChildrenBounded`; plus
  `computeCostsF`.
* `LambdaSat.SaturationSpec` — `ematchF`, `instantiateF`, `applyRulesF`, `saturateF` and the
  `PreservesCV` soundness chain.
* `LambdaSat.Extractable` / `ExtractSpec` — `extractF`, `extractAuto`, `extractF_correct`,
  `extractAuto_correct`.
* `LambdaSat.CompletenessSpec` — `extractAuto_complete`, `computeCostsF_acyclic`,
  `extractF_of_rank` (bounded optimality/completeness of extraction).
* `LambdaSat.PipelineSoundness` — the end-to-end statement for the total pipeline.

**Audit.** `grep -rn sorry LambdaSat/` matches only prose comments (headers describing the
upstream "0 sorry" status and two notes about a *closed* gap); there is no `sorry`, no
`admit` and no `axiom` in the vendored sources. `partial def` occurs in
`Core.rebuild`, `Core.computeCosts`, `Saturate.saturate`, `EMatch.ematch`,
`Optimize.optimizeExpr`, `ILPSolver`, `ParallelSaturate` — i.e. in the *unverified*
convenience layer, which `quantum/` never calls.

**How this project uses it.** `quantum/Quantum/QuantumEGraph.lean` instantiates the classes
for the quantum domain (`QOp n` e-nodes, `PhaseOp n = Operator n / global phase` as the
value domain, `Circuit n` as the extracted expression type) and proves
`extractableSound_qop`, the domain instance of `ExtractableSound`.
`quantum/Quantum/Optimizer.lean` then runs `saturateF` → `computeCostsF` → `extractAuto`.

**Design consequence for trust.** The certificate checker
(`quantum/Quantum/Certificates.lean`) does **not** import LambdaSat at all: it depends only
on syntax, semantics, the rewrite library and contexts. OptiSat therefore sits entirely
*outside* the trust boundary for equivalence: if OptiSat were buggy it could produce a bad
candidate circuit, but the independent checker would reject its certificate and
`optimize` would fall back to the input circuit with the empty (reflexive) certificate.
