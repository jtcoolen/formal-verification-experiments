/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Grammar
import VerifiedLL1.ParseTree
import VerifiedLL1.Derivation
import VerifiedLL1.Leftmost
import VerifiedLL1.Table
import VerifiedLL1.Parser
import VerifiedLL1.Completeness
import VerifiedLL1.Fixpoint
import VerifiedLL1.Nullable
import VerifiedLL1.First
import VerifiedLL1.Reach
import VerifiedLL1.Follow
import VerifiedLL1.Generator
import VerifiedLL1.LeftRec
import VerifiedLL1.SelectedLC
import VerifiedLL1.Classical
import VerifiedLL1.Exec
import VerifiedLL1.Generate
import VerifiedLL1.Fuel
import VerifiedLL1.Memo
import VerifiedLL1.MemoAnalyses
import VerifiedLL1.MemoTest
import VerifiedLL1.Examples.Toy
import VerifiedLL1.Examples.Circuits
import VerifiedLL1.Examples.Loop
import VerifiedLL1.Examples.Continuation
import VerifiedLL1.Examples.QCircuits
import VerifiedLL1.Examples.LeftRecChecks
import VerifiedLL1.Examples.LeftRecCases
import VerifiedLL1.Examples.UnreachableSelectedCycle
import VerifiedLL1.Examples.FuelChecks

/-!
# A formally verified LL(1) parser generator in Lean 4

## Phase 1 - context-free grammars, parse trees and derivations

* `VerifiedLL1.Grammar`    - symbols, grammars, well-formedness, finite enumerations
* `VerifiedLL1.ParseTree`  - parse trees, yield, `MatchList`, `Valid`
* `VerifiedLL1.Derivation` - the derivation relation and the correspondence theorem
* `VerifiedLL1.Leftmost`  - leftmost derivations, the leftmost-derivation lemma
* `VerifiedLL1.Table`     - lookaheads, predictive tables, table correctness
* `VerifiedLL1.Parser`    - the fuelled table-driven parser and its soundness
* `VerifiedLL1.Fixpoint`    - generic finite monotone fixed-point iteration
* `VerifiedLL1.Nullable`     - NULLABLE: specification, computation, soundness, completeness
* `VerifiedLL1.First`        - FIRST: specification, computation, soundness, completeness
* `VerifiedLL1.Reach`        - REACH: which nonterminals occur in a sentential form
* `VerifiedLL1.Follow`       - FOLLOW: specification, computation, soundness, completeness
* `VerifiedLL1.Generator`    - SELECT, the LL(1) check, table generation, correctness
* `VerifiedLL1.LeftRec`      - LL(1) + reduced => no left recursion (counted head traces)
* `VerifiedLL1.SelectedLC`   - LL(1) => no reachable selected left-corner cycle (Phase 5.3)
* `VerifiedLL1.Classical`    - the classical LL(1) characterization for reduced grammars
* `VerifiedLL1.Exec`         - parser execution invariants: reachable context, suffix, selected descent
* `VerifiedLL1.Generate`     - checked generation: a table or a named conflict (Phase 5.4)
* `VerifiedLL1.Fuel`         - the executable fuel bound and the total generated parser (Phase 5.7)
* `VerifiedLL1.Memo`         - memoized Boolean-list backend for the fixed-point approximants
* `VerifiedLL1.MemoTest`     - validation of the memoized backend against `Fixpoint.iterP`
* `VerifiedLL1.Examples.Loop` - a correct table that loops: why progress is needed
* `VerifiedLL1.Examples.Continuation` - why table correctness needs reachability
* `VerifiedLL1.Examples.QCircuits` - the circuit DSL with qubit payloads, an AST, a printer
* `VerifiedLL1.Examples.Toy` - a worked example grammar with acceptance *and*
  rejection proofs

Later phases (table-driven parsing, completeness and termination, the
`NULLABLE`/`FIRST`/`FOLLOW` fixed points, the generator itself, and the quantum
circuit language) are added on top of these modules; see `README.md`.
-/