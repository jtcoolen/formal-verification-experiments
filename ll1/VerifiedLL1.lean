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
import VerifiedLL1.Examples.Toy
import VerifiedLL1.Examples.Circuits
import VerifiedLL1.Examples.Loop

/-!
# A formally verified LL(1) parser generator in Lean 4

## Phase 1 - context-free grammars, parse trees and derivations

* `VerifiedLL1.Grammar`    - symbols, grammars, well-formedness, finite enumerations
* `VerifiedLL1.ParseTree`  - parse trees, yield, `MatchList`, `Valid`
* `VerifiedLL1.Derivation` - the derivation relation and the correspondence theorem
* `VerifiedLL1.Leftmost`  - leftmost derivations, the leftmost-derivation lemma
* `VerifiedLL1.Table`     - lookaheads, predictive tables, table correctness
* `VerifiedLL1.Parser`    - the fuelled table-driven parser and its soundness
* `VerifiedLL1.Examples.Loop` - a correct table that loops: why progress is needed
* `VerifiedLL1.Examples.Toy` - a worked example grammar with acceptance *and*
  rejection proofs

Later phases (table-driven parsing, completeness and termination, the
`NULLABLE`/`FIRST`/`FOLLOW` fixed points, the generator itself, and the quantum
circuit language) are added on top of these modules; see `README.md`.
-/
