# LL(1) review and proposed theorem, 18 October 2026

Reviewed the current working tree, including its uncommitted changes, and both pasted attachments. Existing project sources were not edited. This folder contains review notes and independent proof checks.

## Assessment

The project contains a genuine verified table generator and fuelled predictive parser. Its grammar semantics is independent of the parser: a derivation step requires membership in the grammar's production list ([Derivation.lean:58](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Derivation.lean:58)). The results establish semantic soundness, completeness for some fuel, exact reconstruction of valid start-rooted trees, and unambiguity.

The strongest current end-to-end result is [generated_language_iff_ll1](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Generator.lean:613):

```lean
G.ll1Check = true →
  (G.language ws ↔ ∃ fuel t,
    Parser.parse G G.genTable fuel (ltoks ws ++ [LTok.eof]) =
      PRes.ok t [LTok.eof])
```

This does not supply a certified executable fuel choice or a fuel-free decision procedure. A precise description of the current result is: **a verified LL(1) table generator and fuelled parser, with soundness, existential-fuel completeness, and start-language unambiguity**.

## The independent LL(1) definition

The classical property concerns two successful leftmost derivations from a common configuration:

```
S ⇒*lm u A δ ⇒lm u α δ ⇒*lm u x
S ⇒*lm u A δ ⇒lm u β δ ⇒*lm u y
```

Here `u`, `x`, and `y` are terminal words, and `A → α`, `A → β` belong to the grammar. Equal next lookahead for `x` and `y`, including EOF for an empty word, must imply `α = β`. See the [Saarland compiler lectures, slide 24](https://compilers.cs.uni-saarland.de/teaching/cc/2015/slides/ll.pdf#page=24).

[LL1Specification.lean](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/LL1Specification.lean) defines this as `Grammar.ClassicalLL1`, without mentioning FIRST, FOLLOW, SELECT, tables, or the parser. It proves both:

```lean
G.Ll1 → G.ClassicalLL1
G.ll1Check = true → G.ClassicalLL1
```

These implications have been kernel checked. The recommended characterization theorem to prove next is:

```lean
theorem Grammar.ll1Check_iff_classicalLL1
    (G : Grammar T N)
    [DecidableEq T] [DecidableEq N]
    [FiniteEnum T] [FiniteEnum N]
    (hred : G.Reduced) :
    G.ll1Check = true ↔ G.ClassicalLL1
```

**The reverse implication remains unproved in this review.** The definition `ClassicalLL1CharacterizationTarget` records the proposition; defining that target is not a proof of it.

The reduction assumption follows the exact qualification in Wilhelm, Seidl and Hack's *Compiler Design*, Theorem 3.3.3, printed p.66 ([author-hosted chapter](https://compilers.cs.uni-saarland.de/teaching/cc/2011/book/cha3.pdf#page=39)). Existing `G.Reduced` requires production-bearing nonterminals to occur and occurring nonterminals to be productive ([LeftRec.lean:132](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/LeftRec.lean:132)).

The converse fails without suitable hypotheses:

- `S → a; U → a | ab`: successful start derivations are deterministic, but the checker rejects the unreachable FIRST conflict.
- `S → aU | aV; U → U; V → V`: no terminal word is generated, making the successful-derivation property vacuous, while the checker rejects the FIRST conflict at `S`.

Ordinary productions are identified by LHS/RHS, so RHS equality is appropriate. If production identifiers or distinct semantic actions matter, require duplicate-freeness or explicitly distinguish duplicate rules.

## Comparison with Vermillion

The relevant implementation is [Vermillion](https://github.com/slasser/vermillion), described by Lasser, Casinghino, Fisher and Roux in [*A Verified LL(1) Parser Generator*, ITP 2019](https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf).

The paper's §4.3 uses **lookahead-indexed** nullable paths: every edge requires a selected production and a nullable prefix before the child. Its no-left-recursion lemma excludes positive cycles at one fixed lookahead. This is more closely tied to parser execution than global grammar left-corner acyclicity. Its derivation relation also includes a LOOKAHEAD premise, so preserve this project's independent ordinary-CFG semantics when adapting its results.

[Vermillion Main.v](https://raw.githubusercontent.com/slasser/vermillion/master/Main.v) contains a parser without fuel, soundness, completeness, and exclusion of internal recursion errors for correct tables. Its generator returns an error on conflicts and checks duplicate productions. Generator completeness assumes duplicate-freeness. I inspected these sources; I did not rebuild Vermillion.

There is an important difference in FOLLOW. Vermillion uses production equations even for unreachable productions; this repository's `FollowSym` requires an occurrence reachable from the start ([Follow.lean:58](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Follow.lean:58)). Therefore a global operational theorem for arbitrary subparser roots is false here.

The kernel-checked [UnreachableSelectedCycle.lean](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/UnreachableSelectedCycle.lean) proves that for

```
S → a
U → U b | ε
```

the checker returns true, the generated `(U,b)` entry selects `U b`, and parsing `U` on `b` returns `outOfFuel` at every fuel. Parsing from start `S` on `a` succeeds. Vermillion's FOLLOW equations put `b` in FOLLOW(U), exposing a conflict with the epsilon rule.

For this repository, a suitable paper-inspired target is:

```lean
G.Ll1 → ∀ lookahead A,
  G.Occurs A → ¬ G.SelectedLCPath lookahead A A
```

`SelectedLCPath` is a positive path whose edges each use a production selected at that fixed lookahead, with a nullable prefix before the child. Its definitions are in the counterexample file. **This acyclicity target is proposed, not proved.** Reachability is essential for the present FOLLOW convention. Alternatively, adopt the paper's all-production FOLLOW convention and its stricter acceptance criterion before seeking a global theorem.

The final operational deliverable should be a concrete executable parser without user-supplied fuel, or an executable `fuelFor G ws`, with a theorem that:

1. Every input, valid or invalid, finishes without `outOfFuel` or an internal cycle error.
2. Success is equivalent to membership in the ordinary CFG language.
3. Every successful tree has start root, is valid, and yields exactly the whole input.

`FuelBoundTarget` in the specification file states a strong version for a supplied fuel chooser. No such chooser is implemented by this review.

## Strengths and gaps in the current project

- NULLABLE, FIRST and FOLLOW are proved equivalent to derivation-based specifications: [Nullable:166](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Nullable.lean:166), [First:479](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/First.lean:479), [Follow:449](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Follow.lean:449).
- [generated_parse_tree:562](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Generator.lean:562) reconstructs every valid start-rooted tree exactly. [parseTree_unique:597](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Generator.lean:597) establishes actual tree uniqueness.
- Generated-table lookup has exact SELECT semantics under `Ll1`, combining [genTable_entry:339](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Generator.lean:339) and [genTable_get_of_select:444](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Generator.lean:444). The corollary is checked in [AnalysisConventions.lean](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/AnalysisConventions.lean).
- The general `Table.Correct` interface is weaker: soundness, adequacy, completeness of residual languages. It does not characterize LL(1). The existing Loop example correctly demonstrates this.
- Both end-to-end language theorems remain existential in fuel. Even [complete_core:436](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Completeness.lean:436) has no bound on its witness. Statements that the rank version already bounds fuel overstate the exposed theorem.
- `never_accepts_of_not_language` establishes no false acceptance. It does not establish eventual rejection without fuel exhaustion.
- `Table.Progressing` quantifies over finite valid matching forests. It can hold vacuously on dead grammar components. [ProgressLimitation.lean](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/ProgressLimitation.lean) proves that a custom looping table for `S → S` is both Correct and Progressing, yet exhausts every fuel. It is not the generated table.
- `genTable` is unconditional and chooses the first selected RHS ([Generator:216](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/Generator.lean:216)). It does not enforce the checker or return a conflict. [UncheckedGenerator.lean](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/UncheckedGenerator.lean) proves that for `S → a | ab`, unchecked generation chooses `a` and rejects the valid word `ab` with trailing input. Conditional correctness theorems remain valid. Add a checked `generate` interface.
- The existing theorem `Reduced + Ll1 → noLeftRecursion` is useful and correctly qualified ([LeftRec:616](/Users/julian/Downloads/formally_verified/ll1/VerifiedLL1/LeftRec.lean:616)). It should be distinguished from the lookahead-sensitive operational theorem above.

## The attached Lean specification

The attachment compiles under the project's Lean version. It explicitly supplies interfaces and obligations, rather than implementing a generator. Its total indexed parser, exact table specification, certified conflict result, and generator-success equivalence describe a strong target. They are not established theorems merely because they occur as structure fields.

Two conventions differ from this repository:

- It computes FOLLOW through all production equations, including unreachable rules.
- It distinguishes production-array positions by `RuleId`; the repository identifies equal RHS alternatives.

For example, `S → a; U → ε | V; V → ε; B → U b`, with `U,V,B` unreachable, passes the repository checker. In the attachment, `B → U b` adds `b` to FOLLOW(U), producing a conflict. Duplicate copies of `S → a` similarly pass this repository's checker and fail the attachment's rule-ID criterion.

The attachment's global well-founded machine obligation is consequently not a property that can simply be asserted about the current generated tables.

## The attached Rocq draft

It is not a verified implementation. Beyond its admitted algorithms and theorems, its base definitions have critical problems:

1. `derives` never requires `r ∈ rules G` (attachment lines 108–116). An invented rule `S → w` proves recognition of any word, even when the production list is empty.
2. `left_recursive` permits zero rewrite steps (194–197). Choose the empty derivation and empty suffix: every grammar is left recursive.
3. `derives_one_leftmost_derivation` quantifies over every position (184–188). It requires a first position equal to both 0 and 1, making that predicate impossible. Its `LL1` predicate therefore holds for every grammar.
4. Its admitted `LL1_not_left_recursive` (228–236) contradicts those definitions. In a separate check, the original prefix including that admitted lemma yielded `False`, with precisely that lemma as the dependency.

[RocqDefinitionsAudit.v](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/RocqDefinitionsAudit.v) preserves the relevant original definitions and proves all four consequences. The saved audit adds no axioms or admitted declarations: it proves the original no-left-recursion assertion impossible as a conditional theorem. All audit proofs are closed under the global context.

The Boolean parser also ignores terminal equality (385), both parsers reject nullable completion on empty input (382/462), and the accumulated used-nonterminal list falsely rejects repeated nullable siblings such as `S → A A a; A → ε` on input `a`. The predictor has no EOF and does not specify FOLLOW-based nullable selection. Repair these definitions before attempting additional Rocq proofs.

## Validation

- `lake build`: success, 55 jobs (including replayed build output).
- Fresh elaboration of Generator.lean, Completeness.lean, and LeftRec.lean: success.
- `lake env lean Axioms.lean`: success. The 190 printed dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appeared. Output is saved in [axioms.log](/Users/julian/Downloads/formally_verified/ll1/review-2026-10-18/axioms.log).
- Attached Lean specification: elaborated successfully.
- Review Lean files: checked with `lake env lean review-2026-10-18/FILE.lean`.
- Rocq definition audit: checked with the installed Rocq/Coq compiler. The full old Rocq draft was not rebuilt or certified.

The immediate proof priorities are the independent classical characterization, a checked generation API, and an executable parser with the all-input operational guarantee.
