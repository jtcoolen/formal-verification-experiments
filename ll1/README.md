# A formally verified LL(1) parser generator in Lean 4

An executable LL(1) parser generator whose soundness, completeness, termination and
parsing-table correctness are machine-checked in Lean 4.  The development is
self-contained: **no Mathlib, no `sorry`, no `admit`, no `partial`, no custom
axioms**.

```
lean-toolchain : leanprover/lean4:v4.34.1
lake build                # builds the library, the demo and the axiom audit
lake exe verifiedLL1Demo  # runs the Phase 1 demonstration
lake env lean Axioms.lean # prints the axiom dependencies of every main theorem
```

## Phase status

| Phase | Content | State |
|---|---|---|
| 1 | Context-free grammars, parse trees, yield, derivation relation, correspondence theorem | **done** |
| 2 | Predictive table type, table-driven parser, independent table-correctness predicate, soundness | not started |
| 3 | Completeness, termination, rejection of non-members | not started |
| 4 | `NULLABLE` / `FIRST` / `FOLLOW` specifications + fixed-point computations, soundness/completeness/termination | not started |
| 5 | `SELECT` sets, LL(1) conflict check, table generation, end-to-end theorem | not started |
| 6 | Quantum circuit DSL as a worked instance | grammar + trees + derivations done (Phase 1 slice) |

## Layout

```text
ll1/
├── lakefile.toml, lean-toolchain
├── VerifiedLL1.lean            # library root (imports everything)
├── VerifiedLL1/
│   ├── Grammar.lean            # Sym, Grammar, wellFormed, FiniteEnum
│   ├── ParseTree.lean          # Tree, yield, MatchList, Valid
│   ├── Derivation.lean         # Derives1, Derives, correspondence theorems
│   └── Examples/
│       ├── Toy.lean            # ε-productions, acceptance *and* rejection proofs
│       └── Circuits.lean       # quantum circuit DSL grammar (Phase 6 language)
├── Main.lean                   # lake exe verifiedLL1Demo
├── Axioms.lean                 # axiom audit
└── README.md
```

## Phase 1 — what was formalised

### The mathematical definitions

* `Sym T N` — terminals (`tok`) and nonterminals (`var`).
* `Grammar T N` — a finite list `productions : List (N × List (Sym T N))` plus a
  start symbol.  An **epsilon production** is a production with `rhs = []`; there is
  no separate `ε` symbol, so no side condition is needed to stop `ε` from appearing
  beside other symbols.
* `Grammar.wellFormed G` — the start symbol has a production, and every nonterminal
  mentioned on a right-hand side has one.  Standing assumption of the later phases.
* `FiniteEnum α` — an *explicit* list of all elements of `α` plus a proof of
  exhaustiveness.  Finiteness is carried as data because the Phase 4 fixed points
  must be computable, and because an enumeration obtained by typeclass search would
  be an opaque exponential object in the executable code.
* `Tree T N` — parse trees: `leaf t` and `node A ts`.
* `Tree.yield` / `Tree.yieldForest` — the terminals of a tree, left to right.
* `MatchList G rhs ts` — the forest `ts` validly expands the symbol list `rhs`.
* `Valid G t` — `t` is a valid parse tree of `G`: a leaf is never valid on its own,
  and a node `node A ts` is valid when its children match the right-hand side of
  one of the productions of `A`.
* `Derives1 G xs ys` — one derivation step (rewrite one nonterminal occurrence in a
  context); `Derives G` its reflexive-transitive closure.
* `Grammar.language G ws` — `Derives G [var G.start] (toks ws)`.

### Principal invariants

1. `MatchList G rhs ts` forces `rhs.length = ts.length` (`MatchList.length_eq`), and
   a forest matching a concatenation splits along it (`MatchList.split`) — the two
   facts that make the transport lemmas go through.
2. Every node occurring in a matched forest is valid (`MatchList.valid_of_mem`), so
   validity is inherited by strict subtrees (`Valid.subtree_valid`).
3. **Downwards transport** `matchList_derives`: `MatchList G rhs ts → Derives G rhs
   (toks (yieldForest ts))`.
4. **Upwards transport** `substitute`: `Derives G xs ys → MatchList G ys ts → ∃ ts',
   MatchList G xs ts' ∧ yieldForest ts' = yieldForest ts`.  This is the invariant
   that a parse tree abstracts from the *order* in which nonterminals are expanded.
5. **No junk** `derives_toks_inj`: `Derives G (toks ws) (toks vs) → ws = vs`.  A
   derivation can never change a terminal word, so the derivation relation does not
   invent input.

### The main theorem

```lean
theorem tree_iff_derives {A : N} {ws : List T} :
    (∃ ts, Valid G (Tree.node A ts) ∧ Tree.yield (Tree.node A ts) = ws) ↔
      Derives G [Sym.var A] (toks ws)
```

The left-hand side mentions only parse trees; the right-hand side mentions only the
grammar.  Neither mentions any algorithm, so this is a semantic characterisation
rather than a statement about an implementation.  `Grammar.language_iff_tree` is the
same fact at the start symbol.

### Design tradeoffs

* **Derivations are untyped lists of symbols with a context-based one-step rule**
  (`pre ++ var A :: post`).  The alternative — a leftmost-only relation — is closer
  to what a predictive parser does, and it will be *added* in Phase 2/3 to connect
  parser traces to derivations; it is not the right primitive for Phase 1 because
  the classical equivalence "parse tree ↔ derivation" is order-independent, and
  proving it for the general relation first makes the leftmost version a corollary
  rather than an axiom.
* **Parse trees are not indexed by their root nonterminal, and do not record which
  production they use.**  Indexing would move work into every parser construction
  for no proof benefit; recording productions would make the soundness statement
  depend on table details that do not exist yet.
* **`MatchList` is a single non-mutual inductive** (the node rule is inlined at a
  nonterminal position) so that `induction` on it is a one-place induction; the
  naive mutual `Valid`/`MatchList` presentation forces a mutual proof script for
  no mathematical gain.
* **`Tree` is a nested inductive**, so the defining equations of `yield` are not
  definitional; they are proved and registered as simp lemmas
  (`Tree.yield_leaf`, `Tree.yield_node`).  This is why `decide` on a yield needs
  those lemmas in scope.

### Examples and counterexamples

`Examples/Toy.lean` uses

```text
s → p q        p → a | ε        q → b q | ε
```

and proves `Valid` and `Derives` for the trees of `a b`, `a`, `b b` and `ε`, proves
`G.wellFormed`, proves `¬ Valid G (node p [leaf b])`, and proves the *rejection*
`¬ H.language [a]` for the one-production grammar `u → c` — through the
correspondence theorem, so it rules out every tree, not just the ones we drew.

`Examples/Circuits.lean` gives the Phase 6 quantum circuit language as a grammar
(`h q0;`, `cx q0 q1;`, `s q1;`, `measure q0;`, sequences, and the empty program),
builds parse trees for `h q0;`, `h q0; cx q0 q1;` and the empty program, derives
their token words, and rejects `h q1;` (wrong qubit) and `h q0` (missing
terminator).

### Axiom audit

`lake env lean Axioms.lean` prints, for every main theorem, its axiom dependencies.
The correspondence theorem and its ingredients depend only on `propext` and
`Quot.sound` (plus `Classical.choice` nowhere).

## Limitations of the current state

* Phases 2–5 are not implemented yet: there is no parser, no table, no
  `FIRST`/`FOLLOW` computation and no LL(1) condition.
* `Grammar.wellFormed` is stated but not yet *used* by any theorem; when Phase 5
  states the generator's correctness it will appear as an explicit hypothesis.
* `Derives` is the general (any-order) derivation relation.  The leftmost variant
  and the theorem "the parser's output is a *leftmost* derivation" are still to
  come; that is what makes the Phase 3 completeness proof match what an LL(1)
  parser actually does.
* `Tree` has no `DecidableEq` (Lean core does not derive it for nested inductives);
  `BEq` is derived.  If a later phase needs decidability of tree equality it will be
  written by hand rather than assumed.

## Next step (Phase 2)

Represent a predictive table as a function from a nonterminal and one lookahead
token (with an explicit end-of-input marker), define a *table-correctness*
predicate purely in terms of the Phase 1 semantics, implement a fuelled
table-driven parser that builds a `Tree`, and prove: whenever the parser returns
`ok t`, `t` is valid and its yield is the whole input.
