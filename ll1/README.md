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
| 2 | Predictive table type, table-driven parser, independent table-correctness predicate, soundness | **done** |
| 3 | Completeness, termination, rejection of non-members | **done** |
| 4 | `NULLABLE` / `REACH` / `FIRST` / `FOLLOW` specifications + fixed-point computations, soundness/completeness/termination | **done** |
| 5 | `SELECT` sets, LL(1) conflict check, table generation, end-to-end theorem | **done** |
| 5.1 | exact-tree completeness, parser-output uniqueness, grammar unambiguity, the LL(1)-only end-to-end theorem | **done** |
| 5.2 | LL(1) + reduced => no left recursion (counted head-expansion traces), with formal counterexamples | **done** |
| 4.0b | memoized Boolean-list fixed-point backend, proved equal to `iterP`, wired into FOLLOW | **done** |
| 5.3 | LL(1) => no **reachable selected** left-corner cycle (lookahead-indexed, Vermillion-style), with the unreachable counterexample | **done** |
| 5.4 | checked generation: a table *or* a named conflicting pair of productions | **done** |
| 5.5 | the classical LL(1) characterization for reduced grammars (`ll1Check = true <-> ClassicalLL1`) | **done** |
| 6 | Quantum circuit DSL as a worked instance | **done**: token-kind grammar + hand table, payload grammar + generated table, AST, printer, canonical-tree inversion, parser-extractor round trip |

## Layout

```text
ll1/
├── lakefile.toml, lean-toolchain
├── VerifiedLL1.lean            # library root (imports everything)
├── VerifiedLL1/
│   ├── Grammar.lean            # Sym, Grammar, wellFormed, FiniteEnum
│   ├── ParseTree.lean          # Tree, yield, MatchList, Valid
│   ├── Derivation.lean         # Derives1, Derives, correspondence theorems
│   ├── Leftmost.lean           # leftmost derivations, the leftmost-derivation lemma
│   ├── Table.lean              # LTok (with eof), Table, Sound/Adequate/Complete, soundCheck
│   ├── Parser.lean             # fuelled table-driven parser + soundness
│   ├── Completeness.lean       # monotonicity, rank, completeness, rejection
│   ├── Fixpoint.lean           # generic finite monotone fixed-point iteration
│   ├── Nullable.lean           # NULLABLE spec + computation + soundness/completeness
│   ├── First.lean              # FIRST spec + computation + soundness/completeness
│   ├── Reach.lean              # REACH: which nonterminals occur in a sentential form
│   ├── Follow.lean             # FOLLOW spec + computation + soundness/completeness
│   ├── Generator.lean          # SELECT, LL(1) check, table generation, correctness,
│   │                           #   end-to-end, exact-tree completeness, unambiguity
│   ├── SelectedLC.lean       # LL(1) => no reachable selected left-corner cycle (Phase 5.3)
│   ├── Generate.lean         # checked generation: table or named conflict (Phase 5.4)
│   ├── Classical.lean        # the classical LL(1) characterization (Phase 5.5)
│   ├── LeftRec.lean            # LL(1) + reduced => no left recursion (head-step counting)
│   ├── Memo.lean               # memoized Boolean-list backend for the fixed points
│   ├── MemoTest.lean           # validation of the memoized backend against Fixpoint.iterP
│   └── Examples/
│       ├── Toy.lean            # ε-productions, acceptance *and* rejection proofs
│       ├── Circuits.lean       # quantum circuit DSL, token kinds (Phase 6 language)
│       ├── QCircuits.lean      # circuit DSL with qubit payloads: generated table, AST,
│       │                       #   printer, canonical-tree inversion, round trip
│       ├── LeftRecChecks.lean  # why Reduced is necessary; Toy derived from LL(1)
│       ├── Continuation.lean   # why table correctness needs a reachability hypothesis
│       └── Loop.lean           # a Correct table that loops: progress is necessary
├── Bench/                      # benchmark families (not a default build target)
│   ├── Grow.lean               # the growing family A0 -> eps, A(i+1) -> Ai Ai
│   ├── MemoGrow.lean           # memoized pipelines over the same family
│   ├── Circ.lean               # the scaled circuit family (k qubit tokens)
│   └── Ref.lean                # the all-iterP reference pipeline
├── bench*.sh                   # measurement drivers (see the performance section)
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
6. **Leftmost transport** (`Leftmost.lean`): the same two transport lemmas hold with
   `LeftDerives` in place of `Derives`, giving `tree_iff_leftDerives` and hence the
   classical **leftmost-derivation lemma** `derives_iff_leftDerives`.  A predictive
   parser only ever produces leftmost derivations, so this is the form Phase 2 and
   Phase 3 need — and it is proved here, not assumed about a parser.

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

* The generator (Phase 5) is implemented and proved correct, but the *converse* — that
  every correct table comes from the generator — is not claimed: the generator produces
  *a* correct table for an LL(1) grammar.
* `Grammar.wellFormed` is stated as a standing sanity condition on grammars but is not
  needed as a hypothesis by the generator theorems: `genTable_sound` holds for every
  grammar, and adequacy/completeness are quantified over *reachable* stack contents, so a
  nonterminal without productions can never be the top of a reachable stack.
* `Leftmost.lean` proves that parse trees, general derivations and leftmost
  derivations coincide for terminal yields, but the parser of Phase 2 will still have
  to be *connected* to `LeftDerives` (its trace is a leftmost derivation by
  construction, and that connection is a theorem about the parser, not about
  grammars).
* `Tree` has no `DecidableEq` (Lean core does not derive it for nested inductives);
  `BEq` is derived.  If a later phase needs decidability of tree equality it will be
  written by hand rather than assumed.

### Theorem inventory (Phase 1)

| Theorem | Statement (schematic) |
|---|---|
| `MatchList.length_eq` | `MatchList G rhs ts → rhs.length = ts.length` |
| `MatchList.append` / `MatchList.split` | matching commutes with concatenation, both ways |
| `MatchList.valid_of_mem`, `Valid.subtree_valid` | subtrees of a valid tree are valid |
| `derives_ctx`, `derives_append` | derivations are stable under context and concatenation |
| `derives1_decompose` | a one-step derivation rewrites exactly one nonterminal occurrence |
| `derives_toks_inj` | `Derives G (toks ws) (toks vs) → ws = vs` (no junk) |
| `matchList_derives` | downwards transport: `MatchList G rhs ts → Derives G rhs (toks (yieldForest ts))` |
| `valid_derives` | **soundness**: `Valid G (node A ts) → Derives G [var A] (toks (yield …))` |
| `substitute` | upwards transport along a derivation, yield preserved |
| `derives_valid` | **completeness**: `Derives G [var A] (toks ws) → ∃ ts, Valid … ∧ yield … = ws` |
| `tree_iff_derives` | the correspondence (both directions) |
| `Grammar.language_iff_tree` | the same at the start symbol |
| `matchList_leftDerives`, `valid_leftDerives`, `substitute_left`, `leftDerives_valid` | the four transport lemmas for leftmost derivations |
| `tree_iff_leftDerives` | parse trees ↔ leftmost derivations |
| `derives_iff_leftDerives` | **leftmost-derivation lemma**: derivable ↔ leftmost-derivable |
| `leftDerives_imp_derives` | leftmost derivations are derivations |

## Phase 2 — table-driven parsing and soundness

### Definitions

* `LTok T` — tokens plus an **explicit end-of-input marker** `eof`; `lookaheadOf`,
  `tokensOf`, `WellFormedInput` (a stream is a token word followed by exactly one
  `eof`).
* `Table T N` — a finite list of entries `(A, (x, rhs))` with a computable lookup
  `get : Table → N → LTok T → Option (List (Sym T N))`.
* Table correctness, stated **only** with the Phase 1 derivation relation:
  * `Sound` — every entry names a production of `G`;
  * `Adequate` — if the table proposes `rhs` for `A` under lookahead `x`, then for
    every stack continuation `cont` and every split `u ++ v` of the remaining input
    with `lookaheadOf (u ++ v) = x`:
    `Derives G (var A :: cont) (toks (u ++ v)) → Derives G (rhs ++ cont) (toks (u ++ v))`;
  * `Complete` — whenever *some* production of `A` admits the remaining input, the
    table has an entry that admits it;
  * `Correct := Sound ∧ Adequate ∧ Complete`.
* `soundCheck` — a **decidable** sufficient test for `Sound` (`sound_of_check`), used
  to certify the example table by `decide` and to be used by the Phase 5 generator.
* `ParseError` — structured errors: `noEntry A x`, `tokenMismatch t x`, `outOfFuel`,
  `malformed`, `trailing x`.
* `parseSym` / `parseForest` / `parse` — the fuelled table-driven parser (mutual,
  structural in the fuel, no `partial`), returning a `Tree` plus the unconsumed
  input, or a structured error.

### Theorems

| Theorem | Statement (schematic) |
|---|---|
| `sound_aux` | the fuel-indexed conjunction of the two sub-parse invariants |
| `parseForest_sound` | `parseForest M fuel syms input = ok ts rest → MatchList G syms ts ∧ tokensOf input = yieldForest ts ++ tokensOf rest` |
| `parseSym_sound` | the same for one symbol |
| **`parse_sound`** | `parse G M fuel input = ok t [eof] → Valid G t ∧ yield t = tokensOf input` |
| `sound_of_check` | `soundCheck G M = true → M.Sound G` (decidable certification of a table) |

### Spec revision: continuations must be reachable

The first version of `Adequate`/`Complete` quantified over *every* stack continuation
`cont`.  That is unsatisfiable: for the LL(1) grammar `s → A B; A → ε ∣ a; B → b`, the
entry `(A, a)` would have to serve both the continuation `[tok a]` (where `A ⇒ ε` makes
`[a]` derivable, forcing an `ε` entry) and the continuation `[]` (where `A ⇒ a` forces
the entry `[a]`).  `Examples/Continuation.lean` proves this as
`not_complete_strong`: no table that is `Sound` can satisfy the old
`CompleteStrong`.

The definitions therefore carry `G.Reachable (var A :: cont)` — "the continuation is a
suffix of a sentential form of `G`", the classical `S ⇒* α A β` hypothesis, and exactly
the invariant a predictive parser maintains.  Nothing else about the specification
changed, and every theorem stated before the revision is still proved (the Loop
example's `Correct` proof only had to absorb the extra hypothesis).

`parse_sound` is proved from `Table.Sound` only — deliberately: the validity of the
result must not depend on the adequacy properties that are needed for *completeness*.
The fuelled interpreter is total and executable; no unconditional completeness claim
is made for an arbitrary fuel value (out-of-fuel is reported as `outOfFuel`, and
`Circuits.parse_hcx_out_of_fuel` exhibits it).

### Executed examples (`Examples/Circuits.lean`)

A hand-written 18-entry predictive table `M` for the circuit grammar, certified by
`M_sound : M.Sound C` (proved by `decide` through `soundCheck`).  Then

* `parse_h_ok`, `parse_hcx_ok`, `parse_empty_ok` — the parser *computes* exactly the
  Phase 1 parse trees (each is `rfl`);
* `parse_h_sound`, `parse_hcx_sound` — instances of `parse_sound`: the returned tree
  is valid and its yield is the whole input;
* `parse_bad_err` — `h q1;` fails with `tokenMismatch q0 q1`;
* `parse_truncated_err` — a missing terminator fails with `tokenMismatch ; eof`;
* `parse_hcx_out_of_fuel` — fuel 3 reports `outOfFuel` instead of looping.

## Phase 3 — completeness, rejection and termination

### The mathematical set-up

Write `Lang G syms ws` for `∃ ts, MatchList G syms ts ∧ yieldForest ts = ws`; by
Phase 1 this is exactly `Derives G syms (toks ws)`.  Completeness then reads: if the
table admits the remaining input, the parser can consume it.

Two things are needed beyond `Table.Correct`.

1. **Progress.**  A correct table can still loop (see `Examples/Loop.lean`), so the
   theorem is stated with an explicit rank `w : N → Nat`:

   `Table.Progressing G M w` — whenever `M.get A x = some rhs`, `ts = pre ++ t :: post`
   matches `rhs` with `yieldForest ts = ws`, the node `t` is rooted at `B`, *every*
   tree of `pre` yields `ε`, and `lookaheadOf (ws ++ rest) = x`, then `w B < w A`.

   In words: a child that starts at the *same* input position as its parent must have
   strictly smaller rank.  A child that starts later is fine, because the tokens its
   left siblings consumed are gone.  This is exactly the non-consuming-cycle
   condition, and it is stated purely about `G` and `M` — never about the parser — so
   the specification stays non-circular.  Right recursion (`instrs → instr instrs`) is
   *not* excluded: the recursive child is preceded by `instr`, which never yields `ε`.

2. **A single well-founded measure.**  The pair (tokens still to consume, rank) is a
   lexicographic variant.  It is packed into one natural number

   `nodeCode K w t = |yield t| · (K+1) + w(root t) + 1` for a node, `0` for a leaf,

   with `forestCode K w ts = max` of the children's codes.  The `+1` keeps node ranks
   strictly positive, so `forestCode ts < nodeCode (node A …)` holds even for the empty
   forest — the case that arises when a table entry expands `A` to an `ε`-production.

### Theorems

| Theorem | Statement (schematic) |
|---|---|
| `monotone`, `parseSym_mono`, `parseForest_mono` | more fuel never hurts: a parse that succeeds with `fuel` succeeds with any `fuel' ≥ fuel` |
| `nodeCode_child` | every child of a table expansion has strictly smaller `nodeCode` |
| `complete_core` | the mutual symbol/forest statement, by strong induction on the rank bound |
| `complete_of_match` | `Correct M + Progressing M w` ⇒ every matched forest is parsed for *some* fuel |
| `language_imp_accepts` | **completeness**: `G.language ws → ∃ fuel t, parse = ok t [eof] ∧ Valid ∧ yield = ws` |
| `parse_ok_imp_language` | **rejection**: for *any* table, acceptance implies membership (uses only `Sound`) |
| `never_accepts_of_not_language` | a non-member is rejected at *every* fuel value |
| `parse_ok_imp_shape` | acceptance of a well-formed stream consumes exactly its token word |
| **`language_iff_accepts`** | the two-sided characterisation: accepted **exactly** when in the language |

`complete_core` proves the symbol statement and the forest statement together by
`Nat.strongRecOn` on the rank bound; inside a fixed bound the forest part is an
ordinary induction on the symbol list (the tail does not decrease the bound, only its
length).

### Reachability in the completeness proof

`complete_core` carries `G.Reachable (syms ++ toks rest)` through the mutual induction
and discharges it with two one-line facts: `Grammar.reachable_of_derives` (rewriting a
reachable form keeps it reachable) and `Grammar.reachable_tail` (a suffix of a reachable
form is reachable — the dropped symbol joins the prefix).  Moving past the head of a
forest is the second case; expanding a nonterminal through the table is the first, and
this is where `Table.Sound` is needed to know the entry really is a production.

### Epsilon, end-of-input and malformed input

* An `ε`-production is a table entry with `rhs = []`; `parseForest … []\, input = ok []
  input` consumes nothing, and `Progressing` is what forces such an expansion to
  decrease the rank (the `pre`-all-ε hypothesis in `nodeCode_child` is exactly the
  case `ws = []`).
* End-of-input is a real symbol: `lookaheadOf [] = eof`, so the entry consulted for
  the last position is the `eof` entry, and `Complete` is what guarantees one exists
  whenever the tail of the input is derivable.
* Malformed streams (no `eof`, or tokens after `eof`) are never accepted:
  `parse_ok_imp_shape` shows acceptance forces `yield t = tokensOf input`, and
  `parse` itself rejects any leftover input with `trailing`.

### Counterexample: why `Progressing` cannot be dropped (`Examples/Loop.lean`)

Grammar `p → p ∣ a ∣ ε` with start `p` (language `{[], [a]}`) and the table
`M p x = [var p]` for every lookahead `x`.  Then

* `M_correct : M.Correct L` — sound (certified by `decide`), adequate (the entry
  repeats the symbol it expands) and complete (each of the three productions is
  simulated by one forward step `p ⇒ p`, `p ⇒ a`, `p ⇒ ε`);
* `a_in_language : L.language [a]` and `nil_in_language : L.language []`;
* `never_accepts_a`, `never_accepts_nil` — for **every** fuel the parse fails with
  `outOfFuel`;
* `not_progressing : ∀ w, ¬ Table.Progressing L M w` — the child `node p []` of the
  expansion `p ⇒ p` yields `ε` at the same position, so any rank would have to satisfy
  `w p < w p`;
* `not_cycleFree : ¬ cycleFree L` — the grammar has the non-consuming cycle `p ⇒ p`.

So the extra hypothesis of `language_iff_accepts` is not an artefact of the proof
technique.

## Phase 4 — grammar analysis

### `Fixpoint.lean` — one generic termination argument

All three analyses are least fixed points of monotone rules over a *finite* carrier.
Rather than repeat the termination proof, `VerifiedLL1.Fixpoint` provides it once:

* a set is a boolean predicate on a finite enumeration `carrier`; the set as a list is
  `carrier.filter p`;
* `iterP P n` applies the monotone transformer `P` to the empty predicate `n` times
  (`PMono` is the explicit pointwise monotonicity hypothesis);
* `iterP_increasing` / `iterP_le_limit` — the approximants grow;
* `length_filter_le`, `length_filter_le_of_le`, `length_filter_lt_of_new` — a strict
  increase between two steps makes the filtered list strictly longer;
* `exists_le_of_not_forall_le` — a bounded search for a non-growing step;
* **`iterP_stable`** — *termination*: if `carrier` enumerates the whole type then
  `iterP P (carrier.length + 1) = iterP P carrier.length`, i.e. the limit is a fixed
  point; the proof is the pigeonhole argument "at most `|carrier|` strict increases";
* `iterP_closed` — the closure property each analysis consumes:
  `iterP P |carrier| x = true ↔ P (iterP P |carrier|) x = true`.

### `Nullable.lean` — NULLABLE

* **Specification** (algorithm-free): `G.Nullable A := Derives G [var A] []`.
* **Computation**: `nullableTest G S A` adds `A` when some production `A → rhs` has
  every symbol of `rhs` already known nullable (a terminal never is; the empty
  right-hand side passes vacuously, which is exactly how the ε-rule is represented).
  `Grammar.nullable A` is `iterP (nullableP G) |N| A`; `Grammar.nullableSet` is the
  same answer as an explicit finite list.
* **Theorems**: `nullableP_mono` (monotone), `nullable_sound` (soundness, by induction
  on the iteration stage), `nullable_backward` + `nullable_complete` (completeness, by
  induction on the derivation, transporting nullability *backwards* through a
  derivation step and using `iterP_closed` at the rewritten symbol), `nullable_iff`,
  `nullableSet_iff`, and `nullable_eps_tree` — the ε-behaviour in parse-tree terms:
  `A` is computed nullable exactly when some valid tree rooted at `A` has empty yield.
* **Example** (`Examples/Toy.lean`): for `s → p q; p → a | ε; q → b q | ε`,
  `nullableSet_eq : G.nullableSet = [s, p, q]` is discharged by `decide`, and
  `not_nullable_u` shows the computation rejecting the one nonterminal that has no
  production at all.

### `First.lean` — FIRST

* **Specification** (algorithm-free): `G.FirstList xs x` — for a token `tok t` it means
  `∃ ys, Derives G xs (Sym.tok t :: ys)` (the classical `FIRST_1`: the rest of the form
  is an arbitrary *sentential* form, which is what makes the rules sound without
  assuming trailing symbols generate anything); for `eof` it means `Derives G xs []`.
  Encoding "`eof`" as "derives nothing" is what gives the correct ε-behaviour for free.
* **Computation**: `firstListTest` (list rule: skip nullable heads, otherwise the head
  decides — and `eof` is reachable only by skipping everything) and `firstTest` (symbol
  rules: a terminal has itself; a nonterminal inherits the FIRST of any production's
  right-hand side), iterated by `Fixpoint.iterP` over the finite enumeration of
  `Sym T N × LTok T`, with the Phase 4.1 NULLABLE set as a fixed input.
* **Theorems**: `firstP_mono`, `firstListTest_sound` + `first_sound` (soundness, by
  induction on the iteration stage), `firstListTest.prepend` / `of_allNull` /
  `append_imp` / `firstListTest_eof` (the list theory: a lookahead of a concatenation
  comes from the prefix, or the prefix is all nullable and it comes from the tail),
  `first_step_back` (FIRST is preserved backwards through *one* derivation step — the
  tokens of a form come from the same places before and after a step), `first_backwards`
  (hence along a whole derivation), `first_complete`, and the characterisations
  `first_iff` and `first_eof_iff_nullable` (`eof ∈ FIRST(s)` exactly when `s ⇒* ε`).
* **Example** (`Examples/Toy.lean`): `first_s_b` proves `b ∈ FIRST(s)` — the token comes
  from `q` because `p` is nullable — `first_p_eof` proves `eof ∈ FIRST(p)` via `p ⇒ ε`,
  and `first_u_not_eof` shows the computation rejecting `eof` for the one nonterminal
  that cannot vanish.  `#eval firstPairs` prints the whole computed relation.

### `Reach.lean` — REACH (an auxiliary analysis FOLLOW needs)

* **Specification**: `G.Occurs A := ∃ pre post, Derives G [var G.start] (pre ++ [var A] ++
  post)` — `A` occurs *somewhere* in a sentential form.  This is deliberately not
  `G.Reachable [var A]`, which asks for `A` to occur at the *end* of a form.
* **Why it is needed**: the textbook rule "`B → α A β`, `t ∈ FIRST(β)` ⟹ `t ∈ FOLLOW(A)`"
  is unsound for an unreachable `B`, because that production contributes no occurrence of
`A` at all.  `Follow.lean` therefore makes `G.occurs B` a side condition of that rule
instead of quietly assuming every nonterminal is reachable.
* **Computation**: least fixed point over the carrier `N` (`occursTest`), one pass per
nonterminal.
* **Theorems**: `occursP_mono`, `occurs_sound`, `occurs_complete` (induction on the
derivation of the form, with the occurrence located by `occurrence_append`), `occurs_iff`,
`occurs_stable` (termination), plus `not_occurs_of_absent` — a cheap syntactic rejection
criterion: if `B ≠ start` and no right-hand side mentions `B`, then `B` occurs nowhere.
* **Example**: `occurs_s`, `occurs_p`, `occurs_q` are exhibited as derivations;
`not_occurs_u` proves the fifth nonterminal of the toy grammar unreachable, and
`#eval occursList` prints `[s, p, q]`.

### `Follow.lean` — FOLLOW

* **Specification** (algorithm-free): `G.FollowSym A x := ∃ pre post, Derives G
  [var G.start] (pre ++ [var A] ++ post) ∧ G.FirstList post x`.  Since `FirstList` is
  itself stated with `Derives`, this mentions neither the fixed point nor the parser.
  `Grammar.followSym_of_reachable` is the form the generator needs: a reachable stack top
  `var A` with continuation `cont` inherits every lookahead of `cont`.
* **Computation**: least fixed point over the finite carrier `N × LTok T` of the rules
  `R1` (`eof ∈ FOLLOW(start)`), `R2` (`B` occurs, `x` a *token* of `FIRST(β)` for a
  production `B → α A β`), `R3` (`β` erases and `x ∈ FOLLOW(B)`), with the already
  computed NULLABLE, FIRST and REACH as fixed inputs.
* **Two subtleties the formalisation forces us to state** (both are silent assumptions in
  the textbook presentation):
  * `R2` needs the REACH side condition (above).
  * `R2` must be restricted to *token* lookaheads.  `eof ∈ FIRST(β)` only says `β ⇒* ε`;
    the real suffix after `A` is `β ++ post` where `post` is whatever followed `B` in the
    form, and `post` need not erase.  `eof` therefore has to travel along `R3`, seeded by
    `R1` — which is exactly the classical convention "`eof ∈ FOLLOW(S)` only".
* **Theorems**: `followP_mono`, `follow_sound` (induction on the iteration stage; each
  rule is discharged by building the witness sentential form), `follow_complete`
  (induction on the derivation of the form with the marked occurrence carried along;
  `Grammar.FirstList.append_decomp` decides whether a lookahead comes from the suffix
  inside the production or from further out, which is precisely what selects `R2` versus
  `R3`), `follow_iff`, `follow_eof_iff` (the ε/end-of-input characterisation),
`follow_stable` (termination).
* **Examples**: `follow_p_b` (`b ∈ FOLLOW(p)`, from the form `p q`), `follow_p_eof`
  (`eof ∈ FOLLOW(p)`, because the suffix `q` erases), `follow_q_eof`, `follow_s_eof`;
  `not_follow_u` proves `FOLLOW(u) = ∅` *semantically* (via REACH), and
  `not_follow_q_b`/`not_follow_s_b` are rejected by the computation.  `#eval followPairs`
  prints `{s ↦ eof, p ↦ {b, eof}, q ↦ eof}`.

### Theorem inventory (Phase 4)

| Theorem | Statement (schematic) |
|---|---|
| `Fixpoint.iterP_increasing` | approximants of a monotone transformer grow |
| `Fixpoint.iterP_stable` | **termination**: `iterP P (\|carrier\| + 1) = iterP P \|carrier\|` |
| `Fixpoint.iterP_closed` | the limit is closed under the transformer |
| `nullable_iff` | `G.nullable A = true ↔ Derives G [var A] []` |
| `nullable_eps_tree` | computed NULLABLE = roots of valid trees with empty yield |
| `first_iff` | `G.first s x = true ↔ G.FirstSym s x` |
| `first_eof_iff_nullable` | `eof ∈ FIRST(s)` exactly when `s ⇒* ε` |
| `firstList_iff` | the same for whole symbol lists |
| `Grammar.FirstList.append_decomp` | a lookahead of `xs ++ ys` comes from `xs`, or `xs` erases and it comes from `ys` |
| `Grammar.FirstList.backwards_derives` | FIRST is preserved backwards along a derivation |
| `occurs_iff` | `G.occurs A = true ↔ A` occurs in a sentential form |
| `not_occurs_of_absent` | syntactic unreachability criterion |
| `follow_iff` | `G.follow A x = true ↔ G.FollowSym A x` |
| `follow_eof_iff` | `eof ∈ FOLLOW(A)` iff `A` can be followed by an erasable suffix |
| `occurs_stable`, `follow_stable` | the iterations are stable at their bounds |

## Phase 4.0b / 4.0c — the memoized fixed-point backend, measured rather than promised

`Memo.lean` adds a second implementation of the approximants: a `List Bool` aligned with a
carrier list, a strict continuation-based tabulation worker that matches every produced
`Bool` before accumulating it (so the kernel must materialise the list rather than leave a
lazy `List.map` chain), a fuel-bounded forward loop that stops **exactly** when two
consecutive bit lists are equal, and `iterMemo` for predicate-style lookup:

```lean
def lookup [BEq α] (carrier : List α) (bits : List Bool) (x : α) : Bool :=
  bits.getD (carrier.idxOf x) false

theorem iterMemo_eq_iterP [BEq α] [LawfulBEq α] (carrier : List α)
    (P : (α → Bool) → α → Bool) (hall : ∀ x, x ∈ carrier) (n : Nat) (x : α) :
    iterMemo carrier P n x = Fixpoint.iterP P n x
```

The bridge needs **no monotonicity hypothesis**: exhaustiveness of the carrier turns an
equality of bit lists into an equality of the two approximants *everywhere*, which is exactly
what justifies the early stop.  `MemoTest.lean` validates the backend against `iterP` at zero
rounds, at an immediate fixed point, over carriers **with duplicates** (`FiniteEnum` promises
exhaustiveness, not duplicate-freeness — `Fixpoint.lean`'s module comment claimed otherwise,
and repeated keys really do receive identical tabulated values), over a nullable-style chain,
and against a deliberately **nonmonotone** toggling transformer; it also exhibits a
transformer for which `hall` is genuinely needed, so the hypothesis is not decoration.
`MemoAnalyses.lean` states the memoized form of NULLABLE, REACH, FIRST, FOLLOW and the
left-corner closure, each with a one-line bridge to the `iterP` approximant the semantic
proofs are written against — so no analysis proof had to be re-done.

### Where the memoized backend wins, and where it does not

Times are wall-clock seconds for `lake env lean` on a file whose only content is
`example : <statement> := by decide` — i.e. `decide`'s evaluation *plus* the kernel check of
the declaration — with a 60 s limit per measurement.  `./bench5.sh` and `./bench6.sh`
reproduce them; `Bench/Ref.lean` re-states the all-`iterP` pipeline and proves it equal to
the shipped one, so both are measured inside one build.

| grammar | check | all-`iterP` | shipped (memoized FOLLOW + lcReach) | speed-up |
|---|---|---|---|---|
| Toy | `ll1Check` | 0.35 | 0.30 | 1.2× |
| `Examples/Circuits` | `ll1Check` | 1.93 | **1.07** | **1.8×** |
| `Examples/QCircuits` | `ll1Check` | 2.43 | **1.23** | **2.0×** |
| scaled circuit, k=8 | `ll1Check` | 10.13 | **3.02** | **3.4×** |
| scaled circuit, k=12 | `ll1Check` | 22.24 | **5.13** | **4.3×** |
| scaled circuit, k=16 | `ll1Check` | 35.08 | **7.14** | **4.9×** |
| scaled circuit, k=16 | `noLeftRecursion` | 1.60 | **0.52** | **3.1×** |

The scaled circuit family (`Bench/Circ.lean`) is the QCircuits grammar with k qubit tokens
instead of two: the nonterminal alphabet stays at 8 while the lookahead alphabet grows, so the
FOLLOW carrier has 8·(k+2) pairs and the FIRST carrier (2k+13)·2.  The improvement grows with
the size of the grammar, which is the acceptance target: at the largest size where both
implementations finish, the shipped code is about 5× faster.

The specified growing family (`Bench/Grow.lean`: `A0 -> eps`, `A(i+1) -> Ai Ai`, started at the
deepest nonterminal so every nonterminal is reachable) shows **no** improvement, and it is worth
recording why:

| depth | `nullable` | `ll1Check` (all-`iterP`) | `ll1Check` (shipped) |
|---|---|---|---|
| 8 | 0.24 | 0.62 | 0.83 |
| 12 | 0.29 | 1.44 | 1.86 |
| 16 | 0.29 | 3.49 | 4.00 |

Tabulating a whole carrier every round pays only when the approximant is re-queried at nearly
every carrier point.  The kernel's whnf cache already shares the closed terms `iterP P k`, so a
demand-driven chain is cheap when few carrier points are visited — and in the growing family
the FOLLOW transformer is both small and sparsely queried, so the tabulation costs a little
more than it saves.  Memoizing *everything* is worse still: on the growing family at depth 16
the fully memoized pipeline takes 4.11 s against 3.52 s, a single FOLLOW query 3.78 s against
0.29 s, and QCircuits' FIRST over all 120 symbol/lookahead pairs went from 0.41 s to 2.82 s.
The shipped configuration therefore memoizes the two loops that measurably benefit (FOLLOW and
the left-corner closure) and keeps the memoized forms of NULLABLE, REACH and FIRST as
proved-equal API.  The previous README claim that a list-fold iteration would make the `decide`
proofs *near-instant* was wrong; the numbers above replace it.  Reproduce with `./bench5.sh`,
`./bench6.sh`, `./bench7.sh`.

### Theorem inventory (Phase 4.0b / 4.0c)

```text
Memo.lookup_map               exhaustive carrier => lookup of a tabulated function
Memo.tabulate_map             the strict CPS worker equals carrier.map f (accumulator invariant)
Memo.step_map                 one round = carrier.map (P (lookup carrier bits))
Memo.eq_of_map_beq            bit-list equality => pointwise equality (needs hall)
Memo.loop_map                 loop refinement from an arbitrary carrier.map f (no monotonicity)
Memo.iterBits_eq_map_iterP    the bit list is the n-th approximant, bit for bit
Memo.iterMemo_eq_iterP        the predicate lookup is Fixpoint.iterP P n
Memo.iterMemo_closed / _stable / _increasing   closure and termination transferred from iterP
Grammar.follow_eq_iterP       the shipped FOLLOW is the iterP approximant
Grammar.nullable_eq_iterMemo  the four bridges for the analyses kept on iterP
Grammar.occurs_eq_iterMemo
Grammar.first_eq_iterMemo
Grammar.lcReach_eq_iterMemo
```

## Phase 5 — the LL(1) parser generator

### `Generator.lean`

* **`SELECT`, specified semantically.**  `G.Select A rhs x` says
  `(x is a token and x ∈ FIRST(rhs))` or `(rhs erases and x ∈ FOLLOW(A))` — where
  `FIRST`/`FOLLOW` are themselves the derivation-level predicates of Phase 4, so `Select`
  never mentions the table or the parser.  `Grammar.selectTest` computes it from the
  computed analyses and `select_iff` proves the two equivalent.
* **The LL(1) condition.**  `G.Conflict A x` exhibits two *different* productions of `A`
  both selected by `x`; `G.Ll1` says no pair is conflicted.  `G.ll1Check` is the decidable
  version (for every `(A, x)` all selected right-hand sides agree) and `ll1Check_iff`
  proves it equivalent to `Ll1`.  **The generator refuses a conflicted grammar**:
  `Examples/Loop.lean` now also proves `loop_not_ll1 : L.ll1Check = false` and
  `loop_left_recursive : L.noLeftRecursion = false` — the looping grammar of Phase 3 is
  rejected by the check, with the two concrete conflicts `loop_conflict_a` and
  `loop_conflict_eof` exhibited.
* **Table construction.**  `Grammar.genEntry` writes, for each pair `(A, x)`, the unique
  selected production (or nothing); `Grammar.genTable` collects them over the finite
  enumeration of `N × LTok T`.  `genTable_get` computes a lookup by an explicit induction
  over that enumeration (only the entry generated from `(A, x)` can match the lookup), and
  `genTable_sound` gives `Table.Sound`.
* **The bridge lemma** `select_of_derives`: if `var A :: cont` is reachable and
  `rhs ++ cont` derives the remaining input `w`, then `lookaheadOf w ∈ SELECT(A, rhs)`.
  This is `FirstList.append_decomp` (the lookahead comes from `rhs`, or `rhs` erases and it
  comes from `cont`) plus `followSym_of_reachable`.  It is the only place where the
  derivation semantics and the analysis meet.
* **Correctness of the generated table.**  `genTable_adequate` and `genTable_complete`
  (assuming `ll1Check G = true`) give `genTable_correct : … → Table.Correct G`.  Adequacy
  is the interesting one: the derivation of the input is turned into a forest
  (`derives_forest`, Phase 1) and `MatchList.eq_node_cons` reveals *the* production used at
  the top; the bridge lemma says it is selected by the real lookahead, and conflict-freeness
  identifies it with the table's entry.  No leftmost-derivation reordering is needed.
* **Termination.**  `Progressing` (Phase 3) is discharged from a *new* decidable
  hypothesis: the **left-corner** relation `G.LeftCorner A B` (in one step `A` derives a
  form whose leftmost symbol is `B`), its reachability `lcReach` as a second monotone
  fixed point (`lcReach_iff` proves it is the least one containing `A` and closed under left
  corners), and `noLeftRecursion` (no `A` reaches itself).  The ranking is
  `lcRank A = |{B | lcReach A B}|`, and `lcRank_lt` proves it strictly decreases along a
  left corner — the pigeonhole argument `Fixpoint.length_filter_lt_of_new` again.
  `lc_of_match` is the link back to the parser: if a forest matching `rhs` is
  `pre ++ node B … :: post` with every tree of `pre` yielding nothing, then `B` sits at a
  left corner of `rhs` (the symbols before it are exactly the heads of the empty-yielding
  trees, and each of them erases).  `genTable_progressing` puts the two together.
* **End-to-end.**  `generated_language_iff`: if `ll1Check G = true` and
  `noLeftRecursion G = true` then for every word `ws`,

      G.language ws  ↔  ∃ fuel t, parse G (genTable G) fuel (ltoks ws ++ [eof]) = ok t [eof]

  and `generated_accepts_tree` adds that the returned tree is `Valid` with yield exactly
  `ws`.  Rejection of non-members is `never_accepts_of_not_language` (Phase 3) and needs
  only `Sound`, which holds unconditionally.  **Assumptions stated explicitly**: the two
  decidable hypotheses above; `FiniteEnum` instances for both alphabets; and the
  reachability hypothesis inside `Table.Adequate`/`Complete` (see Phase 2).

> **Update (Phase 5.1).**  `Grammar.generated_language_iff_ll1` derives the same
> end-to-end characterisation from `ll1Check` **alone**: exact-tree completeness makes the
> supplied parse tree the parser's output, so the no-left-recursion hypothesis is not
> needed for acceptance at *some* fuel.  Phase 5.2 then proves that for a reduced grammar
> the left-recursion check could not have failed anyway.

### Worked instances

* `Examples/Toy.lean`: `toy_ll1` and `toy_no_left_recursion` are discharged by `decide`;
  `#eval genEntries` prints the textbook table
  `s ↦ p q` on `{a,b,eof}`, `p ↦ a` on `a`, `p ↦ ε` on `{b,eof}`, `q ↦ b q` on `b`,
  `q ↦ ε` on `eof`.  `toy_accepts_ab` exhibits the acceptance of `a b` through the
  generated parser, and `gen_no_c` that no production of `s` is selected by `c`.
* `Examples/Circuits.lean`: `circ_ll1`, `circ_no_left_recursion` (both by `decide`, a few
  seconds of kernel time), `#eval C.genTable.entries` prints the 18-entry table for the
  circuit DSL, and `circ_end_to_end` / `gen_parse_hcx` / `gen_parse_empty` prove that the
  *generated* parser accepts `h q0; cx q0 q1;` and the empty program with valid parse trees
  covering the whole input.

### Theorem inventory (Phase 5)

| Theorem | Statement (schematic) |
|---|---|
| `select_iff` | computed `SELECT` = the derivation-level `Select` |
| `ll1Check_iff` | the decidable check = the LL(1) condition |
| `select_of_derives` | **bridge**: reachable + `rhs ++ cont ⇒* w` ⟹ `lookaheadOf w ∈ SELECT(A,rhs)` |
| `genTable_get` | lookup in the generated table = the head of its `selectRhs` list |
| `genTable_sound` | every generated entry is a production (unconditional) |
| `genTable_adequate` | `ll1Check` ⟹ the table never destroys a derivation |
| `genTable_complete` | `ll1Check` ⟹ the table offers a production whenever one exists |
| `genTable_correct` | `ll1Check` ⟹ `Sound ∧ Adequate ∧ Complete` |
| `leftCorner_iff` | computed left-corner = the derivation-level relation |
| `lcReach_iff` | computed reachability = the least closed set |
| `noLeftRecursion_iff` | the check = no nonterminal is its own left corner |
| `lcRank_lt` | no left recursion ⟹ the rank drops along every left corner |
| `lc_of_match` | an empty-yielding prefix puts the child at a left corner |
| `genTable_progressing` | no left recursion ⟹ `Table.Progressing` |
| `generated_language_iff` | **end-to-end**: LL(1) + no left recursion ⟹ accepts exactly the language |
| `generated_accepts_tree` | the accepted tree is valid and yields the whole input |

## Phase 5.1 — exact-tree completeness, unambiguity, and the LL(1)-only end-to-end theorem

Phase 3's completeness theorem (`complete_of_match`) proves the parser returns *a* forest
with the right yield; it may replace the tree it was given.  Phase 5's end-to-end theorem
therefore needed *two* decidable hypotheses, `ll1Check` and `noLeftRecursion`, the second
one only to make the parser terminate.  `Generator.lean` now proves the stronger statement,
and everything below follows from it.

* `Grammar.genTable_get_of_select` — the lookup fact `genTable_complete` proved
  existentially, made exact: if `x` selects `A -> rhs` then `G.genTable.get A x = some rhs`.
* **`Grammar.generated_parseForest_of_match`** (the central proof) — if `MatchList G syms ts`
  and `syms ++ toks rest` is reachable, then for some fuel the generated parser returns
  **exactly `ts`** and consumes exactly `yieldForest ts`.  The proof is an induction on the
  matching forest itself: the finite tree *is* the termination argument, so no grammar rank,
  no `Progressing` hypothesis and no left-recursion check are needed.  At a nonterminal the
  matching proof names the production that was used, `select_of_derives` says the remaining
  input selects it, `genTable_get_of_select` forces the table to offer it, and the two
  induction hypotheses are combined at the maximum of their fuels.
* `Grammar.generated_parse_tree` — the one-tree form: every valid tree rooted at `G.start`
  is an output of the generated parser on its own yield.
* `parseForest_success_unique` / `parse_success_unique` — two successful parses of the same
  input agree on the forest *and* on the remaining input, whatever their fuel values (lift
  both to `max f₁ f₂` with `parseForest_mono` and use constructor injectivity).
* **`Grammar.parseTree_unique`** — *grammar unambiguity*: two valid parse trees with the
  start symbol at the root and the same yield are identical.  The start-root hypothesis is
  real, not decoration: an unreachable nonterminal can have two different nullable trees
  with the same empty yield without creating any `SELECT` conflict, because `FOLLOW` is
  empty there.
* **`Grammar.generated_language_iff_ll1`** — the end-to-end characterisation from the LL(1)
  condition **alone**: `G.language ws ↔ ∃ fuel t, parse G G.genTable fuel (ltoks ws ++ [eof])
  = ok t [eof]`.  The two-hypothesis theorem `generated_language_iff` is kept (it additionally
  bounds the fuel through the left-corner rank); the new one needs only `ll1Check`.

### Theorem inventory (Phase 5.1)

```text
Grammar.reachable_append          Reachable (xs ++ ys) -> Derives ys ys' -> Reachable (xs ++ ys')
parseForest_success_unique        two successes => same forest, same remainder
parse_success_unique              two top-level successes => same tree
Grammar.genTable_get_of_select    Select A rhs x -> genTable.get A x = some rhs
Grammar.generated_parseForest_of_match   MatchList G syms ts => parser returns ts exactly
Grammar.generated_parse_tree      Valid G t -> root t = start => parser returns t
Grammar.parseTree_unique          unambiguity of an LL(1) grammar at its start symbol
Grammar.generated_language_iff_ll1  language = accepted, from ll1Check alone
```

## Phase 5.2 — LL(1) plus reduced implies no left recursion

`LeftRec.lean` proves the classical theorem that the textbook argument only sketches:

```lean
theorem Grammar.noLeftRecursion_of_ll1 (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hred : G.Reduced) (hall : G.Ll1) : G.noLeftRecursion = true
```

with the structural hypotheses stated exactly:

```lean
def Grammar.Productive (G : Grammar T N) (A : N) : Prop := ∃ ws, Derives G [Sym.var A] (toks ws)
def Grammar.Reduced (G : Grammar T N) : Prop :=
  (∀ A, G.hasProduction A → G.Occurs A) ∧ (∀ A, G.Occurs A → G.Productive A)
```

`Reduced` allows unused alphabet constructors (the Toy grammar's unused variable is legal)
while requiring every *occurring* nonterminal — including one mentioned only on a
right-hand side — to generate some terminal word.

**Why the naive proof fails.**  The textbook ranks a left corner `A =>+ B gamma` by `FIRST`
and claims the rank drops.  It need not: a nullable edge whose tail also erases keeps every
lookahead of `A` available at `B`, so no strict decrease exists in general.  Instead the
proof *counts head expansions*:

* `HeadSteps G xs ys k` — `ys` is obtained from `xs` by expanding the *head* nonterminal
  exactly `k` times; the continuation is never touched.
* `AtLookahead x ys` — the form `ys` really stops at lookahead `x`: its head is the token
  `x`, or `ys = []` and `x = eof`.
* `Grammar.select_of_first` — the bridge lemma `select_of_derives` generalised from a
  terminal word to an arbitrary lookahead, via `FirstList.append_decomp` and
  `derives_nil_append`.
* **`headSteps_stop_length_unique`** — along a *reachable* form, the number of head
  expansions needed to reach a stopping position is unique.  This is the LL(1) property
  transported through `select_of_first`.  Productivity (the second half of `Reduced`) is
  what makes a stopping position a *lookahead* position at all: the tail of the form a
  trace stops in has to erase down to terminals, otherwise `FIRST` says nothing about it.
* `headSteps_of_match`, `headSteps_of_leftCorner`, `headSteps_of_lcReach` — the witnesses:
  a matching forest stops somewhere, a left corner is a positive-count trace, and a
  left-corner cycle composes into `HeadSteps G [var A] (var A :: delta) j` with `0 < j`.
* `Grammar.noLeftRecursion_aux` — the contradiction.  Iterating the cycle gives reachable
  forms `A delta^n post` with unique stopping lengths `c_n = j + c_(n+1)`, and the yield
  chosen for `A` makes the stopping lookahead independent of `n`; hence `c_0 >= n*j` for
  every `n`, instantiated at `n := c_0 + 1`.

**The hypotheses are necessary**, and `Examples/LeftRecChecks.lean` makes that a theorem
rather than a remark:

* `LeftRecUnreachable`: `S -> s`, `U -> U`, `U -> eps`.  `ll1Check = true` (by `decide`) but
  `noLeftRecursion = false`, because `U` never occurs, so `FOLLOW(U)` is empty and neither
  `U` production is selected by anything.  Here `Reduced.1` fails.
* `LeftRecUnproductive`: `S -> S`.  Again `ll1Check = true`, `noLeftRecursion = false`;
  `S` occurs (it is the start symbol) but derives no terminal word.  Here `Reduced.2` fails.
* `ToyReduced`: the Toy grammar is proved `Reduced`, and its `noLeftRecursion = true` is
  then *derived from* `Ll1` by the new theorem (agreeing with the existing `decide` proof).

**Every shape of cycle is detected.**  `Examples/LeftRecCases.lean` checks the classical cases
by `decide`: direct (`S -> S a | a`), indirect (`S -> A`, `A -> S x | z`), and reachable
epsilon-only (`S -> U`, `U -> U | eps`) each give `noLeftRecursion = false` *and* — exactly as
the theorem forces for a reduced grammar — `ll1Check = false`.  The nullable-prefix case
(`S -> E B`, `E -> eps`, `B -> S`) is the instructive one: `noLeftRecursion = false` but
`ll1Check = true`, because no token is ever produced, so nothing is selected and nothing
conflicts; what fails is productivity, precisely the hypothesis `Reduced.2` supplies.

### Theorem inventory (Phase 5.2)

```text
Grammar.Productive / Grammar.Reduced       the structural hypotheses
Grammar.derives_toks_of_reachable          Reduced + Reachable xs => xs derives a terminal word
HeadSteps.derives / .append_right / .trans the trace API
Grammar.select_of_first                    FirstList (rhs ++ cont) x -> Select A rhs x
Grammar.FirstList.of_atLookahead           Reduced + Reachable + AtLookahead -> FirstList
headSteps_stop_length_unique               the determinism core (Ll1 + Reduced)
headSteps_of_match / of_leftCorner / of_lcReach   the three witness lemmas
Grammar.noLeftRecursion_aux                a cycle contradicts uniqueness
Grammar.noLeftRecursion_of_ll1             the theorem
Grammar.noLeftRecursion_of_ll1Check        the decidable-check form
```

## Phase 5.3 - reachable selected cycles are impossible (`SelectedLC.lean`)

The operational core of Lasser, Casinghino, Fisher and Roux, *A Verified LL(1) Parser
Generator* (ITP 2019) is a **lookahead-indexed** left-corner relation: an edge `A -> B` at
lookahead `x` is a production `A -> alpha B beta` that the `x`-column of SELECT claims,
with `alpha` erasable.  A cycle of such edges is exactly what makes recursive descent loop
without consuming input.  This module proves the version of their no-cycle lemma that is
true for this repository's conventions:

```lean
Grammar.noSelectedLCCycle : G.Ll1 -> G.Occurs A -> not (G.SelectedLCPath x A A)
Grammar.reachableSelectedLCAcyclic : G.Ll1 -> forall x A, G.Occurs A -> not (G.SelectedLCPath x A A)
```

The reachability hypothesis is not decoration.  `Examples/UnreachableSelectedCycle.lean`
kernel-checks the grammar `S -> a`, `U -> U b | epsilon`: the checker passes, `U` does not
occur, `U` nevertheless carries a selected cycle at `b`, and `parseSym` on `U` and the input
`b` returns `outOfFuel` at *every* fuel (`never_parses_b`).  Vermillion's FOLLOW equations
cover all productions and would reject that grammar; this repository's `FollowSym` requires
a reachable occurrence, so the global subparser theorem cannot be transferred unchanged.

### Why no productivity hypothesis is needed here

Phase 5.2 needed `Reduced` to turn a stopping position into a `FIRST` statement.  Two
observations remove it:

* `AtLookahead x ys` *already* gives `G.FirstList ys x` - the witness is the form itself
  (`Grammar.FirstList.of_atLookahead_free`), so comparing stopping traces needs only `Ll1`
  (`headSteps_stop_length_unique_free`; the Phase 5.2 form is now a corollary).
* A selected edge carries its own productivity: `Select A (alpha B beta) x` means either
  `x` is in `FIRST(alpha B beta)` - a stopping witness - or `alpha B beta` erases and
  `x` is in `FOLLOW(A)`.  The two cases are `SelLCFirst` and `SelLCNErased`, and every
  selected edge is one of them (`selLeftCorner_cases`).

### The proof

A path is split (`selPathF_or_selPathE`) into one with a FIRST-justified edge (`SelPathF`)
and one whose edges all erase (`SelPathE`).

* `SelPathF`: the FIRST edge gives a head-expansion trace to a form sitting at `x`
  (`headSteps_stop_of_first`, proved by lifting head traces across a single derivation step
  with `headSteps_lift_derives1` - the replacement for a diamond property, since no
  arbitrary derivation is ever reordered).  Appending a continuation to that trace leaves
  its length untouched, so the stopping length from `var A :: psi` is a constant `c` for
  every `psi`.  Going once around the cycle costs `0 < J` expansions and lands on
  `var A :: delta ++ psi`, whose stopping length is the same `c`; uniqueness gives
  `c = J + c`.
* `SelPathE`: every production on the cycle erases, so `A` erases, the cycle tail `delta`
  erases, and `x in FOLLOW(A)` supplies a continuation `post` with `x in FIRST(post)`.
  Now `var A :: delta^n ++ post` erases down to `post`, so it has a stopping witness of
  some length `c_n`, and uniqueness gives `c_n = J + c_(n+1)`: an infinite descent in `Nat`.

### Theorem inventory (Phase 5.3)

```text
Grammar.SelectedLeftCorner / SelectedLCPath    the review's relation, now in the library
Grammar.SelLCFirst / SelLCNErased              the two shapes of a selected edge
Grammar.SelPathF / SelPathE                    the path case split
Grammar.FirstList.of_atLookahead_free          AtLookahead x ys -> FirstList ys x (no Reduced)
headSteps_stop_length_unique_free              determinism of head expansion under Ll1 alone
headSteps_lift_derives1 / headAt_of_derives    lifting a trace across one derivation step
headSteps_stop_of_first                        FirstList xs x -> a trace stopping at x
selectedLCPath_trace                           a path is a positive head-expansion trace
selLCFirst_uniform_stop / selPathF_uniform_stop  the uniform stopping witness
selPathE_erases                                target erases, tail erases, lookahead in FOLLOW
noSelPathF_cycle / noSelPathE_cycle            the two counting contradictions
Grammar.noSelectedLCCycle                      the theorem
Examples.UnreachableSelectedCycle              why reachability is required
```

## Phase 5.4 - checked generation (`Generate.lean`)

`genTable` is unconditional: it writes an entry for every pair that selects a production
and silently keeps the first one when several do, so the LL(1) guarantee lives in the
theorems' hypotheses rather than in the API.  `Grammar.generate` cannot hand out a bad
table: it enumerates the conflict list over the finite carrier and returns either the
table or two concrete distinct productions of one nonterminal claiming one lookahead.

```lean
Grammar.generate_eq_ok_iff : generate = ok genTable <-> ll1Check = true
Grammar.generate_iff_Ll1   : (exists M, generate = ok M) <-> G.Ll1
Grammar.generate_ok        : generate = ok M -> G.Ll1 and M.Sound G
Grammar.generate_conflict  : generate = conflict A x r1 r2 -> G.Conflict A x
Grammar.generate_not_ok    : ll1Check = false -> generate names a conflict
```

Production identity is the right-hand side throughout, matching the rest of the
development.  Two validation grammars check both outcomes: `S -> a | ab` is rejected
naming `[a]` and `[a b]` at the lookahead `a`, and a clean grammar yields the table.

## Phase 5.5 - the classical characterization (`Classical.lean`)

`Grammar.ClassicalLL1` is the textbook definition, stated with productions, leftmost
derivations and lookahead only - no FIRST, FOLLOW, SELECT, table or parser:

```lean
G.Reduced -> (G.ll1Check = true <-> G.ClassicalLL1)
```

The forward direction needs no reduction hypothesis (the bridge lemma
`select_of_derives` does it).  The converse needs three constructions:

* **Leftmost realization of an occurrence** (`leftDerives_head_of_derives`): if the start
  derives a form containing `var A`, some *leftmost* derivation reaches a configuration
  headed by `var A` whose continuation still derives the original tail.  Keeping that
  chain is what transports a FOLLOW witness to the realized continuation.  The weaker
  statement with the tail unchanged is false even for reduced grammars:
  `S -> A X`, `A -> a`, `X -> b` reaches `A b` but never leftmost.
  The induction asks where the distinguished occurrence sits relative to the last redex
  (`hole_locate`); when the redex *creates* the occurrence the hypothesis is applied to the
  redex instead - legal because the distinguished nonterminal is universally quantified -
  and `Reduced` finishes the terminal prefix.
* **Completing witnesses** (`classical_word_first`, `classical_word_erased`): a FIRST
  witness leaves a tail inside a reachable form, so `Reduced` makes it productive and the
  production plus continuation completes to a terminal word whose lookahead is the one
  chosen; an erasing production takes its lookahead from the continuation instead.
* **The four SELECT combinations** (FIRST/FIRST, FIRST/FOLLOW, FOLLOW/FIRST,
  FOLLOW/FOLLOW) then feed `ClassicalLL1` two leftmost derivations with one lookahead and
  different productions - contradiction.

A note on what is deliberately *not* here: the tempting diamond lemma "if `xs =* ys` and
`xs` is matched by a forest then `ys` is matched by a forest with the same yield" is false
for ambiguous grammars (`A -> a | b`), and `lookaheadOf w = x` is therefore obtained by
constructing the word rather than by uniqueness of it.

### Theorem inventory (Phase 5.5)

```text
Grammar.ClassicalLL1                     the derivation-level definition
Grammar.classicalLL1_of_ll1 / of_ll1Check  the forward direction (no Reduced)
leftDerives_of_derives                   derivation to a word -> leftmost derivation
hole_locate / hole_locate_nil            locating a hole relative to a redex
leftDerives_head_of_derives              occurrence -> leftmost configuration + chain
classical_word_first / classical_word_erased  the two witness completions
Grammar.ll1Check_iff_classicalLL1        the characterization
Examples.ToyReduced.toy_classicalLL1     derived for the toy grammar
```

## Limitations and next steps

* `Table.Correct` is *not* proved equivalent to "the table was generated": the generator
  produces *a* correct table, and `Examples/Continuation.lean` shows no table can satisfy
  the unrestricted variant of `Complete`.
* `ll1Check G = true` does not by itself imply `noLeftRecursion G = true` *for an arbitrary
  grammar* - and Phase 5.2 proves it cannot: `Examples/LeftRecChecks.lean` exhibits grammars
  that pass the conflict check and fail the left-recursion check.  What *is* proved
  (`Grammar.noLeftRecursion_of_ll1`) is the classical statement: for a **reduced** grammar
  (every nonterminal with a production occurs, every occurring nonterminal is productive)
  LL(1) implies no left recursion, so for grammars that are reduced the two hypotheses of
  `generated_language_iff` collapse into one - and `generated_language_iff_ll1` shows the
  end-to-end theorem only ever needed LL(1) in the first place.
* The `decide` proofs of `circ_ll1` / `qc_ll1` cost seconds of kernel time.  Phase 4.0b
  memoises the analysis that dominates that cost (see the performance section below); the
  remaining cost is the size of the finite computation, not a soundness issue.
## Phase 6 — the quantum circuit language

Two grammars, one with token kinds and one with qubit *payloads*.

### `Examples/Circuits.lean` (token kinds)

`h q0 ;`, `cx q0 q1 ;`, `s q1 ;`, `m q0 ;` with sequences and the empty program; the qubit
positions are fixed by the grammar.  A hand-written table `M` is certified against the
Phase 2 predicate (`M_sound`, by `decide`), the parser reconstructs the Phase 1 trees by
`rfl` (`parse_hcx_ok`), soundness is instantiated (`parse_hcx_sound`), and malformed inputs
fail with structured errors (`parse_bad_err`, `parse_truncated_err`).  Phase 5 then proves
that the *generated* table agrees with `M` on every index pair (`gen_eq_hand_list` style
checks are expensive for this grammar, so the table is printed instead).

### `Examples/QCircuits.lean` (qubit payloads, AST, printer)

Here the qubit identifier is structured data: a nonterminal `qubit -> q0 | q1` appears in
the gate productions, so `h q1 ;` is a program.  This grammar is parsed by the *generated*
table — no hand-written table is needed.

* `qc_ll1 : Q.ll1Check = true` and `qc_no_left_recursion : Q.noLeftRecursion = true`, both
  discharged by `decide` (kernel computations, a few seconds each), so the Phase 5
  correctness and termination theorems apply; `qc_end_to_end` states the characterisation.
* `Qubit`, `Instr` (`hadamard`, `cnot`, `phase`, `measure`), `Program = List Instr` — the
  AST.  `printInstr` / `printProg` are the pretty-printer; `qubitOfTree` … `progOfTree` are
  the AST extractor (total functions returning `Option`, failing on shapes the grammar
  cannot produce).
* `progTree : Program → Tree Tok Var` builds the canonical parse tree, and
  `valid_progTree`, `yield_progTree`, `progOf_progTree` prove it is valid, prints to
  `printProg p`, and extracts back to `p`.
* `language_printProg p : Q.language (printProg p)` — printing produces a word of the
  language, hence (Phase 5) the generated parser accepts it.
* **Canonical-tree inversion**: `valid_qubit_canonical`, `valid_instr_canonical`,
  `valid_instrs_canonical`, `valid_prog_canonical` — a *valid* tree of this grammar is the
  canonical tree of a unique program, proved by inverting the productions (the two qubit
  productions force the two qubit trees; the gate productions force keyword, payload and
  terminator children; `instrs` recurses through the matching forest, whose induction
  hypothesis already covers the smaller `instrs` child).  No parser is involved.
* **Extraction of parser output**: `progOfTree_total` (the extractor is total on valid
  program trees), `printProg_toAST` (printing what it extracted gives back the yield of the
  tree), `parse_printProg` (the *generated parser* returns `progTree p` on `printProg p`),
  `progOfTree_of_parse_success` (**any** successful fuel returns a tree extracting to `p`)
  and `parse_output_canonical` (every accepted tree is canonical *and* extracts to the
  printed program).  These rest on exact-tree completeness and output uniqueness, not on the
  left-recursion ranking.
* **Validation**: `round_trip_empty`, `round_trip_all_forms` (every instruction form and
  every qubit combination in one mixed sequence), and `parse_hq1_fuel20` /
  `parse_hcx_fuel60` — concrete parses checked by `rfl` at explicit fuel values.
* **`round_trip`**: for every program `p`, `progOfTree (progTree p) = some p`,
  `yield (progTree p) = printProg p`, and *the generated parser accepts the printed
  program* with a valid tree whose yield is exactly `printProg p` — i.e. print → parse →
  (extract) is the identity on programs, and the parser consumes the whole printed input.
* Invalid inputs: `h ;` and `h q0` are rejected with structured errors (printed by
  `#eval`); the general guarantee is `never_accepts_of_not_language`, which needs only
  table soundness.

### What is *not* claimed

* Nothing is left unclaimed here any more: the extractor was previously proved to invert the
  *canonical* tree builder only, and is now also proved total on an arbitrary valid tree
  (`progOfTree_total`) and correct on *parser output* (`parse_output_canonical`,
  `progOfTree_of_parse_success`).  The per-nonterminal shape analysis the old note deferred
  is `valid_qubit_canonical` / `valid_*gate_canonical` / `valid_instr_canonical` /
  `valid_instrs_canonical` / `valid_prog_canonical`.
* Qubit identifiers are enumerated (`q0`, `q1`) rather than arbitrary numerals: a numeral
  payload would need the parser to match a *class* of tokens, which the Phase 2 parser
  deliberately does not do (it compares terminals for equality).

## Remaining work

* Pre-index the production list (currently a linear scan inside every `selectTest`), give
  FIRST a carrier of only the symbol/lookahead pairs the grammar can reach, and cache the
  left-corner rows per source: all three are representation changes that the measurements
  say are worth doing, and none of them affects a proof.
* **The fuel bound is still open.**  `generated_language_iff_ll1` is existential in the fuel:
  every word of the language is accepted at *some* fuel, and `parseForest_stable` (Phase 5.1
  plus the new `fuel_stable`) now says that any outcome other than fuel exhaustion is the
  outcome at every larger fuel.  What is missing is an executable `fuelFor G ws` that is
  large enough for *every* input, valid or not, so that the parser becomes a total decision
  procedure.  Phase 5.3 supplies the semantic ingredient (no reachable selected cycle, hence
  no infinite non-consuming descent); the remaining work is to turn the parser's call tree
  into a numeric depth bound - a rank on the *lookahead-indexed* selected relation, plus the
  observation that every recursive call keeps a reachable context and that a call which does
  not consume a token descends along such an edge.
* `genTable` still exists alongside `generate`.  The unchecked table is what the theorems are
  stated about, so it stays; `generate` is the API a caller should use, and
  `generate_iff_Ll1` says the two agree exactly when the grammar is LL(1).
* `ClassicalLL1` is proved equivalent to the check only for **reduced** grammars, matching
  the textbook hypothesis.  Dropping or weakening `Reduced` is open: the review's
  `S -> a; U -> a | ab` (unreachable FIRST conflict) and
  `S -> aU | aV; U -> U; V -> V` (vacuous successful derivations) both show a hypothesis is
  needed, but neither is the exact boundary.
* Extend the DSL: numeral qubit identifiers would need the parser to match a *class* of
  tokens, which the Phase 2 parser deliberately does not do.
