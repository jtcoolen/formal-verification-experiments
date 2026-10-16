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
| 4 | `NULLABLE` / `FIRST` / `FOLLOW` specifications + fixed-point computations, soundness/completeness/termination | `NULLABLE` **done**; `FIRST`/`FOLLOW` in progress |
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
│   ├── Leftmost.lean           # leftmost derivations, the leftmost-derivation lemma
│   ├── Table.lean              # LTok (with eof), Table, Sound/Adequate/Complete, soundCheck
│   ├── Parser.lean             # fuelled table-driven parser + soundness
│   ├── Completeness.lean       # monotonicity, rank, completeness, rejection
│   ├── Fixpoint.lean           # generic finite monotone fixed-point iteration
│   ├── Nullable.lean           # NULLABLE spec + computation + soundness/completeness
│   └── Examples/
│       ├── Toy.lean            # ε-productions, acceptance *and* rejection proofs
│       ├── Circuits.lean       # quantum circuit DSL grammar (Phase 6 language)
│       ├── Continuation.lean   # why table correctness needs a reachability hypothesis
│       └── Loop.lean           # a Correct table that loops: progress is necessary
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

* Phases 4–5 are not implemented yet: there is no `FIRST`/`FOLLOW` computation and
  no LL(1) condition, so no table has yet been *generated* — the example tables are
  hand-written and certified against the Phase 2 predicate.
* `Grammar.wellFormed` is stated but not yet *used* by any theorem; when Phase 5
  states the generator's correctness it will appear as an explicit hypothesis.
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

## Next step (Phase 4, continued)

`FIRST` and `FOLLOW` in the same style:

* `G.FirstList xs x` := (∃ ys, Derives G xs (tok t :: ys)) for a token `x = tok t`, and
  `Derives G xs []` for `x = eof` — the standard `FIRST_1`, stated with derivations;
* `G.FollowSym A x` := ∃ pre post, Derives G [var start] (toks pre ++ [var A] ++ post)
  ∧ G.FirstList post x — the classical `S ⇒* α A β` with `x ∈ FIRST(β)`, which puts
  `eof ∈ FOLLOW(A)` exactly when `A` can be followed by nothing;
* both computed by `Fixpoint.iterP` over the finite enumerations of `Sym T N` and
  `N × LTok T`, with NULLABLE as a fixed input, each with soundness, completeness and
  the characterisation theorem.
