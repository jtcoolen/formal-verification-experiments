/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Table

/-!
# Phase 2.2 — A table-driven parser and its soundness

## The parser

A predictive (recursive-descent shaped) interpreter over a `Table`:

* a terminal symbol is matched against the lookahead and consumed;
* a nonterminal symbol `A` is expanded by the right-hand side the table proposes for
  the pair `(A, lookahead)`; if the table has no entry the parse fails with a
  structured error naming the nonterminal and the offending lookahead;
* the tree is built *bottom-up as the recursion unwinds*, so a successful parse
  returns a `Tree` whose nodes are exactly the productions that were used.

The interpreter carries an explicit fuel argument, which makes it structural (hence
total, hence executable) with no `partial`.  Phase 3 will supply the fuel from the
input and the grammar, turning this into a total parser with unconditional
termination.

## What is proved here

`sound_aux` (hence `parseForest_sound`, `parseSym_sound` and `parse_sound`), by
induction on the fuel: if a (sub)parse succeeds then

1. the forest it returned is a `MatchList` for the symbols it was asked to parse —
   i.e. it is *valid*, using only productions of the grammar; and
2. the tokens it consumed are exactly the yield of that forest.

Point (1) needs only `Table.Sound` (every entry names a production).  That is
deliberate: soundness of the *result* must not depend on the adequacy properties
that are needed for completeness.

## Why this is not circular

The statements are phrased entirely with the Phase 1 predicates `MatchList`, `Valid`,
`Tree.yield` and the Phase 1 derivation relation (through `Table.Sound`).  The
parser is not used to define any of them.
-/

universe u v w

-- The section instances `LawfulBEq T` / `LawfulBEq N` are needed by the parser
-- definitions but not by every equation lemma about them.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace VerifiedLL1

/-- Structured parse errors.  Errors carry the data a user needs: which nonterminal
had no table entry for which lookahead, or which terminal was expected where. -/
inductive ParseError (T : Type u) (N : Type v) where
  | noEntry : N → LTok T → ParseError T N
  | tokenMismatch : T → LTok T → ParseError T N
  | outOfFuel : ParseError T N
  | malformed : ParseError T N
  | trailing : LTok T → ParseError T N
  deriving Repr

/-- The result of a (sub)parse: a value together with the *remaining* input, or an
error. -/
inductive PRes (T : Type u) (N : Type v) (α : Type w) where
  | ok : α → List (LTok T) → PRes T N α
  | error : ParseError T N → PRes T N α
  deriving Repr

/-- Sequencing of parser results. -/
def pbind (r : PRes T N α) (f : α → List (LTok T) → PRes T N β) : PRes T N β :=
  match r with
  | PRes.ok a rest => f a rest
  | PRes.error e => PRes.error e

theorem pbind_ok {r : PRes T N α} {f : α → List (LTok T) → PRes T N β} {b : β}
    {rest : List (LTok T)} (h : pbind r f = PRes.ok b rest) :
    ∃ a mid, r = PRes.ok a mid ∧ f a mid = PRes.ok b rest := by
  cases r with
  | ok a mid =>
      simp only [pbind] at h
      exact ⟨a, mid, rfl, h⟩
  | error e => simp [pbind] at h

namespace Parser

variable {T : Type u} {N : Type v} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N]

mutual
/-- Parse one symbol against the input, producing the corresponding subtree. -/
def parseSym (M : Table T N) : (fuel : Nat) → (s : Sym T N) →
    (input : List (LTok T)) → PRes T N (Tree T N)
  | _, Sym.tok t, LTok.tok t' :: rest =>
      if t == t' then PRes.ok (Tree.leaf t) rest
      else PRes.error (ParseError.tokenMismatch t (LTok.tok t'))
  | _, Sym.tok t, x :: _ => PRes.error (ParseError.tokenMismatch t x)
  | _, Sym.tok _, [] => PRes.error ParseError.malformed
  | 0, Sym.var _, _ => PRes.error ParseError.outOfFuel
  | fuel + 1, Sym.var A, input =>
      match input with
      | [] => PRes.error ParseError.malformed
      | x :: _ =>
          match M.get A x with
          | none => PRes.error (ParseError.noEntry A x)
          | some rhs =>
              match parseForest M fuel rhs input with
              | PRes.ok ts rest => PRes.ok (Tree.node A ts) rest
              | PRes.error e => PRes.error e

/-- Parse a list of symbols, producing a forest. -/
def parseForest (M : Table T N) : (fuel : Nat) → (syms : List (Sym T N)) →
    (input : List (LTok T)) → PRes T N (List (Tree T N))
  | 0, _, _ => PRes.error ParseError.outOfFuel
  | fuel + 1, [], input => PRes.ok [] input
  | fuel + 1, s :: ss, input =>
      pbind (parseSym M fuel s input) fun t rest =>
        pbind (parseForest M fuel ss rest) fun ts rest' => PRes.ok (t :: ts) rest'
end

/-- The top-level parser: parse the start symbol and require that the whole input,
up to its end-of-input marker, has been consumed. -/
def parse (G : Grammar T N) (M : Table T N) (fuel : Nat) (input : List (LTok T)) :
    PRes T N (Tree T N) :=
  match parseForest M fuel [Sym.var G.start] input with
  | PRes.ok [t] [LTok.eof] => PRes.ok t [LTok.eof]
  | PRes.ok _ rest => PRes.error (ParseError.trailing (rest.headD LTok.eof))
  | PRes.error e => PRes.error e

end Parser

section Soundness

variable {T : Type u} {N : Type v} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] {M : Table T N}
  {G : Grammar T N}

open Parser

-- The section variables \`LawfulBEq T\` / \`LawfulBEq N\` are needed by the parser
-- definitions but not by every equation lemma about them.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in

/-- The unfolding equations of the parser, as rewrite rules. -/
theorem parseForest_nil (input : List (LTok T)) :
    parseForest M (fuel + 1) [] input = PRes.ok [] input := rfl

theorem parseForest_cons (s : Sym T N) (ss : List (Sym T N)) (input : List (LTok T)) :
    parseForest M (fuel + 1) (s :: ss) input =
      pbind (parseSym M fuel s input) fun t rest =>
        pbind (parseForest M fuel ss rest) fun ts rest' => PRes.ok (t :: ts) rest' := rfl

theorem parseSym_terminal (t t' : T) (rest : List (LTok T)) :
    parseSym M fuel (Sym.tok t) (LTok.tok t' :: rest) =
      if t == t' then PRes.ok (Tree.leaf t) rest
      else PRes.error (ParseError.tokenMismatch t (LTok.tok t')) := by
  simp [parseSym]

theorem parseSym_var (A : N) (x : LTok T) (xs : List (LTok T)) :
    parseSym M (fuel + 1) (Sym.var A) (x :: xs) =
      match M.get A x with
      | none => PRes.error (ParseError.noEntry A x)
      | some rhs => match parseForest M fuel rhs (x :: xs) with
          | PRes.ok ts rest => PRes.ok (Tree.node A ts) rest
          | PRes.error e => PRes.error e := by
  simp [parseSym]

/-- Matching a terminal symbol: the only thing it can produce is the corresponding
leaf, and it consumes exactly that token. -/
theorem parseSym_tok {fuel : Nat} {a : T} {input : List (LTok T)} {t : Tree T N}
    {rest : List (LTok T)} (h : parseSym M fuel (Sym.tok a) input = PRes.ok t rest) :
    MatchList G [Sym.tok a] [t] ∧ tokensOf input = Tree.yield t ++ tokensOf rest := by
  cases input with
  | nil => exact absurd h (by simp [parseSym])
  | cons x xs =>
      cases x with
      | eof => exact absurd h (by simp [parseSym])
      | tok b =>
          rw [parseSym_terminal] at h
          split at h
          · next hab =>
              have hab' : a = b := eq_of_beq hab
              subst hab'
              cases h
              refine ⟨MatchList.tok MatchList.nil, ?_⟩
              simp [Tree.yield_leaf]
          · next hab => exact absurd h (by simp)

/-- The two soundness statements, proved together by induction on the fuel. -/
theorem sound_aux (hM : M.Sound G) :
    ∀ fuel : Nat,
      (∀ (syms : List (Sym T N)) (input : List (LTok T)) (ts : List (Tree T N))
          (rest : List (LTok T)),
          parseForest M fuel syms input = PRes.ok ts rest →
            MatchList G syms ts ∧
              tokensOf input = Tree.yieldForest ts ++ tokensOf rest) ∧
        (∀ (s : Sym T N) (input : List (LTok T)) (t : Tree T N) (rest : List (LTok T)),
          parseSym M fuel s input = PRes.ok t rest →
            MatchList G [s] [t] ∧
              tokensOf input = Tree.yield t ++ tokensOf rest) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro syms input ts rest h
        cases syms with
        | nil => exact absurd h (by simp [parseForest])
        | cons s ss => exact absurd h (by simp [parseForest])
      · intro s input t rest h
        cases s with
        | tok a => exact parseSym_tok h
        | var A => exact absurd h (by simp [parseSym])
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · intro syms input ts rest h
        cases syms with
        | nil =>
            obtain ⟨h1, h2⟩ := by simpa [parseForest_nil] using h
            subst h1
            refine ⟨MatchList.nil, ?_⟩
            rw [h2]
            simp [Tree.yieldForest_nil]
        | cons s ss =>
            rw [parseForest_cons] at h
            obtain ⟨t, rest', ht, hfor⟩ := pbind_ok h
            obtain ⟨x, y, h1, h2⟩ := pbind_ok hfor
            cases h2
            have ⟨hmatchS, hyieldS⟩ := ih.2 s input t rest' ht
            have ⟨hmatchF, hyieldF⟩ := ih.1 ss rest' x rest h1
            refine ⟨MatchList.append hmatchS hmatchF, ?_⟩
            rw [hyieldS, hyieldF]
            simp [Tree.yieldForest_cons, List.append_assoc]
      · intro s input t rest h
        cases s with
        | tok a => exact parseSym_tok h
        | var A =>
            cases input with
            | nil => exact absurd h (by simp [parseSym])
            | cons x xs =>
                rw [parseSym_var] at h
                cases hget : M.get A x with
                | none =>
                    simp only [hget] at h
                    exact absurd h (by simp)
                | some rhs =>
                    have hp : (A, rhs) ∈ G.productions := hM A x rhs hget
                    simp only [hget] at h
                    cases hfor : parseForest M fuel rhs (x :: xs) with
                    | ok ts rest' =>
                        rw [hfor] at h
                        obtain ⟨h1, h2⟩ := PRes.ok.inj h
                        rw [← h1, ← h2]
                        have ⟨hmatch, hyield⟩ := ih.1 rhs (x :: xs) ts rest' hfor
                        refine ⟨MatchList.var hp hmatch MatchList.nil, ?_⟩
                        simp [Tree.yield_node, hyield]
                    | error e =>
                        rw [hfor] at h
                        exact absurd h (by simp)

/-- **Parser soundness, forest form.**  A successful sub-parse returns a valid
forest, and the tokens it consumed are exactly that forest's yield. -/
theorem parseForest_sound (hM : M.Sound G) (fuel : Nat) (syms : List (Sym T N))
    (input : List (LTok T)) (ts : List (Tree T N)) (rest : List (LTok T))
    (h : parseForest M fuel syms input = PRes.ok ts rest) :
    MatchList G syms ts ∧ tokensOf input = Tree.yieldForest ts ++ tokensOf rest :=
  (sound_aux hM fuel).1 syms input ts rest h

/-- **Parser soundness, symbol form.** -/
theorem parseSym_sound (hM : M.Sound G) (fuel : Nat) (s : Sym T N) (input : List (LTok T))
    (t : Tree T N) (rest : List (LTok T))
    (h : parseSym M fuel s input = PRes.ok t rest) :
    MatchList G [s] [t] ∧ tokensOf input = Tree.yield t ++ tokensOf rest :=
  (sound_aux hM fuel).2 s input t rest h

/-- Inversion of a successful top-level parse. -/
theorem parse_ok {fuel : Nat} {input : List (LTok T)} {t : Tree T N} {rest : List (LTok T)}
    (h : parse G M fuel input = PRes.ok t rest) :
    parseForest M fuel [Sym.var G.start] input = PRes.ok [t] [LTok.eof] ∧
      rest = [LTok.eof] := by
  have key : ∀ (r : PRes T N (List (Tree T N))),
      (match r with
        | PRes.ok [t] [LTok.eof] => PRes.ok t [LTok.eof]
        | PRes.ok a rr => PRes.error (ParseError.trailing (rr.headD LTok.eof))
        | PRes.error e => PRes.error e) = PRes.ok t rest →
        r = PRes.ok [t] [LTok.eof] ∧ rest = [LTok.eof] := by
    intro r
    cases r with
    | ok xs rr =>
        cases xs with
        | nil => intro h; exact absurd h (by simp)
        | cons x xs' =>
            cases xs' with
            | cons y ys => intro h; exact absurd h (by simp)
            | nil =>
                cases rr with
                | nil => intro h; exact absurd h (by simp)
                | cons a ar =>
                    cases ar with
                    | cons b br => intro h; exact absurd h (by simp)
                    | nil =>
                        cases a with
                        | tok c => intro h; exact absurd h (by simp)
                        | eof =>
                            intro hh
                            cases hh
                            exact ⟨rfl, rfl⟩
    | error e => intro h; exact absurd h (by simp)
  exact key (parseForest M fuel [Sym.var G.start] input) (by simpa [parse] using h)

/--
**Phase 2 main theorem — soundness of the parser.**  Whenever the parser succeeds
on a well-formed input, the result is a *valid* parse tree of `G` whose yield is
exactly the whole input.  Only `Table.Sound` is used: the stronger adequacy
properties are needed for completeness (Phase 3), not for soundness. -/
theorem parse_sound (hM : M.Sound G) {fuel : Nat} {input : List (LTok T)} {t : Tree T N}
    (_hwf : WellFormedInput input)
    (h : parse G M fuel input = PRes.ok t [LTok.eof]) :
    Valid G t ∧ Tree.yield t = tokensOf input := by
  obtain ⟨hcall, _⟩ := parse_ok h
  obtain ⟨hmatch, hyield⟩ :=
    parseForest_sound hM fuel [Sym.var G.start] input [t] [LTok.eof] hcall
  obtain ⟨t', rhs, rest, hts, hp, hchild, hrest2⟩ := MatchList.eq_node_cons hmatch
  obtain ⟨h1, h2⟩ := List.cons.inj hts
  subst h1
  subst h2
  refine ⟨Valid.mk hp hchild, ?_⟩
  rw [hyield]
  simp [Tree.yieldForest_cons, Tree.yield_node]

end Soundness



end VerifiedLL1
