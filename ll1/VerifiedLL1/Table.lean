/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Leftmost

/-!
# Phase 2.1 — Predictive parsing tables

## Contents

* `LTok T` — the token alphabet extended with an explicit end-of-input marker.
* `Table T N` — a *finite* predictive table: a list of entries indexed by a
  nonterminal and one lookahead symbol, with a computable lookup.
* `Sound` / `Adequate` / `Complete` / `Correct` — what it means for a table to be
  correct for a grammar, stated **only** in terms of the Phase 1 derivation
  relation.

## Why the correctness predicate is stated with derivations, not with `FIRST`

The textbook definition says "`M A a = rhs ⟷ a ∈ SELECT(A,rhs)`", i.e. it is phrased
through `FIRST` and `FOLLOW`.  That is the right *construction* principle (Phase 5
will use it) but the wrong *specification* principle: if correctness is defined via
`FIRST`, then "the table is correct" only says something about our `FIRST`
computation, and the development risks becoming a self-consistency check of the
implementation.

The definitions below quantify over *stack continuations* and over the split of the
remaining input, and say directly what a table entry must guarantee:

* **Soundness of entries** (`Sound`): every entry names an actual production.  This
  alone already yields parser soundness: the tree the parser builds is valid.
* **Adequacy** (`Adequate`): if the table proposes `rhs` for `A` under lookahead
  `x`, then whenever the remaining input (whose first token is `x`) can be derived
  from `var A` followed by the continuation, it can also be derived from `rhs`
  followed by that continuation.  The table never steers a parse of a word of the
  language into a dead end.
* **Totality on the language** (`Complete`): whenever *some* production of `A` can
  start a derivation of the remaining input, the table offers an entry that can.
  This is what stops the parser from getting stuck on words of the language.

Nothing here mentions the parser, and nothing mentions the generator, so Phase 5
must prove a real theorem: that the generated table satisfies the predicate the
parser theorems consume.
-/

universe u v

namespace VerifiedLL1

/-- A lookahead symbol: an input token, or the explicit end-of-input marker. -/
inductive LTok (T : Type u) where
  | tok : T → LTok T
  | eof : LTok T
  deriving DecidableEq, Repr

/-- Equality of lookaheads, lifted from token equality. -/
def lbeq [BEq T] : LTok T → LTok T → Bool
  | LTok.tok a, LTok.tok b => a == b
  | LTok.eof, LTok.eof => true
  | _, _ => false

/-- The first token of a word, with `eof` for the empty word. -/
def lookaheadOf {T : Type u} (ws : List T) : LTok T :=
  match ws with
  | [] => LTok.eof
  | t :: _ => LTok.tok t

@[simp] theorem lookaheadOf_nil {T : Type u} : @lookaheadOf T [] = LTok.eof := rfl
@[simp] theorem lookaheadOf_cons {T : Type u} (t : T) (ws : List T) :
    lookaheadOf (t :: ws) = LTok.tok t := rfl

/-- The tokens occurring in a lookahead stream, in order. -/
def tokensOf {T : Type u} : List (LTok T) → List T :=
  List.filterMap (fun x => match x with | LTok.tok t => some t | LTok.eof => none)

@[simp] theorem tokensOf_nil {T : Type u} : @tokensOf T [] = [] := rfl
@[simp] theorem tokensOf_eof {T : Type u} : (@tokensOf T [LTok.eof]) = [] := rfl
@[simp] theorem tokensOf_cons_tok {T : Type u} (t : T) (ws : List (LTok T)) :
    tokensOf (LTok.tok t :: ws) = t :: tokensOf ws := rfl
@[simp] theorem tokensOf_cons_eof {T : Type u} (ws : List (LTok T)) :
    tokensOf (LTok.eof :: ws) = tokensOf ws := rfl
@[simp] theorem tokensOf_append {T : Type u} (xs ys : List (LTok T)) :
    tokensOf (xs ++ ys) = tokensOf xs ++ tokensOf ys := by simp [tokensOf]

@[simp] theorem tokensOf_map_tok {T : Type u} (ws : List T) : tokensOf (List.map LTok.tok ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w rest ih => simp [List.map, ih]

/-- A token word as a lookahead stream. -/
def ltoks {T : Type u} (ws : List T) : List (LTok T) := ws.map LTok.tok

@[simp] theorem ltoks_nil {T : Type u} : @ltoks T [] = [] := rfl
@[simp] theorem ltoks_cons {T : Type u} (t : T) (ws : List T) :
    ltoks (t :: ws) = LTok.tok t :: ltoks ws := rfl
@[simp] theorem ltoks_append {T : Type u} (ws vs : List T) :
    ltoks (ws ++ vs) = ltoks ws ++ ltoks vs := List.map_append
@[simp] theorem tokensOf_ltoks {T : Type u} (ws : List T) :
    tokensOf (ltoks ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w rest => simp [ltoks]

/-- A stream is a *well-formed input* when it is a token word followed by exactly
one end-of-input marker. -/
def WellFormedInput {T : Type u} (input : List (LTok T)) : Prop :=
  ∃ ws : List T, input = List.map LTok.tok ws ++ [LTok.eof]

theorem tokensOf_wellFormed {T : Type u} {input : List (LTok T)} (h : WellFormedInput input) :
    List.map LTok.tok (tokensOf input) ++ [LTok.eof] = input := by
  obtain ⟨ws, rfl⟩ := h
  simp

theorem lookahead_wellFormed {T : Type u} {input : List (LTok T)} (h : WellFormedInput input) :
    input.headD LTok.eof = lookaheadOf (tokensOf input) := by
  obtain ⟨ws, rfl⟩ := h
  cases ws with
  | nil => simp
  | cons t rest => simp [List.headD]

/-- A predictive parsing table: a finite list of entries, each pairing a
nonterminal and a lookahead with the right-hand side to expand to. -/
structure Table (T : Type u) (N : Type v) where
  entries : List (N × (LTok T × List (Sym T N)))

/-- `G.Reachable xs`: `xs` is a *suffix* of a sentential form of `G`, i.e. some symbol
list `pre` — the part of the form to its left, which a top-down parser has already
committed to — extends it to a form derivable from the start symbol.

This is the classical hypothesis of the LL(1) correctness proof (`S ⇒* α A β\', read as
`var A :: β is reachable\'), and it is exactly the invariant a predictive parser
maintains: its stack is always the unproduced suffix of a sentential form.  It cannot
be dropped: a table would then have to behave correctly on continuations the grammar
can never produce, which no table can do (`Examples/Continuation.lean\'). -/
def Grammar.Reachable (G : Grammar T N) (xs : List (Sym T N)) : Prop :=
  ∃ pre : List (Sym T N), Derives G [Sym.var G.start] (pre ++ xs)

namespace Grammar

/-- Reachability is inherited by derivable rewrites. -/
theorem reachable_of_derives {G : Grammar T N} {xs ys : List (Sym T N)}
    (h : G.Reachable xs) (h' : Derives G xs ys) : G.Reachable ys := by
  obtain ⟨pre, hpre⟩ := h
  exact ⟨pre, derives_trans hpre (derives_prefix h' pre)⟩

/-- Every suffix of a reachable form is reachable: the dropped symbol joins the prefix. -/
theorem reachable_tail {G : Grammar T N} {s : Sym T N} {xs : List (Sym T N)}
    (h : G.Reachable (s :: xs)) : G.Reachable xs := by
  obtain ⟨pre, hpre⟩ := h
  exact ⟨pre ++ [s], by rw [List.append_assoc]; exact hpre⟩

end Grammar
namespace Table

variable {T : Type u} {N : Type v}

/-- Table lookup: the right-hand side proposed for nonterminal `A` under lookahead
`x`.  Earlier entries shadow later ones. -/
def get [BEq N] [BEq T] (M : Table T N) (A : N) (x : LTok T) : Option (List (Sym T N)) :=
  (M.entries.find? fun e => e.1 == A && lbeq e.2.1 x).map fun e => e.2.2

/-- A table is **sound** when every entry names an actual production of the
grammar. -/
def Sound (G : Grammar T N) [BEq N] [BEq T] (M : Table T N) : Prop :=
  ∀ A x rhs, M.get A x = some rhs → (A, rhs) ∈ G.productions


/-- A table is **adequate**: an entry never destroys derivability.  If the table
proposes `rhs` for `A` under lookahead `x`, then whenever `var A :: cont` is the
active part of a sentential form and the remaining input `u ++ v` (whose first token
is `x`) can be derived from it, then `u ++ v` can also be derived from `rhs ++ cont`.
-/
def Adequate (G : Grammar T N) [BEq N] [BEq T] (M : Table T N) : Prop :=
  ∀ (A : N) (x : LTok T) (rhs : List (Sym T N)), M.get A x = some rhs →
    ∀ (cont : List (Sym T N)) (u v : List T),
      G.Reachable (Sym.var A :: cont) →
        lookaheadOf (u ++ v) = x →
          Derives G (Sym.var A :: cont) (toks (u ++ v)) →
            Derives G (rhs ++ cont) (toks (u ++ v))

/-- A table is **complete for the language**: whenever some production of `A` lets
the remaining input be derived, and `var A :: cont` is the active part of a
sentential form, the table offers an entry that lets it be derived. -/
def Complete (G : Grammar T N) [BEq N] [BEq T] (M : Table T N) : Prop :=
  ∀ (A : N) (cont : List (Sym T N)) (u v : List T),
    G.Reachable (Sym.var A :: cont) →
      (∃ rhs, (A, rhs) ∈ G.productions ∧
          Derives G (rhs ++ cont) (toks (u ++ v))) →
        ∃ rhs, M.get A (lookaheadOf (u ++ v)) = some rhs ∧
          Derives G (rhs ++ cont) (toks (u ++ v))

/-- The *unrestricted* variant of `Complete`, kept only to record why the reachability
hypothesis is needed: it demands the guarantee for **every** continuation, including
continuations no parse of the grammar can ever produce.  `Examples/Continuation.lean`
proves that `CompleteStrong` is unsatisfiable — even for a grammar that is LL(1) — so
no generator could ever produce a table meeting it. -/
def CompleteStrong (G : Grammar T N) [BEq N] [BEq T] (M : Table T N) : Prop :=
  ∀ (A : N) (cont : List (Sym T N)) (u v : List T),
    (∃ rhs, (A, rhs) ∈ G.productions ∧
        Derives G (rhs ++ cont) (toks (u ++ v))) →
      ∃ rhs, M.get A (lookaheadOf (u ++ v)) = some rhs ∧
        Derives G (rhs ++ cont) (toks (u ++ v))

/-- **Table correctness**: the independent specification consumed by the parser
theorems. -/
def Correct (G : Grammar T N) [BEq N] [BEq T] (M : Table T N) : Prop :=
  M.Sound G ∧ M.Adequate G ∧ M.Complete G

theorem Correct.sound {G : Grammar T N} [BEq N] [BEq T] {M : Table T N} (h : M.Correct G) :
    M.Sound G := h.1
theorem Correct.adequate {G : Grammar T N} [BEq N] [BEq T] {M : Table T N} (h : M.Correct G) :
    M.Adequate G := h.2.1
theorem Correct.complete {G : Grammar T N} [BEq N] [BEq T] {M : Table T N} (h : M.Correct G) :
    M.Complete G := h.2.2

/-- If the first result of a `find?` is `some a`, then `a` is in the list and
satisfies the predicate. -/
theorem find?_eq_some {α : Type w} {p : α → Bool} {l : List α} {a : α}
    (h : List.find? p l = some a) : a ∈ l ∧ p a = true := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      by_cases hx : p x = true
      · have h2 : List.find? p (x :: xs) = some x := by simp [hx]
        have hxa : a = x := by simpa [h2] using h.symm
        subst hxa
        exact ⟨List.Mem.head _, hx⟩
      · have h2 : List.find? p (x :: xs) = List.find? p xs := by simp [hx]
        obtain ⟨hmem, hp⟩ := ih (by simpa [h2] using h)
        exact ⟨List.Mem.tail _ hmem, hp⟩

/-- **Decidable check** that every entry of the table names a production of `G`.
This is the shape Phase 5's generator will use to certify its own output. -/
def soundCheck [DecidableEq N] [DecidableEq T] (G : Grammar T N) (M : Table T N) : Bool :=
  M.entries.all fun e => G.productions.any fun p => p.1 == e.1 && p.2 == e.2.2

theorem sound_of_check [DecidableEq N] [DecidableEq T]
    (G : Grammar T N) (M : Table T N) (h : soundCheck G M = true) : M.Sound G := by
  have hentries : ∀ e ∈ M.entries, (e.1, e.2.2) ∈ G.productions := by
    intro e he
    have hall := (List.all_eq_true.mp h) e he
    obtain ⟨p, hp, hbeq⟩ := (List.any_eq_true.mp hall)
    have ⟨h1, h2⟩ : (p.1 == e.1) = true ∧ (p.2 == e.2.2) = true := by
      simpa [Bool.and_eq_true] using hbeq
    exact (eq_of_beq h1) ▸ (eq_of_beq h2) ▸ hp
  intro A x rhs hget
  unfold get at hget
  cases hfind : M.entries.find? (fun e => e.1 == A && lbeq e.2.1 x) with
  | none =>
      rw [hfind] at hget
      simp at hget
  | some e =>
      obtain ⟨hem, hpred⟩ := find?_eq_some hfind
      obtain ⟨hA, _⟩ : (e.1 == A) = true ∧ (lbeq e.2.1 x) = true := by
        simpa [Bool.and_eq_true] using hpred
      have he1 : e.1 = A := eq_of_beq hA
      rw [hfind] at hget
      simp at hget
      subst hget
      rw [← he1]
      exact hentries e hem

/-- The empty table. -/
def empty (T : Type u) (N : Type v) : Table T N := ⟨[]⟩

@[simp] theorem empty_get [BEq N] [BEq T] (A : N) (x : LTok T) :
    (Table.empty T N).get A x = none := by
  simp [get, Table.empty]

theorem empty_sound (G : Grammar T N) [BEq N] [BEq T] : (Table.empty T N).Sound G := by
  intro A x rhs h
  rw [empty_get] at h
  exact absurd h (by simp)

end Table

end VerifiedLL1
