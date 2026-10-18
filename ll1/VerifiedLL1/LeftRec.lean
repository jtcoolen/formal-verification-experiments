/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Generator

/-!
# Phase 5.2 - a reduced LL(1) grammar has no left recursion

## The theorem

The generator refuses a grammar whose *computed* left-recursion test fails.  This
module proves that the test can never fire on a grammar that is both *reduced*
(every nonterminal that has a production occurs, and every occurring nonterminal is
productive) and LL(1):

    Grammar.noLeftRecursion_of_ll1

Consequently a reduced LL(1) grammar always produces a table that the Phase 3 parser
can run to completion (Grammar.generated_language_iff consumes exactly this boolean).

## Why the naive argument fails

The textbook proof ranks a left corner  A =>+ B gamma  by FIRST and claims the rank
drops.  That is unsound here: a nullable edge with an erasable tail keeps every
lookahead of A available at B, so no strict decrease is available in general.  We
therefore count *head expansions* instead.

## The counted head-expansion trace

HeadSteps G xs ys k is a derivation of ys from xs in which exactly k head
nonterminals have been expanded: a step replaces the head variable A by the
right-hand side of one of its productions and leaves the continuation in place.
AtLookahead x ys says the form ys really *stops* at lookahead x: its head is the
token x, or ys = [] and x = eof.

The engine of the proof is headSteps_stop_length_unique: along a *reachable* form the
number of head expansions needed to reach a stopping position is unique.  Uniqueness
is the LL(1) property transported through select_of_first, the generalisation of the
bridge lemma select_of_derives from a terminal word to an arbitrary lookahead.
Productivity - the second half of Reduced - is what makes a stopping position a
*lookahead* position: the tail of the form a trace stops in has to erase down to
terminals, otherwise FIRST says nothing about it.

A left-corner cycle  A =>+ B gamma,  B =>* A delta  then supplies, for every n, a
reachable form  A delta^n post  whose unique stopping length c_n obeys
c_n = j + c_(n+1)  with 0 < j, while the yield chosen for A makes the lookahead
independent of n: an infinite strictly decreasing sequence of naturals.

## Where the hypotheses are used

* Ll1 - headSteps_stop_length_unique: two different productions selected by one
  lookahead is a Conflict.
* Reduced.2 (occurs implies productive) - the same lemma, to turn "the head of the
  stopping form is the token x" into a FirstList statement, and noLeftRecursion_aux,
  to make the cycle tail and the continuation erasable.
* Reduced.1 (has a production implies occurs) - so that the nonterminal carrying the
  cycle sits inside a sentential form, i.e. the forms  A delta^n post  are reachable.

## Necessity of the hypotheses

Examples.LeftRecUnreachable (U -> U | epsilon beside an unrelated start S -> s) has
ll1Check = true but noLeftRecursion = false: Reduced.1 fails there.
Examples.LeftRecUnproductive (S -> S) is the same with Reduced.2 failing.
Both are proved by decide.
-/

set_option linter.unusedSectionVars false

universe u v w

namespace VerifiedLL1

variable {T : Type u} {N : Type v} {G : Grammar T N}

@[simp] theorem toks_nil {T : Type u} {N : Type v} : @toks T N [] = [] := rfl

/-- delta^n: n copies of the list delta, concatenated. -/
def listPow {α : Type w} (δ : List α) : Nat → List α
  | 0 => []
  | n + 1 => δ ++ listPow δ n

@[simp] theorem listPow_zero {α : Type w} (δ : List α) : listPow δ 0 = [] := rfl
@[simp] theorem listPow_succ {α : Type w} (δ : List α) (n : Nat) :
    listPow δ (n + 1) = δ ++ listPow δ n := rfl

@[simp] theorem listPow_nil {α : Type w} : ∀ n : Nat, listPow ([] : List α) n = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [listPow_succ, ih]

/-- n copies of the forest ts, concatenated. -/
def forestPow {T : Type u} {N : Type v} (ts : List (Tree T N)) : Nat → List (Tree T N)
  | 0 => []
  | n + 1 => ts ++ forestPow ts n

@[simp] theorem forestPow_zero {T : Type u} {N : Type v} (ts : List (Tree T N)) :
    forestPow ts 0 = [] := rfl
@[simp] theorem forestPow_succ {T : Type u} {N : Type v} (ts : List (Tree T N)) (n : Nat) :
    forestPow ts (n + 1) = ts ++ forestPow ts n := rfl

@[simp] theorem forestPow_nil {T : Type u} {N : Type v} :
    ∀ n : Nat, forestPow ([] : List (Tree T N)) n = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [forestPow_succ, ih]

/-- A list whose every symbol derives a terminal word derives a terminal word. -/
theorem derives_toks_of_symbols (zs : List (Sym T N))
    (h : ∀ s ∈ zs, ∃ ws, Derives G [s] (toks ws)) : ∃ ws, Derives G zs (toks ws) := by
  induction zs with
  | nil => exact ⟨[], derives_refl []⟩
  | cons s rest ih =>
      obtain ⟨ws, h1⟩ := h s (List.Mem.head _)
      obtain ⟨vs, h2⟩ := ih (fun x hx => h x (List.Mem.tail _ hx))
      have := derives_append h1 h2
      exact ⟨ws ++ vs, by simpa [toks_append] using this⟩

section Reduced

/-- **Productivity.**  G.Productive A: some terminal word is derivable from A.  A
nonterminal that produces nothing but itself (S -> S) is not productive. -/
def Grammar.Productive (G : Grammar T N) (A : N) : Prop :=
  ∃ ws, Derives G [Sym.var A] (toks ws)

/-- **Reduced grammar.**  Every nonterminal that has a production occurs in some
sentential form, and every occurring nonterminal is productive: the classical *reduced*
normal form (reachable + productive), stated as two implications. -/
def Grammar.Reduced (G : Grammar T N) : Prop :=
  (∀ A, G.hasProduction A → G.Occurs A) ∧ (∀ A, G.Occurs A → G.Productive A)

namespace Grammar

/-- A variable that is a symbol of a reachable form occurs in a sentential form. -/
theorem occurs_of_mem_reachable_var {A : N} {xs : List (Sym T N)} (hR : G.Reachable xs)
    (hs : Sym.var A ∈ xs) : G.Occurs A := by
  obtain ⟨pre, hpre⟩ := hR
  obtain ⟨l₁, l₂, hsplit⟩ := exists_split_of_mem (Sym.var A) xs hs
  refine ⟨pre ++ l₁, l₂, ?_⟩
  simpa [hsplit] using hpre

/-- Under Reduced, every occurring variable of a reachable form is productive. -/
theorem productive_of_mem_reachable (hred : G.Reduced) {A : N} {xs : List (Sym T N)}
    (hR : G.Reachable xs) (hs : Sym.var A ∈ xs) : G.Productive A :=
  hred.2 A (occurs_of_mem_reachable_var hR hs)

/-- Under Reduced, *every* symbol of a reachable form derives a terminal word:
terminals trivially, variables by productivity. -/
theorem derives_toks_of_sym (hred : G.Reduced) {xs : List (Sym T N)} (hR : G.Reachable xs)
    {s : Sym T N} (hs : s ∈ xs) : ∃ ws, Derives G [s] (toks ws) := by
  cases s with
  | tok t => exact ⟨[t], derives_refl _⟩
  | var A =>
      obtain ⟨ws, hder⟩ := productive_of_mem_reachable hred hR hs
      exact ⟨ws, hder⟩

/-- Under Reduced, every reachable sentential form derives a terminal word. -/
theorem derives_toks_of_reachable (hred : G.Reduced) {xs : List (Sym T N)}
    (hR : G.Reachable xs) : ∃ ws, Derives G xs (toks ws) :=
  derives_toks_of_symbols xs (fun _s hs => derives_toks_of_sym hred hR hs)

end Grammar

end Reduced

section HeadSteps

/-- **Counted head expansions.**  HeadSteps G xs ys k: ys is obtained from xs by
expanding the *head* nonterminal k times, each step replacing the current head
variable by the right-hand side of one of its productions and leaving the surrounding
continuation in place.  The count k is what makes the relation deterministic under Ll1. -/
inductive HeadSteps (G : Grammar T N) : List (Sym T N) → List (Sym T N) → Nat → Prop where
  | refl (xs : List (Sym T N)) : HeadSteps G xs xs 0
  | step {A rhs cont ys k} : (A, rhs) ∈ G.productions →
      HeadSteps G (rhs ++ cont) ys k → HeadSteps G (Sym.var A :: cont) ys (k + 1)

/-- ys sits *at* the lookahead x: its head is the token x, or ys is empty and x = eof.
This is the stopping condition of a head-expansion trace. -/
def AtLookahead {T : Type u} {N : Type v} (x : LTok T) (ys : List (Sym T N)) : Prop :=
  match x with
  | .tok t => ∃ zs, ys = Sym.tok t :: zs
  | .eof => ys = []

/-- No form whose head is a variable sits at a lookahead; eof sits only at the empty form. -/
theorem atLookahead_not_var_head (x : LTok T) (A : N) (cont : List (Sym T N)) :
    ¬ AtLookahead x (Sym.var A :: cont) := by
  cases x with
  | tok t =>
      intro h
      obtain ⟨zs, hEq⟩ := h
      obtain ⟨h1, _⟩ := List.cons.inj hEq
      exact Sym.ne_tok_var t A h1.symm
  | eof => intro h; exact absurd h (by simp [AtLookahead])

/-- A token-headed form sits at that token's lookahead. -/
theorem atLookahead_tok (t : T) (zs : List (Sym T N)) :
    AtLookahead (LTok.tok t) (Sym.tok t :: zs) := ⟨zs, rfl⟩

/-- The empty form sits at eof. -/
theorem atLookahead_eof_nil : @AtLookahead T N LTok.eof [] := rfl

namespace HeadSteps

variable {G : Grammar T N}

/-- A head-expansion trace is a derivation. -/
theorem derives {xs ys : List (Sym T N)} {k : Nat} (h : HeadSteps G xs ys k) :
    Derives G xs ys := by
  induction h with
  | refl => exact derives_refl _
  | @step A rhs cont ys k hp htr ih =>
      have h1 : Derives G (Sym.var A :: cont) (rhs ++ cont) := by
        have := derives_ctx (derives_production A rhs hp) [] cont
        simpa using this
      exact derives_trans h1 ih

/-- A trace is stable under appending a fixed right context. -/
theorem append_right {xs ys : List (Sym T N)} {k : Nat} (δ : List (Sym T N))
    (h : HeadSteps G xs ys k) : HeadSteps G (xs ++ δ) (ys ++ δ) k := by
  induction h with
  | refl => exact HeadSteps.refl _
  | @step A rhs cont ys k hp htr ih =>
      have h1 : HeadSteps G (rhs ++ (cont ++ δ)) (ys ++ δ) k := by
        rw [← List.append_assoc]
        exact ih
      have h2 : HeadSteps G (Sym.var A :: (cont ++ δ)) (ys ++ δ) (k + 1) := HeadSteps.step hp h1
      simpa [List.cons_append] using h2

/-- Traces compose, and the counts add. -/
theorem trans {xs ys zs : List (Sym T N)} {k j : Nat}
    (h : HeadSteps G xs ys k) (h' : HeadSteps G ys zs j) : HeadSteps G xs zs (k + j) := by
  induction h with
  | refl => simpa [Nat.zero_add] using h'
  | @step A rhs cont ys k hp htr ih =>
      have h2 : HeadSteps G (rhs ++ cont) zs (k + j) := ih h'
      have h3 : HeadSteps G (Sym.var A :: cont) zs (k + j + 1) := HeadSteps.step hp h2
      have hEq : k + 1 + j = k + j + 1 := by omega
      exact hEq ▸ h3

/-- A positive-length trace begins by expanding its head variable. -/
theorem succ_inv {xs ys : List (Sym T N)} {k : Nat} (h : HeadSteps G xs ys (k + 1)) :
    ∃ A rhs cont, xs = Sym.var A :: cont ∧ (A, rhs) ∈ G.productions ∧
      HeadSteps G (rhs ++ cont) ys k := by
  cases h with
  | @step A rhs cont ys' k' hp htr => exact ⟨A, rhs, cont, rfl, hp, htr⟩

end HeadSteps

end HeadSteps

section Bridge

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The generalised bridge lemma.**  Where select_of_derives needs a *terminal*
continuation (toks w), this needs only that rhs ++ cont can *begin* with the lookahead
x.  The proof is the same split: the lookahead either comes from rhs (first disjunct of
Select), or rhs erases and it comes from cont, which is a legal FOLLOW witness because
var A :: cont is reachable. -/
theorem Grammar.select_of_first {A : N} {rhs cont : List (Sym T N)} {x : LTok T}
    (hR : G.Reachable (Sym.var A :: cont)) (hf : G.FirstList (rhs ++ cont) x) :
    G.Select A rhs x := by
  have hfollow : ∀ (y : LTok T), G.FirstList cont y → G.FollowSym A y := by
    intro y hy
    exact Grammar.followSym_of_reachable y hR hy
  cases x with
  | eof =>
      obtain ⟨hr, hc⟩ := derives_nil_append rhs cont hf
      exact Or.inr ⟨hr, hfollow LTok.eof hc⟩
  | tok t =>
      rcases Grammar.FirstList.append_decomp rhs cont (LTok.tok t) hf with hf' | hn
      · exact Or.inl ⟨by simp [isEof], hf'⟩
      · exact Or.inr ⟨hn.1, hfollow (LTok.tok t) hn.2⟩

/-- Under Reduced, a reachable form that *sits* at lookahead x has x in its FIRST.
This is the only place productivity is needed to speak about the FIRST of a stopping
form: its tail has to erase down to terminals. -/
theorem Grammar.FirstList.of_atLookahead (hred : G.Reduced) {x : LTok T}
    {ys : List (Sym T N)} (hR : G.Reachable ys) (ha : AtLookahead x ys) :
    G.FirstList ys x := by
  cases x with
  | tok t =>
      obtain ⟨zs, rfl⟩ := ha
      obtain ⟨vs, hder⟩ := Grammar.derives_toks_of_reachable hred (Grammar.reachable_tail hR)
      exact ⟨toks vs, derives_cons hder (Sym.tok t)⟩
  | eof =>
      have : ys = [] := ha
      subst this
      exact derives_refl []

end Bridge

section Uniqueness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **A form sitting at a lookahead has that lookahead in its FIRST.**  No productivity
hypothesis is needed: the witness is the form itself, because \`AtLookahead\` already names
the token (or the empty form) at the head.  Contrast \`Grammar.FirstList.of_atLookahead\`,
which proves the same statement through \`Reduced\` and returns a *terminal* tail. -/
theorem Grammar.FirstList.of_atLookahead_free {x : LTok T} {ys : List (Sym T N)}
    (ha : AtLookahead x ys) : G.FirstList ys x := by
  cases x with
  | tok t =>
      obtain ⟨zs, rfl⟩ := ha
      exact ⟨zs, derives_refl _⟩
  | eof =>
      have hnil : ys = [] := ha
      subst hnil
      exact derives_refl []

/-- **Determinism of head expansion, without \`Reduced\`.**  Productivity is only needed to
*produce* stopping witnesses, never to compare them: two traces from the same reachable
form that both stop at the same lookahead have the same length in any grammar.  The proof
is the original one, with \`Grammar.FirstList.of_atLookahead\` replaced by
\`Grammar.FirstList.of_atLookahead_free\`. -/
theorem headSteps_stop_length_unique_free (hall : G.Ll1)
    {xs ys₁ : List (Sym T N)} {k₁ : Nat} (h₁ : HeadSteps G xs ys₁ k₁) :
    ∀ (x : LTok T) (_ : G.Reachable xs), AtLookahead x ys₁ →
      ∀ (ys₂ : List (Sym T N)) (k₂ : Nat), HeadSteps G xs ys₂ k₂ → AtLookahead x ys₂ →
        k₁ = k₂ := by
  induction h₁ with
  | refl =>
      intro x _hR hs₁ ys₂ k₂ h₂ _
      cases h₂ with
      | refl => rfl
      | @step B rhs₂ cont' ys₂ k₂' hp₂ htr₂ =>
          exfalso
          exact atLookahead_not_var_head x B cont' hs₁
  | @step A rhs₁ cont ys₁' k₁' hp₁ htr₁ ih =>
      intro x hR hs₁ ys₂ k₂ h₂ hs₂
      cases h₂ with
      | refl =>
          exfalso
          exact atLookahead_not_var_head x A cont hs₂
      | @step B rhs₂ cont' ys₂ k₂' hp₂ htr₂ =>
          have hstep₁ : Derives G (Sym.var A :: cont) (rhs₁ ++ cont) := by
            have := derives_ctx (derives_production A rhs₁ hp₁) [] cont
            simpa using this
          have hstep₂ : Derives G (Sym.var A :: cont) (rhs₂ ++ cont) := by
            have := derives_ctx (derives_production A rhs₂ hp₂) [] cont
            simpa using this
          have hd₁ : Derives G (rhs₁ ++ cont) ys₁' := HeadSteps.derives htr₁
          have hd₂ : Derives G (rhs₂ ++ cont) ys₂ := HeadSteps.derives htr₂
          have hR₁ : G.Reachable (rhs₁ ++ cont) := Grammar.reachable_of_derives hR hstep₁
          have hR₂ : G.Reachable (rhs₂ ++ cont) := Grammar.reachable_of_derives hR hstep₂
          have hf₁ : G.FirstList (rhs₁ ++ cont) x :=
            Grammar.FirstList.backwards_derives x hd₁
              (Grammar.FirstList.of_atLookahead_free hs₁)
          have hf₂ : G.FirstList (rhs₂ ++ cont) x :=
            Grammar.FirstList.backwards_derives x hd₂
              (Grammar.FirstList.of_atLookahead_free hs₂)
          have s₁ : G.Select A rhs₁ x := Grammar.select_of_first hR hf₁
          have s₂ : G.Select A rhs₂ x := Grammar.select_of_first hR hf₂
          have hne : rhs₁ = rhs₂ := by
            by_cases h : rhs₁ = rhs₂
            · exact h
            · exact absurd ⟨rhs₁, rhs₂, hp₁, hp₂, h, s₁, s₂⟩ (hall A x)
          subst hne
          have hEq := ih x hR₁ hs₁ ys₂ k₂' htr₂ hs₂
          omega

/-- **Determinism of head expansion** (the historical \`Reduced\` form): an immediate
consequence of \`headSteps_stop_length_unique_free\`. -/
theorem headSteps_stop_length_unique (_hred : G.Reduced) (hall : G.Ll1)
    {xs ys₁ : List (Sym T N)} {k₁ : Nat} (h₁ : HeadSteps G xs ys₁ k₁) :
    ∀ (x : LTok T) (_ : G.Reachable xs), AtLookahead x ys₁ →
      ∀ (ys₂ : List (Sym T N)) (k₂ : Nat), HeadSteps G xs ys₂ k₂ → AtLookahead x ys₂ →
        k₁ = k₂ :=
  headSteps_stop_length_unique_free hall h₁

end Uniqueness
section Witnesses

/-- n copies of a matched right-hand side are matched by n copies of the forest. -/
theorem MatchList.forestPow {rhs : List (Sym T N)} {ts : List (Tree T N)}
    (h : MatchList G rhs ts) : ∀ n, MatchList G (listPow rhs n) (forestPow ts n) := by
  intro n
  induction n with
  | zero => exact MatchList.nil
  | succ n ih => exact MatchList.append h ih

/-- n copies of a forest yield n copies of the yield. -/
theorem Tree.yieldForest_forestPow (ts : List (Tree T N)) :
    ∀ n, Tree.yieldForest (forestPow ts n) = listPow (Tree.yieldForest ts) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [forestPow_succ, Tree.yieldForest_append, ih, listPow_succ]

/-- **Witness lemma.**  A forest matching xs yields a head-expansion trace from xs that
stops at the lookahead of its own yield.  A terminal head stops immediately (count 0);
a node expands through its production and either continues into the tail forest (when
its own yield is empty) or stops inside its children. -/
theorem headSteps_of_match {xs : List (Sym T N)} {ts : List (Tree T N)}
    (hm : MatchList G xs ts) :
    ∃ ys k, HeadSteps G xs ys k ∧ AtLookahead (lookaheadOf (Tree.yieldForest ts)) ys := by
  induction hm with
  | nil => exact ⟨[], 0, HeadSteps.refl _, atLookahead_eof_nil⟩
  | @tok rhs ts t hrest _ =>
      refine ⟨Sym.tok t :: rhs, 0, HeadSteps.refl _, ?_⟩
      have hy : Tree.yieldForest (Tree.leaf t :: ts) = t :: Tree.yieldForest ts := by
        simp [Tree.yieldForest_cons]
      have hlook : lookaheadOf (Tree.yieldForest (Tree.leaf t :: ts)) = LTok.tok t := by
        rw [hy]; rfl
      rw [hlook]
      exact atLookahead_tok t rhs
  | @var rhs ts A ts' rhsA hp hchild hrest ihchild ihrest =>
      obtain ⟨ys₁, k₁, ht₁, ha₁⟩ := ihchild
      obtain ⟨ys₂, k₂, ht₂, ha₂⟩ := ihrest
      have hy : Tree.yieldForest (Tree.node A ts' :: ts)
          = Tree.yieldForest ts' ++ Tree.yieldForest ts := by
        simp [Tree.yieldForest_cons]
      have hcase : ∀ (ws : List T), ws = [] ∨ ∃ t rest, ws = t :: rest := by
        intro ws
        cases ws with
        | nil => exact Or.inl rfl
        | cons t rest => exact Or.inr ⟨t, rest, rfl⟩
      obtain (heq | ⟨t, rest, heq⟩) :
          Tree.yieldForest ts' = [] ∨ ∃ t rest, Tree.yieldForest ts' = t :: rest :=
        hcase (Tree.yieldForest ts')
      · -- the head subtree erases: the trace continues into the tail forest
        have ha₁' : AtLookahead LTok.eof ys₁ := by
          rw [heq] at ha₁
          exact ha₁
        have heq' : ys₁ = [] := ha₁'
        subst heq'
        have h1 : HeadSteps G (rhsA ++ rhs) rhs k₁ := by
          have := HeadSteps.append_right rhs ht₁
          simpa using this
        refine ⟨ys₂, k₁ + k₂ + 1, HeadSteps.step hp (HeadSteps.trans h1 ht₂), ?_⟩
        rw [hy, heq, List.nil_append]
        exact ha₂
      · -- the head subtree has a token head: the trace stops there
        have ha₁' : AtLookahead (LTok.tok t) ys₁ := by
          rw [heq] at ha₁
          exact ha₁
        obtain ⟨zs, heq'⟩ := ha₁'
        subst heq'
        have h1 : HeadSteps G (rhsA ++ rhs) (Sym.tok t :: zs ++ rhs) k₁ :=
          HeadSteps.append_right rhs ht₁
        refine ⟨Sym.tok t :: zs ++ rhs, k₁ + 1, HeadSteps.step hp h1, ?_⟩
        have hlook : lookaheadOf (Tree.yieldForest (Tree.node A ts' :: ts)) = LTok.tok t := by
          simp [hy, heq]
        rw [hlook]
        exact atLookahead_tok t (zs ++ rhs)

/-- **One left corner is a positive head-expansion trace.**  The erasable prefix of the
left-corner definition is expanded by a forest with empty yield, so the trace lands on
the left-corner variable itself. -/
theorem headSteps_of_leftCorner {A B : N} (h : G.LeftCorner A B) :
    ∃ γ k, 0 < k ∧ HeadSteps G [Sym.var A] (Sym.var B :: γ) k := by
  obtain ⟨α, β, hprod, hder⟩ := h
  obtain ⟨ts, hm, hy⟩ := derives_forest (ws := []) hder
  obtain ⟨ys, k, ht₁, ha⟩ := headSteps_of_match hm
  have heq : ys = [] := by
    rw [hy] at ha
    exact ha
  subst heq
  have hnil : α ++ [Sym.var B] ++ β ++ [] = α ++ [Sym.var B] ++ β := List.append_nil _
  have h0 : HeadSteps G [Sym.var A] (α ++ [Sym.var B] ++ β) 1 := by
    rw [← hnil]
    exact HeadSteps.step hprod (HeadSteps.refl _)
  have h1 : HeadSteps G (α ++ [Sym.var B] ++ β) ([Sym.var B] ++ β) k := by
    have := HeadSteps.append_right ([Sym.var B] ++ β) ht₁
    simpa using this
  have h2 : HeadSteps G [Sym.var A] ([Sym.var B] ++ β) (1 + k) := HeadSteps.trans h0 h1
  have hEq : 1 + k = k + 1 := by omega
  exact ⟨β, k + 1, Nat.zero_lt_succ _, hEq ▸ h2⟩

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **A left-corner cycle is a positive-length trace from a variable back in front of
itself.**  LcReach is consumed through its induction principle lcReach_ind, with the set
of variables reachable from B *by head-expansion traces*; that set is closed under left
corners by composition plus right context. -/
theorem headSteps_of_lcReach {A B : N} (hcorner : G.LeftCorner A B)
    (hreach : G.LcReach B A) :
    ∃ δ j, 0 < j ∧ HeadSteps G [Sym.var A] (Sym.var A :: δ) j := by
  obtain ⟨β, j, hj, ht⟩ := headSteps_of_leftCorner hcorner
  have hstep : ∀ C D, G.LeftCorner C D →
      (∃ γ k, HeadSteps G [Sym.var B] (Sym.var C :: γ) k) →
      ∃ γ k, HeadSteps G [Sym.var B] (Sym.var D :: γ) k := by
    intro C D hc ⟨γ, k, ht₁⟩
    obtain ⟨δ, l, _, ht₂⟩ := headSteps_of_leftCorner hc
    have h3 : HeadSteps G (Sym.var C :: γ) (Sym.var D :: δ ++ γ) l := by
      have := HeadSteps.append_right γ ht₂
      simpa using this
    exact ⟨δ ++ γ, k + l, HeadSteps.trans ht₁ h3⟩
  obtain ⟨γ, k, ht₃⟩ :=
    Grammar.lcReach_ind G B (fun C => ∃ γ k, HeadSteps G [Sym.var B] (Sym.var C :: γ) k)
      ⟨[], 0, HeadSteps.refl _⟩ hstep G.occursRounds A
      ((Grammar.lcReach_eq_iterP G B A) ▸ (Grammar.lcReach_iff G B A).mpr hreach)
  have h4 : HeadSteps G (Sym.var B :: β) (Sym.var A :: γ ++ β) k := by
    have := HeadSteps.append_right β ht₃
    simpa using this
  exact ⟨γ ++ β, j + k, by omega, HeadSteps.trans ht h4⟩

end Witnesses

section Contradiction

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The counting contradiction.**  No reduced LL(1) grammar admits a positive-length
head-expansion trace from a variable back in front of itself.

The lookahead is made independent of the number of cycles by choosing the yield of A to
be *non-empty whenever A has one*: if A's only yield is empty then so is the cycle tail
δ, because A =>+ A δ together with A =>* [] puts δ among the yields of A. -/
theorem Grammar.noLeftRecursion_aux (hred : G.Reduced) (hall : G.Ll1)
    {A : N} (hprod : G.hasProduction A) {δ : List (Sym T N)} {j : Nat}
    (hj : 0 < j) (hcyc : HeadSteps G [Sym.var A] (Sym.var A :: δ) j) : False := by
  -- where A sits inside a sentential form
  obtain ⟨pre, post, hpre⟩ := hred.1 A hprod
  have hx₀ : G.Reachable (Sym.var A :: post) :=
    ⟨pre, by rw [← append_cons_eq]; exact hpre⟩
  -- one cycle, in an arbitrary right context
  have hcyc' (ψ : List (Sym T N)) :
      HeadSteps G (Sym.var A :: ψ) (Sym.var A :: δ ++ ψ) j :=
    HeadSteps.append_right ψ hcyc
  -- the yield of A, chosen non-empty whenever A has any non-empty yield
  obtain ⟨wA, hwA, hAw⟩ : ∃ wA, Derives G [Sym.var A] (toks wA) ∧
      (wA ≠ [] ∨ ∀ vs, Derives G [Sym.var A] (toks vs) → vs = []) := by
    by_cases h : ∃ vs, vs ≠ [] ∧ Derives G [Sym.var A] (toks vs)
    · obtain ⟨vs, hne, hder⟩ := h
      exact ⟨vs, hder, Or.inl hne⟩
    · obtain ⟨vs, hder⟩ := hred.2 A (hred.1 A hprod)
      refine ⟨vs, hder, Or.inr ?_⟩
      intro w hw
      by_cases hne : w = []
      · exact hne
      · exact absurd ⟨w, hne, hw⟩ h
  obtain ⟨tsA, hAt, hAy⟩ := derives_valid hwA
  obtain ⟨rhsA, hprA, hmA⟩ := hAt
  -- the cycle tail and the continuation both erase down to terminals
  have hRδ : G.Reachable (Sym.var A :: δ ++ post) :=
    Grammar.reachable_of_derives hx₀ (HeadSteps.derives (hcyc' post))
  obtain ⟨wδ, hwδ⟩ : ∃ wδ, Derives G δ (toks wδ) :=
    derives_toks_of_symbols δ (fun s hs =>
      Grammar.derives_toks_of_sym (hred := hred) (hR := hRδ)
        (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hs)))))
  obtain ⟨wₚ, hwₚ⟩ : ∃ wₚ, Derives G post (toks wₚ) :=
    derives_toks_of_symbols post (fun s hs =>
      Grammar.derives_toks_of_sym (hred := hred) (hR := hx₀)
        (List.mem_cons.mpr (Or.inr hs)))
  obtain ⟨tsδ, hmδ, hyδ⟩ := derives_forest hwδ
  obtain ⟨tsp, hmp, hyp⟩ := derives_forest hwₚ
  -- if A erases, so does the cycle tail
  have hwδ_nil : wA = [] → wδ = [] := fun hw => by
    have h1 : Derives G [Sym.var A] (toks wA ++ δ) :=
      derives_trans (HeadSteps.derives hcyc) (derives_ctx hwA [] δ)
    have h2 : Derives G [Sym.var A] δ := by rw [hw] at h1; simpa using h1
    have h3 : Derives G [Sym.var A] (toks wδ) := derives_trans h2 hwδ
    rcases hAw with hne | hall'
    · exact absurd hw (fun h => hne h)
    · exact hall' wδ h3
  -- the forest matching  A δ^n post
  have forest (n : Nat) : ∃ ts,
      MatchList G (Sym.var A :: listPow δ n ++ post) ts ∧
        Tree.yieldForest ts = wA ++ listPow wδ n ++ wₚ := by
    refine ⟨Tree.node A tsA :: forestPow tsδ n ++ tsp, ?_, ?_⟩
    · exact MatchList.var hprA hmA (MatchList.append (MatchList.forestPow hmδ n) hmp)
    · show Tree.yieldForest (Tree.node A tsA :: (forestPow tsδ n ++ tsp)) = _
      rw [Tree.yieldForest_cons, Tree.yieldForest_append, hAy, hyp,
        Tree.yieldForest_forestPow, hyδ]
      simp
  -- the lookahead does not depend on the number of cycles
  have hx : ∀ n, lookaheadOf (wA ++ listPow wδ n ++ wₚ) = lookaheadOf (wA ++ wₚ) := by
    intro n
    by_cases hw : wA = []
    · rw [hw, hwδ_nil hw]
      simp
    · obtain ⟨t, rest, rfl⟩ : ∃ t rest, wA = t :: rest := by
        cases wA with
        | nil => exact absurd rfl hw
        | cons t rest => exact ⟨t, rest, rfl⟩
      simp
  -- every iterated form is reachable
  have hreach : ∀ m, G.Reachable (Sym.var A :: listPow δ m ++ post) := by
    intro m
    induction m with
    | zero => exact hx₀
    | succ m ih =>
        have hcy : HeadSteps G (Sym.var A :: listPow δ m ++ post)
            (Sym.var A :: listPow δ (m + 1) ++ post) j := by
          simpa using hcyc' (listPow δ m ++ post)
        exact Grammar.reachable_of_derives ih (HeadSteps.derives hcy)
  -- the stopping lengths decrease by j per cycle
  have hbound : ∀ (n m : Nat) (ys : List (Sym T N)) (k : Nat),
      HeadSteps G (Sym.var A :: listPow δ m ++ post) ys k →
        AtLookahead (lookaheadOf (wA ++ wₚ)) ys → n * j ≤ k := by
    intro n
    induction n with
    | zero => intro m ys k _ _; omega
    | succ n ih =>
        intro m ys k htrace hla
        obtain ⟨ts₁, hm₁, hy₁⟩ := forest (m + 1)
        obtain ⟨ys₁, k₁, ht₁, ha₁⟩ := headSteps_of_match hm₁
        have hla₁ : AtLookahead (lookaheadOf (wA ++ wₚ)) ys₁ :=
          (hx (m + 1)) ▸ (hy₁ ▸ ha₁)
        have hcy : HeadSteps G (Sym.var A :: listPow δ m ++ post)
            (Sym.var A :: listPow δ (m + 1) ++ post) j := by
          simpa using hcyc' (listPow δ m ++ post)
        have hcomp : HeadSteps G (Sym.var A :: listPow δ m ++ post) ys₁ (j + k₁) :=
          HeadSteps.trans hcy ht₁
        have huni : k = j + k₁ :=
          headSteps_stop_length_unique hred hall htrace
            (lookaheadOf (wA ++ wₚ)) (hreach m) hla ys₁ (j + k₁) hcomp hla₁
        have hge : n * j ≤ k₁ := ih (m + 1) ys₁ k₁ ht₁ hla₁
        have h1 : (n + 1) * j = n * j + j := by rw [Nat.add_mul, Nat.one_mul]
        have h2 : n * j + j ≤ k₁ + j := Nat.add_le_add_right hge j
        have h3 : k₁ + j = k := by omega
        omega
  obtain ⟨ts₀, hm₀, hy₀⟩ := forest 0
  obtain ⟨ys₀, k₀, ht₀, ha₀⟩ := headSteps_of_match hm₀
  have hla₀ : AtLookahead (lookaheadOf (wA ++ wₚ)) ys₀ := by
    have hEq : lookaheadOf (Tree.yieldForest ts₀) = lookaheadOf (wA ++ wₚ) := by
      rw [hy₀, listPow_zero]
      simp
    rw [← hEq]
    exact ha₀
  have hge := hbound (k₀ + 1) 0 ys₀ k₀ ht₀ hla₀
  have h1 : k₀ + 1 ≤ (k₀ + 1) * j := by
    have hj' : 1 ≤ j := by omega
    have hmul := Nat.mul_le_mul (Nat.le_refl (k₀ + 1)) hj'
    simpa using hmul
  omega

/-- **Main theorem.**  A reduced LL(1) grammar passes the decidable left-recursion
check: no nonterminal is a left corner of a nonterminal that reaches it back. -/
theorem Grammar.noLeftRecursion_of_ll1 (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hred : G.Reduced) (hall : G.Ll1) : G.noLeftRecursion = true := by
  refine (Grammar.noLeftRecursion_iff G).mpr fun A B hcorner => ?_
  by_cases h : G.lcReach B A = true
  · exfalso
    obtain ⟨δ, j, hj, hcyc⟩ := headSteps_of_lcReach hcorner ((Grammar.lcReach_iff G B A).mp h)
    obtain ⟨α, β, hprod, _⟩ := hcorner
    exact noLeftRecursion_aux hred hall ⟨α ++ [Sym.var B] ++ β, hprod⟩ hj hcyc
  · cases h' : G.lcReach B A with
    | true => simp_all
    | false => simp_all

/-- The same statement in the form the generator consumes: a reduced grammar whose
ll1Check passes also passes noLeftRecursion. -/
theorem Grammar.noLeftRecursion_of_ll1Check (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hred : G.Reduced) (hall : G.ll1Check = true) : G.noLeftRecursion = true :=
  Grammar.noLeftRecursion_of_ll1 G hred ((Grammar.ll1Check_iff G).mp hall)

end Contradiction