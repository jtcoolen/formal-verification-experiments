/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.LeftRec

/-!
# Phase 5.5 - the classical LL(1) characterization

`Grammar.ClassicalLL1` states the textbook definition: whenever two leftmost derivations
from the start reach a common configuration `u A delta`, expand `A` by two productions
`alpha` and `beta`, and finish with terminal words whose next lookahead agrees (EOF
included), then `alpha = beta`.  It mentions no FIRST, no FOLLOW, no SELECT, no table and
no parser.  The forward direction

    G.ll1Check = true -> G.ClassicalLL1

is immediate from the bridge lemma `Grammar.select_of_derives`.  This module proves the
converse for reduced grammars:

    Grammar.ll1Check_iff_classicalLL1 : G.Reduced -> (G.ll1Check = true <-> G.ClassicalLL1)

Reduction is the hypothesis the textbook uses (Wilhelm, Seidl and Hack, *Compiler Design*,
Theorem 3.3.3) and the review shows it is needed: `S -> a; U -> a | ab` has deterministic
successful start derivations but a FIRST conflict at the unreachable `U`, and
`S -> aU | aV; U -> U; V -> V` makes the derivation condition vacuous.

## The two constructions the converse needs

* **Leftmost realization of an occurrence** (`leftDerives_of_derives_occurrence`): if
  `xs =* pre ++ var A :: post` and `pre =* toks u`, then some leftmost derivation from `xs`
  reaches `toks u ++ var A :: cont` with `cont =* post`.  The induction walks the derivation
  and lets the redex drift past the distinguished occurrence: steps to its left grow the
  terminal prefix, steps to its right are absorbed into the continuation, which is why the
  continuation is *derived* rather than equal.  Keeping `cont =* post` is what preserves a
  FOLLOW witness: `FirstList post x` pulls back to `FirstList cont x`.
  Note that the stronger statement with `cont = post` is false even for reduced grammars:
  `S -> A X`, `A -> a`, `X -> b` reaches `A b` but never leftmost.
* **Completing witnesses** (`Grammar.derives_toks_reachable`): under `Reduced` every symbol
  of a reachable form derives a terminal word, so the tails that the FIRST witnesses leave
  behind can be finished, giving terminal words whose lookahead is the one we chose.

The four SELECT combinations (FIRST/FIRST, FIRST/FOLLOW, FOLLOW/FIRST, FOLLOW/FOLLOW) are
then the same construction with the occurrence taken from FOLLOW when one side needs it.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v} {G : Grammar T N}

section Realization

/-- A derivation to a terminal word is a *leftmost* derivation. -/
theorem leftDerives_of_derives {xs : List (Sym T N)} {ws : List T}
    (h : Derives G xs (toks ws)) : LeftDerives G xs (toks ws) := by
  obtain ⟨ts, hm, hy⟩ := derives_forest h
  have h2 : LeftDerives G xs (toks (Tree.yieldForest ts)) := matchList_leftDerives hm
  rw [← hy]
  exact h2

/-- Locating a hole at the end of a concatenation: if `pre ++ var A :: post = rhs ++ q`,
the distinguished occurrence is inside `rhs` or inside `q`. -/
theorem hole_locate_nil {pre post rhs q : List (Sym T N)} {A : N}
    (h : pre ++ Sym.var A :: post = rhs ++ q) :
      (∃ r₁ r₂, rhs = r₁ ++ Sym.var A :: r₂ ∧ pre = r₁ ∧ post = r₂ ++ q) ∨
      (∃ q₁ q₂, q = q₁ ++ Sym.var A :: q₂ ∧ rhs ++ q₁ = pre ∧ post = q₂) := by
  induction rhs generalizing pre post with
  | nil => exact Or.inr ⟨pre, post, h.symm, rfl, rfl⟩
  | cons u rhs' ih =>
      cases pre with
      | nil =>
          obtain ⟨hu, hrest⟩ := List.cons.inj h
          cases hu
          exact Or.inl ⟨[], rhs', rfl, rfl, hrest⟩
      | cons t pre' =>
          obtain ⟨ht, hrest⟩ := List.cons.inj h
          cases ht
          rcases ih hrest with ⟨r₁, r₂, hr, hpre, hpost⟩ | ⟨q₁, q₂, hq, hpre, hpost⟩
          · exact Or.inl ⟨u :: r₁, r₂, congrArg (List.cons u) hr,
              congrArg (List.cons u) hpre, hpost⟩
          · exact Or.inr ⟨q₁, q₂, hq, congrArg (List.cons u) hpre, hpost⟩

/-- **Locating a hole.**  If `pre ++ var A :: post = p ++ rhs ++ q`, the distinguished
occurrence at index `pre.length` lies inside `p`, inside `rhs`, or inside `q`. -/
theorem hole_locate {pre post p q rhs : List (Sym T N)} {A : N}
    (h : pre ++ Sym.var A :: post = p ++ rhs ++ q) :
      (∃ p₂, pre ++ Sym.var A :: p₂ = p ∧ post = p₂ ++ rhs ++ q) ∨
      (∃ r₁ r₂, rhs = r₁ ++ Sym.var A :: r₂ ∧ pre = p ++ r₁ ∧ post = r₂ ++ q) ∨
      (∃ q₁ q₂, q = q₁ ++ Sym.var A :: q₂ ∧ p ++ rhs ++ q₁ = pre ∧ post = q₂) := by
  induction p generalizing pre post with
  | nil =>
      rcases hole_locate_nil h with ⟨r₁, r₂, hr, hpre, hpost⟩ | ⟨q₁, q₂, hq, hpre, hpost⟩
      · exact Or.inr (Or.inl ⟨r₁, r₂, hr, hpre, hpost⟩)
      · exact Or.inr (Or.inr ⟨q₁, q₂, hq, hpre, hpost⟩)
  | cons u p' ih =>
      cases pre with
      | nil =>
          obtain ⟨hu, hrest⟩ := List.cons.inj h
          cases hu
          exact Or.inl ⟨p', rfl, hrest⟩
      | cons t pre' =>
          obtain ⟨ht, hrest⟩ := List.cons.inj h
          cases ht
          rcases ih hrest with ⟨p₂, hp, hpost⟩ | ⟨r₁, r₂, hr, hpre, hpost⟩ |
            ⟨q₁, q₂, hq, hpre, hpost⟩
          · exact Or.inl ⟨p₂, congrArg (List.cons u) hp, hpost⟩
          · exact Or.inr (Or.inl ⟨r₁, r₂, hr, congrArg (List.cons u) hpre, hpost⟩)
          · exact Or.inr (Or.inr ⟨q₁, q₂, hq,
            congrArg (List.cons u) hpre, hpost⟩)
/-- **Leftmost realization of an occurrence.**  Under `Reduced`, if the start derives a
sentential form containing `var A`, some leftmost derivation from the start reaches a
configuration whose head is `var A`, with a terminal prefix and a continuation that still
derives the original tail.  Keeping that chain is what lets a FOLLOW witness travel.

The induction walks the derivation and asks where the distinguished occurrence sits
relative to the redex of the last step (`hole_locate`).  If the occurrence survives the
step, the induction hypothesis applies unchanged and the chain is extended by the step.
If the step *creates* the occurrence - `B -> rho₁ A rho₂` - the induction hypothesis is
applied to `B`, which is legal because the distinguished nonterminal is universally
quantified; `Reduced` makes `rho₁` productive, so a leftmost derivation of `rho₁` finishes
the terminal prefix.
-/
theorem leftDerives_head_of_derives (hred : G.Reduced) :
    ∀ (ys : List (Sym T N)), Derives G [Sym.var G.start] ys →
      ∀ (pre : List (Sym T N)) (A : N) (post : List (Sym T N)),
        ys = pre ++ Sym.var A :: post →
          ∃ (u : List T) (cont : List (Sym T N)),
            LeftDerives G [Sym.var G.start] (toks u ++ Sym.var A :: cont) ∧
              Derives G cont post := by
  intro ys h
  induction h with
  | refl =>
      intro pre A post hEq
      cases pre with
      | nil =>
          obtain ⟨hA, hpost⟩ := List.cons.inj hEq
          cases hA
          exact ⟨[], [], leftDerives_refl _, hpost ▸ derives_refl _⟩
      | cons s rest => exact absurd hEq (by simp [List.cons_append])
  | tail h' hs ih =>
      intro pre A post hEq
      obtain ⟨B, rhsB, p, q, hprod, hy', hz⟩ := derives1_decompose hs
      -- hy' : ⟨intermediate⟩ = p ++ var B :: q ;  hz : ⟨target⟩ = p ++ rhsB ++ q
      rcases hole_locate (hEq.symm.trans hz) with ⟨p₂, hp, hpost⟩ |
        ⟨r₁, r₂, hrhs, hpre, hpost⟩ | ⟨q₁, q₂, hq, hpre, hpost⟩
      · -- the occurrence lies inside the left context of the redex
          obtain ⟨u, cont, hleft, hchain⟩ :=
            ih pre A (p₂ ++ Sym.var B :: q) (by rw [hy', ← hp]; simp [List.append_assoc])
          refine ⟨u, cont, hleft, ?_⟩
          rw [hpost]
          exact derives_trans hchain
            (derives_single (Derives1.step (pre := p₂) (post := q) hprod))
      · -- the redex creates the occurrence: apply the induction hypothesis to `B`
          obtain ⟨u, contB, hleft, hchain⟩ := ih p B q (by rw [hy'])
          have hstep : LeftDerives G [Sym.var G.start]
              (toks u ++ (r₁ ++ (Sym.var A :: (r₂ ++ contB)))) := by
            have h1 := LeftDerives.tail hleft
              (DerivesLeft1.step (ws := u) (post := contB) hprod)
            rw [hrhs] at h1
            simpa [List.append_assoc] using h1
          have hR : G.Reachable (r₁ ++ (Sym.var A :: (r₂ ++ contB))) :=
            ⟨toks u, leftDerives_imp_derives hstep⟩
          obtain ⟨v, hv⟩ :=
            derives_toks_of_symbols r₁ (fun σ hσ =>
              Grammar.derives_toks_of_sym (hred := hred) hR
                (List.mem_append.mpr (Or.inl hσ)))
          have hfin : LeftDerives G (toks u ++ (r₁ ++ (Sym.var A :: (r₂ ++ contB))))
              (toks (u ++ v) ++ (Sym.var A :: (r₂ ++ contB))) := by
            have h3 : LeftDerives G (r₁ ++ (Sym.var A :: (r₂ ++ contB)))
                (toks v ++ (Sym.var A :: (r₂ ++ contB))) :=
              leftDerives_rightCtx (leftDerives_of_derives hv)
                (Sym.var A :: (r₂ ++ contB))
            have h4 := leftDerives_leftCtxToks h3 u
            simpa [toks_append] using h4
          refine ⟨u ++ v, r₂ ++ contB, leftDerives_trans hstep hfin, ?_⟩
          rw [hpost]
          exact derives_append (derives_refl _) hchain
      · -- the occurrence lies inside the right context of the redex
          obtain ⟨u, cont, hleft, hchain⟩ :=
            ih (p ++ Sym.var B :: q₁) A q₂ (by rw [hy', hq]; simp [List.append_assoc])
          refine ⟨u, cont, hleft, ?_⟩
          rw [hpost]
          exact hchain

end Realization
theorem ltok_of_not_eof {T : Type u} {x : LTok T} (h : isEof x = false) :
    ∃ t : T, x = LTok.tok t := by
  cases x with
  | tok t => exact ⟨t, rfl⟩
  | eof => exact absurd h (by simp [isEof])

section Witness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **FIRST witness.**  In a reachable configuration, a production whose right-hand side
can begin with the token `t` expands and completes to a terminal word whose lookahead is
`t`: the tail the FIRST witness leaves behind sits in a reachable form, so `Reduced` makes
it productive. -/
theorem classical_word_first (hred : G.Reduced) {A : N} {cont : List (Sym T N)}
    (hR : G.Reachable (Sym.var A :: cont)) {rhs : List (Sym T N)}
    (hp : (A, rhs) ∈ G.productions) {t : T} (hf : G.FirstList rhs (LTok.tok t)) :
    ∃ w, LeftDerives G (rhs ++ cont) (toks w) ∧ lookaheadOf w = LTok.tok t := by
  obtain ⟨ys, hder⟩ := hf
  have h1 : Derives G (rhs ++ cont) (Sym.tok t :: (ys ++ cont)) :=
    derives_append hder (derives_refl cont)
  have hstep : Derives G (Sym.var A :: cont) (rhs ++ cont) :=
    derives_single (Derives1.step (pre := []) (post := cont) hp)
  have hR2 : G.Reachable (ys ++ cont) :=
    Grammar.reachable_tail (Grammar.reachable_of_derives hR
      (derives_trans hstep h1))
  obtain ⟨v, hv⟩ := Grammar.derives_toks_of_reachable hred hR2
  have h3 : Derives G (rhs ++ cont) (Sym.tok t :: toks v) :=
    derives_trans h1 (derives_cons hv (Sym.tok t))
  exact ⟨(t :: v), leftDerives_of_derives h3, rfl⟩

/-- **Erasing witness.**  When the production erases, the lookahead comes from the
continuation itself. -/
theorem classical_word_erased (hred : G.Reduced) {A : N} {cont : List (Sym T N)}
    (hR : G.Reachable (Sym.var A :: cont)) {rhs : List (Sym T N)}
    (hp : (A, rhs) ∈ G.productions) (hr : Derives G rhs []) {x : LTok T}
    (hcont : G.FirstList cont x) :
    ∃ w, LeftDerives G (rhs ++ cont) (toks w) ∧ lookaheadOf w = x := by
  have hder : Derives G (rhs ++ cont) cont := derives_append hr (derives_refl cont)
  cases x with
  | tok t =>
      obtain ⟨ys, hder2⟩ := hcont
      have h1 : Derives G (rhs ++ cont) (Sym.tok t :: ys) :=
        derives_trans hder hder2
      have hstep : Derives G (Sym.var A :: cont) (rhs ++ cont) :=
        derives_single (Derives1.step (pre := []) (post := cont) hp)
      have hR2 : G.Reachable ys :=
        Grammar.reachable_tail (Grammar.reachable_of_derives hR
          (derives_trans hstep h1))
      obtain ⟨v, hv⟩ := Grammar.derives_toks_of_reachable hred hR2
      have h3 : Derives G (rhs ++ cont) (Sym.tok t :: toks v) :=
        derives_trans h1 (derives_cons hv (Sym.tok t))
      exact ⟨(t :: v), leftDerives_of_derives h3, rfl⟩
  | eof =>
      exact ⟨[], leftDerives_of_derives (derives_trans hder hcont), rfl⟩
end Witness

section Characterization

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The classical definition.**  One token determines the production at every reachable
leftmost configuration.  Mentions only productions, leftmost derivations and lookahead:
no FIRST, no FOLLOW, no SELECT, no table, no parser. -/
def Grammar.ClassicalLL1 (G : Grammar T N) : Prop :=
  ∀ (pre w₁ w₂ : List T) (A : N) (cont rhs₁ rhs₂ : List (Sym T N)),
    LeftDerives G [Sym.var G.start] (toks pre ++ Sym.var A :: cont) →
    (A, rhs₁) ∈ G.productions → (A, rhs₂) ∈ G.productions →
    LeftDerives G (rhs₁ ++ cont) (toks w₁) →
    LeftDerives G (rhs₂ ++ cont) (toks w₂) →
    lookaheadOf w₁ = lookaheadOf w₂ → rhs₁ = rhs₂

/-- **The forward direction needs no reduction hypothesis**: the bridge lemma
`Grammar.select_of_derives` turns the two leftmost derivations into two SELECT members
with the same lookahead. -/
theorem Grammar.classicalLL1_of_ll1 (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hall : G.Ll1) : G.ClassicalLL1 := by
  intro pre w₁ w₂ A cont rhs₁ rhs₂ hreach hp₁ hp₂ hd₁ hd₂ hlook
  have hR : G.Reachable (Sym.var A :: cont) :=
    ⟨toks pre, leftDerives_imp_derives hreach⟩
  have hs₁ := Grammar.select_of_derives hR hp₁ w₁ (leftDerives_imp_derives hd₁)
  have hs₂ := Grammar.select_of_derives hR hp₂ w₂ (leftDerives_imp_derives hd₂)
  by_cases h : rhs₁ = rhs₂
  · exact h
  · exact False.elim (hall A (lookaheadOf w₁)
      ⟨rhs₁, rhs₂, hp₁, hp₂, h, hs₁, hlook.symm ▸ hs₂⟩)

theorem Grammar.classicalLL1_of_ll1Check (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hall : G.ll1Check = true) : G.ClassicalLL1 :=
  Grammar.classicalLL1_of_ll1 G ((Grammar.ll1Check_iff G).mp hall)

/-- **The classical characterization.**  For a reduced grammar the decidable check agrees
with the textbook definition.  The reverse direction takes a conflict at `(A, x)` and
realizes an occurrence of `A` as a *leftmost* configuration; when one side of the conflict
erases, the occurrence is taken from the FOLLOW witness so that the chain of
`leftDerives_head_of_derives` transports `x ∈ FIRST(delta)` to the realized continuation.
-/
theorem Grammar.ll1Check_iff_classicalLL1 (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hred : G.Reduced) : G.ll1Check = true ↔ G.ClassicalLL1 := by
  constructor
  ·
    intro h
    exact Grammar.classicalLL1_of_ll1Check G h
  ·
    intro hclass
    apply (Grammar.ll1Check_iff G).mpr
    intro A x hconf
    obtain ⟨rhs₁, rhs₂, hp₁, hp₂, hne, s₁, s₂⟩ := hconf
    -- the shared realization step: an occurrence bundle gives the two words
    rcases s₁ with ⟨hne₁, hf₁⟩ | ⟨hr₁, hfol₁⟩
    ·
      rcases s₂ with ⟨hne₂, hf₂⟩ | ⟨hr₂, hfol₂⟩
      ·
        -- FIRST / FIRST
        obtain ⟨t₁, rfl⟩ : ∃ t₁, x = LTok.tok t₁ := ltok_of_not_eof hne₁
        obtain ⟨pre₀, post₀, hder₀₀⟩ := hred.1 A ⟨rhs₁, hp₁⟩
        have hder₀ : Derives G [Sym.var G.start] (pre₀ ++ Sym.var A :: post₀) := by simpa using hder₀₀
        obtain ⟨u, cont, hleft, _⟩ :=
          leftDerives_head_of_derives hred _ hder₀ pre₀ A post₀ rfl
        have hR : G.Reachable (Sym.var A :: cont) :=
          ⟨toks u, leftDerives_imp_derives hleft⟩
        obtain ⟨w₁, hw₁, hl₁⟩ := classical_word_first hred hR hp₁ hf₁
        obtain ⟨w₂, hw₂, hl₂⟩ := classical_word_first hred hR hp₂ hf₂
        exact hne (hclass u w₁ w₂ A cont rhs₁ rhs₂ hleft hp₁ hp₂ hw₁ hw₂
          (by rw [hl₁, hl₂]))
      ·
        -- FIRST / FOLLOW
        obtain ⟨pre₀, post₀, hder₀₀, hfirst⟩ := hfol₂
        have hder₀ : Derives G [Sym.var G.start] (pre₀ ++ Sym.var A :: post₀) := by simpa using hder₀₀
        obtain ⟨u, cont, hleft, hchain⟩ :=
          leftDerives_head_of_derives hred _ hder₀ pre₀ A post₀ rfl
        have hR : G.Reachable (Sym.var A :: cont) :=
          ⟨toks u, leftDerives_imp_derives hleft⟩
        have hcont : G.FirstList cont x :=
          Grammar.FirstList.backwards_derives x hchain hfirst
        obtain ⟨t₁, rfl⟩ : ∃ t₁, x = LTok.tok t₁ := ltok_of_not_eof hne₁
        obtain ⟨w₁, hw₁, hl₁⟩ := classical_word_first hred hR hp₁ hf₁
        obtain ⟨w₂, hw₂, hl₂⟩ := classical_word_erased hred hR hp₂ hr₂ hcont
        exact hne (hclass u w₁ w₂ A cont rhs₁ rhs₂ hleft hp₁ hp₂ hw₁ hw₂
          (by rw [hl₁, hl₂]))
    ·
      -- FOLLOW / *
      obtain ⟨pre₀, post₀, hder₀₀, hfirst⟩ := hfol₁
      have hder₀ : Derives G [Sym.var G.start] (pre₀ ++ Sym.var A :: post₀) := by simpa using hder₀₀
      obtain ⟨u, cont, hleft, hchain⟩ :=
        leftDerives_head_of_derives hred _ hder₀ pre₀ A post₀ rfl
      have hR : G.Reachable (Sym.var A :: cont) :=
        ⟨toks u, leftDerives_imp_derives hleft⟩
      have hcont : G.FirstList cont x :=
        Grammar.FirstList.backwards_derives x hchain hfirst
      obtain ⟨w₁, hw₁, hl₁⟩ := classical_word_erased hred hR hp₁ hr₁ hcont
      rcases s₂ with ⟨hne₂, hf₂⟩ | ⟨hr₂, hfol₂⟩
      ·
        obtain ⟨t₂, rfl⟩ : ∃ t₂, x = LTok.tok t₂ := ltok_of_not_eof hne₂
        obtain ⟨w₂, hw₂, hl₂⟩ := classical_word_first hred hR hp₂ hf₂
        exact hne (hclass u w₁ w₂ A cont rhs₁ rhs₂ hleft hp₁ hp₂ hw₁ hw₂
          (by rw [hl₁, hl₂]))
      ·
        obtain ⟨w₂, hw₂, hl₂⟩ := classical_word_erased hred hR hp₂ hr₂ hcont
        exact hne (hclass u w₁ w₂ A cont rhs₁ rhs₂ hleft hp₁ hp₂ hw₁ hw₂
          (by rw [hl₁, hl₂]))
end Characterization

end VerifiedLL1
