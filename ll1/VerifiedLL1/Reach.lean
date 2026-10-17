/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.First

/-!
# Phase 4.3a — REACH: which nonterminals occur in a sentential form

## Specification

`G.Occurs A` says that `A` occurs *somewhere* in a sentential form of `G`:

    exists pre post, Derives G [var G.start] (pre ++ [var A] ++ post)

This is deliberately different from `G.Reachable [var A]`, which asks for `A` to occur
at the *end* of a form: a form `alpha A beta` whose tail `beta` cannot be erased
witnesses `Occurs A` but not `Reachable [var A]`.

## Why FOLLOW needs it

The textbook rule "if `B -> alpha A beta` and `t` is in `FIRST(beta)` then `t` is in
`FOLLOW(A)`" is sound only when `B` occurs somewhere: for an unreachable `B` the
production contributes no sentential form at all, so the rule would invent a lookahead.
`Follow.lean` uses `G.occurs B` as a side condition of that rule, which costs nothing
because the computation here is proved both sound and complete.

## Computation

Least fixed point over the finite carrier `N` of the two rules

    A = G.start
    B occurs, var A on the right-hand side of (B, rhs), (B, rhs) in prods  =>  A occurs

Termination is the generic pigeonhole argument of `Fixpoint.iterP`.
-/

set_option linter.unusedSectionVars false

universe u v w

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

section ListLemmas

variable {α : Type w}

/-- Nothing can be derived from the empty sentential form except the empty form. -/
theorem derives_nil_imp_nil {G : Grammar T N} : ∀ (ys : List (Sym T N)),
    Derives G ([] : List (Sym T N)) ys → ys = [] := by
  intro ys h
  induction h with
  | refl => rfl
  | @tail mid fin hrec hstep ih =>
      have hmid : mid = [] := ih
      subst hmid
      obtain ⟨B, rhs, pre, post, hp, h1, h2⟩ := derives1_decompose hstep
      cases pre with
      | nil => cases h1
      | cons a as => cases h1

/-- A list containing `a` can be split around an occurrence of `a`. -/
theorem exists_split_of_mem (a : α) : ∀ (l : List α), a ∈ l →
    ∃ l₁ l₂, l = l₁ ++ [a] ++ l₂ := by
  intro l h
  induction l with
  | nil => cases h
  | cons s ss ih =>
      rcases List.mem_cons.mp h with heq | hmem
      · exact ⟨[], ss, heq ▸ rfl⟩
      · obtain ⟨l₁, l₂, hl⟩ := ih hmem
        exact ⟨s :: l₁, l₂, by rw [hl]; rfl⟩

/-- The boolean counterpart, for a `==`-test. -/
theorem exists_split_of_any (a : α) [BEq α] [LawfulBEq α] : ∀ (l : List α),
    (l.any fun s => s == a) = true → ∃ l₁ l₂, l = l₁ ++ [a] ++ l₂ := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons s ss ih =>
      intro h
      rw [List.any_cons] at h
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · have hs : s = a := eq_of_beq h
        exact ⟨[], ss, hs ▸ rfl⟩
      · obtain ⟨l₁, l₂, hl⟩ := ih h
        exact ⟨s :: l₁, l₂, by rw [hl]; rfl⟩

/-- Membership implies the corresponding `any`-test succeeds. -/
theorem any_eq_true_of_mem (a : α) [BEq α] [LawfulBEq α] : ∀ (l : List α),
    a ∈ l → (l.any fun s => s == a) = true := by
  intro l h
  induction l with
  | nil => cases h
  | cons s ss ih =>
      rw [List.any_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · exact Fixpoint.or_eq_true_iff.mpr (Or.inl (heq ▸ by simp))
      · exact Fixpoint.or_eq_true_iff.mpr (Or.inr (ih hmem))

/-- **Where does a marked occurrence sit?**  If `pre ++ [a] ++ post = l ++ r`, the
occurrence of `a` sits either inside `l` or inside `r`. -/
theorem occurrence_append (a : α) : ∀ (l r pre post : List α),
    pre ++ [a] ++ post = l ++ r →
      (∃ l₁ l₂, l = l₁ ++ [a] ++ l₂ ∧ pre = l₁ ∧ post = l₂ ++ r) ∨
      (∃ r₁ r₂, r = r₁ ++ [a] ++ r₂ ∧ pre = l ++ r₁ ∧ post = r₂) := by
  intro l
  induction l with
  | nil =>
      intro r pre post h
      right
      refine ⟨pre, post, ?_, ?_, ?_⟩
      · exact h.symm
      · rfl
      · rfl
  | cons s l' ih =>
      intro r pre post h
      cases pre with
      | nil =>
          obtain ⟨hs, hrest⟩ := List.cons.inj h
          refine Or.inl ⟨[], l', ?_, rfl, hrest⟩
          rw [hs]
          rfl
      | cons p pre' =>
          simp only [List.cons_append] at h
          obtain ⟨hp, hrest⟩ := List.cons.inj h
          rcases ih r pre' post hrest with ⟨l₁, l₂, hl₁, heq, hpost⟩ | ⟨r₁, r₂, hr₁, heq', hpost⟩
          · refine Or.inl ⟨s :: l₁, l₂, ?_, ?_, hpost⟩
            · rw [hl₁]
              rfl
            · rw [heq, hp]
          · refine Or.inr ⟨r₁, r₂, hr₁, ?_, hpost⟩
            · rw [heq', hp]
              rfl

/-- Bracketing a one-element middle list is the same as a cons. -/
theorem append_cons_eq {α : Type w} (xs : List α) (a : α) (ys : List α) :
    xs ++ [a] ++ ys = xs ++ a :: ys := by
  induction xs with
  | nil => rfl
  | cons x xrest ih => simp only [List.cons_append, ih]

end ListLemmas

/-- **Specification.** `G.Occurs A`: the nonterminal `A` occurs in some sentential form
of `G`. -/
def Grammar.Occurs (G : Grammar T N) (A : N) : Prop :=
  ∃ pre post : List (Sym T N),
    Derives G [Sym.var G.start] (pre ++ [Sym.var A] ++ post)

namespace Grammar

/-- An occurrence at the end of a form is an occurrence. -/
theorem occurs_of_reachable_var {G : Grammar T N} {A : N}
    (h : G.Reachable [Sym.var A]) : G.Occurs A := by
  obtain ⟨pre, hder⟩ := h
  exact ⟨pre, [], by simpa using hder⟩

end Grammar

section Computation

variable [DecidableEq T] [DecidableEq N]

/-- The monotone transformer computing occurring nonterminals. -/
def occursTest (G : Grammar T N) (S : N → Bool) (A : N) : Bool :=
  A == G.start || G.productions.any fun pr =>
    S pr.1 && pr.2.any (fun s => s == Sym.var A)

def occursP (G : Grammar T N) : (N → Bool) → N → Bool := occursTest G

theorem occursP_mono (G : Grammar T N) : Fixpoint.PMono (occursP G) := by
  intro f g hle A h
  unfold occursP occursTest at h ⊢
  rcases Fixpoint.or_eq_true_iff.mp h with h | h
  · exact Fixpoint.or_eq_true_iff.mpr (Or.inl h)
  · obtain ⟨pr, hpr, hand⟩ := List.any_eq_true.mp h
    obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
    refine Fixpoint.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨pr, hpr, ?_⟩))
    show (g pr.1 && pr.2.any (fun s => s == Sym.var A)) = true
    exact Fixpoint.and_eq_true_iff.mpr ⟨hle pr.1 h1, h2⟩

/-- One pass per nonterminal. -/
def Grammar.occursRounds (_G : Grammar T N) [FiniteEnum N] : Nat :=
  (FiniteEnum.elems (α := N)).length

/-- The computed occurrence predicate. -/
def Grammar.occurs (G : Grammar T N) [FiniteEnum N] (A : N) : Bool :=
  Fixpoint.iterP (occursP G) (G.occursRounds) A

theorem occurs_closed [FiniteEnum N] (G : Grammar T N) (A : N) :
    G.occurs A = true ↔ occursTest G (G.occurs) A = true := by
  show Fixpoint.iterP (occursP G) (G.occursRounds) A = true ↔
      occursP G (Fixpoint.iterP (occursP G) (G.occursRounds)) A = true
  exact Fixpoint.iterP_closed (FiniteEnum.elems (α := N)) (occursP G)
    (occursP_mono G) FiniteEnum.complete A

end Computation

section Soundness

variable [DecidableEq T] [DecidableEq N]

/-- **Soundness.**  Whatever the iteration produces is a genuine occurrence. -/
theorem occurs_sound [LawfulBEq N] (G : Grammar T N) : ∀ (k : Nat) (A : N),
    Fixpoint.iterP (occursP G) k A = true → G.Occurs A := by
  intro k
  induction k with
  | zero => intro A h; exact absurd h (by simp [Fixpoint.iterP])
  | succ k ih =>
      intro A h
      rw [Fixpoint.iterP_succ] at h
      unfold occursP occursTest at h
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · have hA : A = G.start := eq_of_beq h
        subst hA
        exact ⟨[], [], derives_refl _⟩
      · obtain ⟨pr, hpr, hand⟩ := List.any_eq_true.mp h
        obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
        obtain ⟨pre, post, hform⟩ := ih pr.1 h1
        obtain ⟨α₁, α₂, hsplit⟩ := exists_split_of_any (Sym.var A) pr.2 h2
        refine ⟨pre ++ α₁, α₂ ++ post, ?_⟩
        have hstep : Derives G [Sym.var pr.1] (α₁ ++ [Sym.var A] ++ α₂) := hsplit ▸
          derives_production pr.1 pr.2 hpr
        have hmid : Derives G (pre ++ [Sym.var pr.1] ++ post)
            (pre ++ (α₁ ++ [Sym.var A] ++ α₂) ++ post) := derives_ctx hstep pre post
        have htrans : Derives G [Sym.var G.start]
            (pre ++ (α₁ ++ [Sym.var A] ++ α₂) ++ post) := derives_trans hform hmid
        simp only [List.append_assoc] at htrans ⊢
        exact htrans

end Soundness

section Completeness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum N]

/-- **Completeness.**  Every nonterminal occurring in a sentential form is found. -/
theorem occurs_complete [LawfulBEq N] (G : Grammar T N) (A : N)
    (h : G.Occurs A) : G.occurs A = true := by
  obtain ⟨pre₀, post₀, hform₀⟩ := h
  -- The statement is proved for *every* marked occurrence, because the induction has to
  -- reason about other nonterminals appearing in the same form.
  have key : ∀ (mid : List (Sym T N)), Derives G [Sym.var G.start] mid →
      ∀ (C : N) (pre post : List (Sym T N)), mid = pre ++ [Sym.var C] ++ post →
        G.occurs C = true := by
    intro mid hmid
    induction hmid with
    | refl =>
        intro C pre post hmid
        cases pre with
        | nil =>
            rw [List.nil_append] at hmid
            obtain ⟨hA, hpost⟩ := List.cons.inj hmid
            have hCA : G.start = C := by cases hA; rfl
            subst hpost
            rw [← hCA]
            rw [occurs_closed G G.start]
            simp [occursTest]
        | cons p ps =>
            rw [List.cons_append] at hmid
            obtain ⟨_, hrest⟩ := List.cons.inj hmid
            cases ps with
            | nil => cases hrest
            | cons b bs => cases hrest
    | @tail mid' fin hrec hstep ih =>
        intro C pre post hmid
        obtain ⟨B, rhs, ctxL, ctxR, hp, emid', efin⟩ := derives1_decompose hstep
        rw [efin] at hmid
        rw [List.append_assoc] at hmid
        rcases occurrence_append (Sym.var C) ctxL (rhs ++ ctxR) pre post hmid.symm with
            ⟨l₁, l₂, hctxL, heq_pre, heq_post⟩ | ⟨r₁, r₂, hr, heq_pre, heq_post⟩
        · -- the occurrence is in the left context of the rewritten variable
          refine ih C l₁ (l₂ ++ [Sym.var B] ++ ctxR) ?_
          rw [emid', hctxL]
          simp
        · -- the occurrence is in `rhs ++ ctxR`: split again
          have heq : r₁ ++ [Sym.var C] ++ r₂ = rhs ++ ctxR := hr.symm
          rcases occurrence_append (Sym.var C) rhs ctxR r₁ r₂ heq with
              ⟨m₁, m₂, hrhs, heq₁, heq₂⟩ | ⟨c₁, c₂, hctxR, heq₁, heq₂⟩
          · -- the occurrence comes from the production that was just used
            rw [occurs_closed G C]
            simp only [occursTest]
            refine Fixpoint.or_eq_true_iff.mpr
              (Or.inr (List.any_eq_true.mpr ⟨(B, rhs), hp, Fixpoint.and_eq_true_iff.mpr
                ⟨ih B ctxL ctxR ((append_cons_eq ctxL (Sym.var B) ctxR).symm ▸ emid'),
                  any_eq_true_of_mem (Sym.var C) rhs ?_⟩⟩))
            rw [hrhs]
            simp [List.mem_append]
          · -- the occurrence is in the right context of the rewritten variable
            refine ih C (ctxL ++ [Sym.var B] ++ c₁) c₂ ?_
            rw [emid', hctxR]
            simp
  exact key _ hform₀ A pre₀ post₀ rfl

end Completeness

/-- **A syntactic rejection test.**  If `B` is not the start symbol and no right-hand
side of `G` mentions `B`, then `B` occurs in no sentential form: no derivation step can
introduce it.  This is the cheap way to prove that a nonterminal is unreachable. -/
theorem not_occurs_of_absent [DecidableEq T] [DecidableEq N] (G : Grammar T N) (B : N)
    (hne : B ≠ G.start) (habs : ∀ pr ∈ G.productions, Sym.var B ∉ pr.2) :
    ¬ G.Occurs B := by
  intro h
  obtain ⟨pre, post, hder⟩ := h
  have key : ∀ (mid : List (Sym T N)), Derives G [Sym.var G.start] mid →
      ∀ s ∈ mid, s ≠ Sym.var B := by
    intro mid hmid
    induction hmid with
    | refl =>
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact fun hb => hne (Sym.var.inj hb).symm
    | @tail mid' fin hrec hstep ih =>
        obtain ⟨C, rhs, ctxL, ctxR, hp, emid', efin⟩ := derives1_decompose hstep
        intro s hs
        rw [efin] at hs
        rcases List.mem_append.mp hs with hmid | hright
        · rcases List.mem_append.mp hmid with hleft | hrhs
          · refine ih s ?_
            rw [emid']
            exact List.mem_append.mpr (Or.inl hleft)
          · intro hb
            exact habs (C, rhs) hp (hb ▸ hrhs)
        · refine ih s ?_
          rw [emid']
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hright)))
  have hmem : Sym.var B ∈ pre ++ [Sym.var B] ++ post := by simp [List.mem_append]
  exact key _ hder (Sym.var B) hmem rfl

/-- **The characterisation.**  The computation decides occurrence. -/
theorem occurs_iff [DecidableEq T] [DecidableEq N] [FiniteEnum N] (G : Grammar T N) (A : N) :
    G.occurs A = true ↔ G.Occurs A :=
  ⟨fun h => occurs_sound G (G.occursRounds) A h, fun h => occurs_complete G A h⟩

/-- **Termination.**  The iteration is stable at the bound: one more pass adds nothing. -/
theorem occurs_stable [DecidableEq T] [DecidableEq N] [FiniteEnum N] (G : Grammar T N) (A : N) :
    Fixpoint.iterP (occursP G) (G.occursRounds + 1) A =
      Fixpoint.iterP (occursP G) G.occursRounds A :=
  Fixpoint.iterP_stable (FiniteEnum.elems (α := N)) (occursP G)
    (occursP_mono G) FiniteEnum.complete A

end VerifiedLL1
