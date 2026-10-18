/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Reach
import VerifiedLL1.Memo

/-!
# Phase 4.3 — FOLLOW

## Specification

`G.FollowSym A x` says that in *some* sentential form of `G` the nonterminal `A` is
followed by a suffix that can begin with the lookahead `x`:

    exists pre post, Derives G [var G.start] (pre ++ [var A] ++ post) /\ FirstList post x

Because `FirstList` is itself stated with `Derives` (see `First.lean`), this is a purely
semantic definition: it mentions neither the fixed-point computation nor the parser.
Two consequences worth spelling out:

* `eof` is in `FOLLOW(A)` exactly when some sentential form ends with `A` followed by an
  erasable suffix — in particular `eof` is in `FOLLOW(G.start)`.
* `x` is in `FOLLOW(A)` whenever `var A :: cont` is the active suffix of a sentential
  form whose `cont` can begin with `x` (`Grammar.followSym_of_reachable`).  This is the
  form used by the generator in Phase 5.

## The rules, and why one of them needs REACH

The computation is the least fixed point over the finite carrier `N x LTok T` of:

    (R1) A = G.start, x = eof
    (R2) (B, alpha ++ [var A] ++ beta) in prods,  B occurs,  x a token in FIRST(beta)
    (R3) (B, alpha ++ [var A] ++ beta) in prods,  beta erases,  x in FOLLOW(B)

R2 needs `B` to occur: if `B` never appears in any sentential form the production
contributes no occurrence of `A` at all, and the rule would invent lookaheads (e.g.
`S -> a`, `B -> A b` would put `b` in `FOLLOW(A)` although `A` never appears).  R3 does
not need it, because `x in FOLLOW(B)` already carries a real occurrence of `B`.

R2 is also restricted to *token* lookaheads.  `eof in FIRST(beta)` means `beta` erases,
but then the suffix after `A` is `beta ++ post`, where `post` is the tail of the form
that contained `B`; that tail need not erase, so `eof` must instead travel along R3 from
`FOLLOW(B)` — which is exactly what R1 seeds with `eof in FOLLOW(G.start)`.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

/-- **Specification.** `G.FollowSym A x`: some sentential form of `G` contains `var A`
followed by a suffix that can begin with the lookahead `x`. -/
def Grammar.FollowSym (G : Grammar T N) (A : N) (x : LTok T) : Prop :=
  ∃ pre post : List (Sym T N),
    Derives G [Sym.var G.start] (pre ++ [Sym.var A] ++ post) ∧ G.FirstList post x

namespace Grammar

/-- **The form the generator uses.**  A reachable stack top `var A` with continuation
`cont` inherits every lookahead of `cont` into `FOLLOW(A)`. -/
theorem followSym_of_reachable {G : Grammar T N} {A : N} {cont : List (Sym T N)}
    (x : LTok T) (h : G.Reachable (Sym.var A :: cont)) (hf : G.FirstList cont x) :
    G.FollowSym A x := by
  obtain ⟨pre, hder⟩ := h
  refine ⟨pre, cont, ?_, hf⟩
  rw [append_cons_eq]
  exact hder

/-- The start symbol may be followed by the end of input. -/
theorem followSym_start (G : Grammar T N) : G.FollowSym G.start LTok.eof :=
  ⟨[], [], derives_refl _, derives_refl _⟩

end Grammar

section Computation

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- The contribution of one production `B -> rhs` to the pair `(A, x)`: walk along
`rhs`; at an occurrence of `var A` with suffix `ss` either `x` is a token of
`FIRST(ss)` (rule R2, available when `B` occurs), or `ss` erases and every lookahead of
`FOLLOW(B)` transfers to `A` (rule R3). -/
def followRhsTest (B A : N) (x : LTok T) (first : Sym T N → LTok T → Bool)
    (nul : Sym T N → Bool) (occ : N → Bool) (S : N × LTok T → Bool) :
    List (Sym T N) → Bool
  | [] => false
  | s :: ss =>
      (s == Sym.var A &&
        (((occ B && !isEof x) && firstListTest first nul ss x) ||
          (ss.all nul && S (B, x))))
      || followRhsTest B A x first nul occ S ss

/-- The full step: rule R1 plus one copy of R2/R3 per production. -/
def followTest (G : Grammar T N) (first : Sym T N → LTok T → Bool)
    (nul : Sym T N → Bool) (occ : N → Bool) (S : (N × LTok T) → Bool) (p : N × LTok T) :
    Bool :=
  match p with
  | (A, x) => (A == G.start && isEof x) ||
      G.productions.any fun pr => followRhsTest pr.1 A x first nul occ S pr.2

/-- The monotone transformer whose least fixed point is FOLLOW. -/
def followP (G : Grammar T N) (first : Sym T N → LTok T → Bool) (nul : Sym T N → Bool)
    (occ : N → Bool) : ((N × LTok T) → Bool) → (N × LTok T) → Bool :=
  followTest G first nul occ

theorem followRhsTest_mono (B A : N) (x : LTok T) (first : Sym T N → LTok T → Bool)
    (nul : Sym T N → Bool) (occ : N → Bool) (S S' : N × LTok T → Bool)
    (hle : ∀ p, S p = true → S' p = true) :
    ∀ (rhs : List (Sym T N)), followRhsTest B A x first nul occ S rhs = true →
      followRhsTest B A x first nul occ S' rhs = true := by
  intro rhs
  induction rhs with
  | nil => intro h; exact absurd h (by simp [followRhsTest])
  | cons s ss ih =>
      intro h
      simp only [followRhsTest] at h ⊢
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        refine Fixpoint.or_eq_true_iff.mpr
          (Or.inl (Fixpoint.and_eq_true_iff.mpr ⟨h1, ?_⟩))
        rcases Fixpoint.or_eq_true_iff.mp h2 with h2 | h2
        · exact Fixpoint.or_eq_true_iff.mpr (Or.inl h2)
        · obtain ⟨h3, h4⟩ := Fixpoint.and_eq_true_iff.mp h2
          exact Fixpoint.or_eq_true_iff.mpr
            (Or.inr (Fixpoint.and_eq_true_iff.mpr ⟨h3, hle (B, x) h4⟩))
      · exact Fixpoint.or_eq_true_iff.mpr (Or.inr (ih h))

theorem followP_mono (G : Grammar T N) (first : Sym T N → LTok T → Bool)
    (nul : Sym T N → Bool) (occ : N → Bool) : Fixpoint.PMono (followP G first nul occ) := by
  intro f g hle p h
  unfold followP followTest at h ⊢
  cases p with
  | mk A x =>
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · exact Fixpoint.or_eq_true_iff.mpr (Or.inl h)
      · obtain ⟨pr, hpr, hand⟩ := List.any_eq_true.mp h
        refine Fixpoint.or_eq_true_iff.mpr
          (Or.inr (List.any_eq_true.mpr ⟨pr, hpr, ?_⟩))
        show followRhsTest pr.1 A x first nul occ g pr.2 = true
        exact followRhsTest_mono pr.1 A x first nul occ f g hle pr.2 hand

/-- One pass per pair (nonterminal, lookahead). -/
def Grammar.followRounds (_G : Grammar T N) : Nat :=
  (FiniteEnum.elems (α := N × LTok T)).length

/-- **The computed FOLLOW relation**, using the already computed FIRST, NULLABLE and REACH
as fixed inputs.

FOLLOW is the analysis the memoized backend is worth switching to: the conflict check asks
it at (nearly) every `(nonterminal, lookahead)` pair, so the approximant is re-queried
densely, and one tabulated pass over the bit list beats re-unfolding the `iterP` chain at
every pair.  `follow_eq_iterP` says it is *the same computation* as the `iterP` chain that
the soundness and completeness proofs below reason about, so nothing is re-proved. -/
def Grammar.follow (G : Grammar T N) (A : N) (x : LTok T) : Bool :=
  Memo.iterMemo (FiniteEnum.elems (α := N × LTok T))
    (followP G G.first (firstNul G) G.occurs) (G.followRounds) (A, x)

/-- **The bridge.**  The memoized FOLLOW is the `iterP` approximant at the bound. -/
theorem Grammar.follow_eq_iterP (G : Grammar T N) (A : N) (x : LTok T) :
    G.follow A x =
      Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) (G.followRounds) (A, x) :=
  Memo.iterMemo_eq_iterP (FiniteEnum.elems (α := N × LTok T))
    (followP G G.first (firstNul G) G.occurs) FiniteEnum.complete (G.followRounds) (A, x)

/-- The two forms agree as *functions*, which is what the transformer needs. -/
theorem Grammar.follow_fun_eq (G : Grammar T N) :
    (fun p : N × LTok T => G.follow p.1 p.2) =
      Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) (G.followRounds) := by
  funext p
  cases p with
  | mk A x => exact G.follow_eq_iterP A x

/-- The limit is closed under the rules. -/
theorem follow_closed (G : Grammar T N) (A : N) (x : LTok T) :
    G.follow A x = true ↔
      followTest G G.first (firstNul G) G.occurs (fun p => G.follow p.1 p.2) (A, x) = true := by
  rw [Grammar.follow_eq_iterP, Grammar.follow_fun_eq]
  show Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) (G.followRounds) (A, x) = true ↔
      followP G G.first (firstNul G) G.occurs
        (Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) (G.followRounds)) (A, x) = true
  exact Fixpoint.iterP_closed (FiniteEnum.elems (α := N × LTok T))
    (followP G G.first (firstNul G) G.occurs) (followP_mono G _ _ _) FiniteEnum.complete (A, x)

/-- **Termination.**  One more pass beyond the bound adds nothing. -/
theorem follow_stable (G : Grammar T N) (A : N) (x : LTok T) :
    Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) (G.followRounds + 1) (A, x) =
      Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) G.followRounds (A, x) :=
  Fixpoint.iterP_stable (FiniteEnum.elems (α := N × LTok T))
    (followP G G.first (firstNul G) G.occurs) (followP_mono G _ _ _) FiniteEnum.complete (A, x)

/-- Rule R1. -/
theorem follow_start (G : Grammar T N) : G.follow G.start LTok.eof = true := by
  rw [follow_closed G G.start LTok.eof]
  simp only [followTest]
  exact Fixpoint.or_eq_true_iff.mpr
    (Or.inl (Fixpoint.and_eq_true_iff.mpr ⟨by simp, by simp [isEof]⟩))

/-- At an explicit occurrence `alpha₁ ++ [var A] ++ alpha₂` the production rule fires. -/
theorem followRhsTest_at (B A : N) (x : LTok T) (first : Sym T N → LTok T → Bool)
    (nul : Sym T N → Bool) (occ : N → Bool) (S : N × LTok T → Bool) (α₂ : List (Sym T N))
    (h : (((occ B && !isEof x) && firstListTest first nul α₂ x) ||
          (α₂.all nul && S (B, x))) = true) :
    ∀ (α₁ : List (Sym T N)),
      followRhsTest B A x first nul occ S (α₁ ++ [Sym.var A] ++ α₂) = true := by
  intro α₁
  induction α₁ with
  | nil =>
      have key : (([] : List (Sym T N)) ++ [Sym.var A] ++ α₂) = Sym.var A :: α₂ := rfl
      rw [key]
      simp only [followRhsTest]
      exact Fixpoint.or_eq_true_iff.mpr
        (Or.inl (Fixpoint.and_eq_true_iff.mpr ⟨by simp, h⟩))
  | cons s ss ih =>
      simp only [List.cons_append, followRhsTest]
      exact Fixpoint.or_eq_true_iff.mpr (Or.inr ih)

/-- Rule R2: a token of the FIRST of a suffix belongs to the FOLLOW of the nonterminal
in front of it, provided the left-hand side of the production occurs. -/
theorem follow_of_first (G : Grammar T N) {B A : N} {α₁ α₂ : List (Sym T N)} (t : T)
    (hprod : (B, α₁ ++ [Sym.var A] ++ α₂) ∈ G.productions) (hocc : G.occurs B = true)
    (hfirst : firstListTest G.first (firstNul G) α₂ (LTok.tok t) = true) :
    G.follow A (LTok.tok t) = true := by
  rw [follow_closed G A (LTok.tok t)]
  simp only [followTest]
  refine Fixpoint.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr
    ⟨(B, α₁ ++ [Sym.var A] ++ α₂), hprod, ?body⟩))
  show followRhsTest B A (LTok.tok t) G.first (firstNul G) G.occurs
    (fun p => G.follow p.1 p.2) (α₁ ++ [Sym.var A] ++ α₂) = true
  refine followRhsTest_at B A (LTok.tok t) G.first (firstNul G) G.occurs
    (fun p => G.follow p.1 p.2) α₂ ?_ α₁
  exact Fixpoint.or_eq_true_iff.mpr (Or.inl
    (Fixpoint.and_eq_true_iff.mpr ⟨Fixpoint.and_eq_true_iff.mpr ⟨hocc, by simp [isEof]⟩,
      hfirst⟩))

/-- Rule R3: if the suffix erases, the FOLLOW of the left-hand side transfers. -/
theorem follow_of_trans (G : Grammar T N) {B A : N} {α₁ α₂ : List (Sym T N)} (x : LTok T)
    (hprod : (B, α₁ ++ [Sym.var A] ++ α₂) ∈ G.productions)
    (hnull : α₂.all (firstNul G) = true) (hS : G.follow B x = true) :
    G.follow A x = true := by
  rw [follow_closed G A x]
  simp only [followTest]
  refine Fixpoint.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr
    ⟨(B, α₁ ++ [Sym.var A] ++ α₂), hprod, ?body⟩))
  show followRhsTest B A x G.first (firstNul G) G.occurs
    (fun p => G.follow p.1 p.2) (α₁ ++ [Sym.var A] ++ α₂) = true
  refine followRhsTest_at B A x G.first (firstNul G) G.occurs
    (fun p => G.follow p.1 p.2) α₂ ?_ α₁
  exact Fixpoint.or_eq_true_iff.mpr (Or.inr
    (Fixpoint.and_eq_true_iff.mpr ⟨hnull, hS⟩))

end Computation

section Soundness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- Reading the production rule backwards: a successful test exhibits the occurrence and
which of R2/R3 fired. -/
theorem followRhsTest_imp (B A : N) (x : LTok T) (first : Sym T N → LTok T → Bool)
    (nul : Sym T N → Bool) (occ : N → Bool) (S : N × LTok T → Bool) :
    ∀ (rhs : List (Sym T N)), followRhsTest B A x first nul occ S rhs = true →
      ∃ α₁ α₂, rhs = α₁ ++ [Sym.var A] ++ α₂ ∧
        ((occ B = true ∧ isEof x = false ∧ firstListTest first nul α₂ x = true) ∨
          (α₂.all nul = true ∧ S (B, x) = true)) := by
  intro rhs
  induction rhs with
  | nil => intro h; exact absurd h (by simp [followRhsTest])
  | cons s ss ih =>
      intro h
      simp only [followRhsTest] at h
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        have hs : s = Sym.var A := eq_of_beq h1
        refine ⟨[], ss, by rw [hs]; rfl, ?_⟩
        rcases Fixpoint.or_eq_true_iff.mp h2 with h | h
        · obtain ⟨hne, hf⟩ := Fixpoint.and_eq_true_iff.mp h
          obtain ⟨hocc, hne'⟩ := Fixpoint.and_eq_true_iff.mp hne
          exact Or.inl ⟨hocc, by simpa using hne', hf⟩
        · exact Or.inr (Fixpoint.and_eq_true_iff.mp h)
      · obtain ⟨α₁, α₂, hsplit, hcase⟩ := ih h
        exact ⟨s :: α₁, α₂, by rw [hsplit]; rfl, hcase⟩

/-- **Soundness of the computation.**  Every lookahead the iteration assigns to `A` is a
genuine `FOLLOW` lookahead of `A` in the grammar. -/
theorem follow_sound (G : Grammar T N) : ∀ (k : Nat) (A : N) (x : LTok T),
    Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) k (A, x) = true →
      G.FollowSym A x := by
  intro k
  induction k with
  | zero => intro A x h; exact absurd h (by simp [Fixpoint.iterP])
  | succ k ih =>
      intro A x h
      rw [Fixpoint.iterP_succ] at h
      unfold followP followTest at h
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · -- rule R1
        obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        have hA : A = G.start := eq_of_beq h1
        have hx : x = LTok.eof := isEof_eq_true_iff.mp h2
        subst hA
        subst hx
        exact ⟨[], [], derives_refl _, derives_refl _⟩
      · obtain ⟨pr, hpr, hand⟩ := List.any_eq_true.mp h
        obtain ⟨α₁, α₂, hsplit, hcase⟩ :
            ∃ α₁ α₂, pr.2 = α₁ ++ [Sym.var A] ++ α₂ ∧
              ((G.occurs pr.1 = true ∧ isEof x = false ∧
                  firstListTest G.first (firstNul G) α₂ x = true) ∨
                (α₂.all (firstNul G) = true ∧
                  Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) k (pr.1, x) = true)) := by
          exact followRhsTest_imp pr.1 A x G.first (firstNul G) G.occurs
            (Fixpoint.iterP (followP G G.first (firstNul G) G.occurs) k) pr.2 hand
        have hprod : (pr.1, α₁ ++ [Sym.var A] ++ α₂) ∈ G.productions := hsplit ▸ hpr
        rcases hcase with ⟨hocc, hne, hfirst⟩ | ⟨hnull, hS⟩
        · -- rule R2: a token of FIRST(α₂)
          obtain ⟨t, rfl⟩ : ∃ t : T, x = LTok.tok t := by
            cases x with
            | tok t => exact ⟨t, rfl⟩
            | eof => exact absurd hne (by simp [isEof])
          obtain ⟨pre, post, hform⟩ := (occurs_iff G pr.1).mp hocc
          have hfspec : G.FirstList α₂ (LTok.tok t) :=
            (firstList_iff G α₂ (LTok.tok t)).mpr hfirst
          have hstep : Derives G [Sym.var pr.1] (α₁ ++ [Sym.var A] ++ α₂) :=
            hsplit ▸ derives_production pr.1 pr.2 hpr
          have hmid : Derives G (pre ++ [Sym.var pr.1] ++ post)
              (pre ++ (α₁ ++ [Sym.var A] ++ α₂) ++ post) := derives_ctx hstep pre post
          have htrans := derives_trans hform hmid
          refine ⟨pre ++ α₁, α₂ ++ post, ?_,
            Grammar.FirstList.spec_prepend α₂ post t hfspec⟩
          simp only [List.append_assoc] at htrans ⊢
          exact htrans
        · -- rule R3: transfer from FOLLOW(B)
          obtain ⟨pre, post, hform, hFirst⟩ := ih pr.1 x hS
          have hder : Derives G α₂ [] :=
            derives_nil_of_symbols α₂ (fun s hs =>
              (symNull_iff G s).mp ((List.all_eq_true.mp hnull) s hs))
          have hstep : Derives G [Sym.var pr.1] (α₁ ++ [Sym.var A] ++ α₂) :=
            hsplit ▸ derives_production pr.1 pr.2 hpr
          have hmid : Derives G (pre ++ [Sym.var pr.1] ++ post)
              (pre ++ (α₁ ++ [Sym.var A] ++ α₂) ++ post) := derives_ctx hstep pre post
          have htrans := derives_trans hform hmid
          refine ⟨pre ++ α₁, α₂ ++ post, ?_,
            Grammar.FirstList.append_left_of_null α₂ post x hder hFirst⟩
          simp only [List.append_assoc] at htrans ⊢
          exact htrans

end Soundness

section Completeness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **Completeness of the computation.**  Every genuine `FOLLOW` lookahead is found by
the iteration.  The proof is an induction on the derivation of the sentential form with
the marked occurrence of `A` carried along: wherever the marked occurrence sits, one of
the three rules accounts for it. -/
theorem follow_complete (G : Grammar T N) (A : N) (x : LTok T) (h : G.FollowSym A x) :
    G.follow A x = true := by
  obtain ⟨pre₀, post₀, hform₀, hfirst₀⟩ := h
  have key : ∀ (mid : List (Sym T N)), Derives G [Sym.var G.start] mid →
      ∀ (C : N) (pre post : List (Sym T N)), mid = pre ++ [Sym.var C] ++ post →
        G.FirstList post x → G.follow C x = true := by
    intro mid hmid
    induction hmid with
    | refl =>
        intro C pre post hmid hfirst
        cases pre with
        | nil =>
            rw [List.nil_append] at hmid
            obtain ⟨hA, hpost⟩ := List.cons.inj hmid
            have hCA : G.start = C := by cases hA; rfl
            subst hpost
            subst hCA
            cases x with
            | tok t =>
                obtain ⟨ys, hder⟩ := hfirst
                have hnil := derives_nil_imp_nil _ hder
                cases hnil
            | eof => exact follow_start G
        | cons p ps =>
            rw [List.cons_append] at hmid
            obtain ⟨_, hrest⟩ := List.cons.inj hmid
            cases ps with
            | nil => cases hrest
            | cons b bs => cases hrest
    | @tail mid' fin hrec hstep ih =>
        intro C pre post hmid hfirst
        obtain ⟨B, rhs, ctxL, ctxR, hp, emid', efin⟩ := derives1_decompose hstep
        rw [efin] at hmid
        rw [List.append_assoc] at hmid
        rcases occurrence_append (Sym.var C) ctxL (rhs ++ ctxR) pre post hmid.symm with
            ⟨l₁, l₂, hctxL, heq_pre, heq_post⟩ | ⟨r₁, r₂, hr, heq_pre, heq_post⟩
        · -- the marked occurrence is in the left context of the rewritten variable
          have hpost' : G.FirstList ((l₂ ++ rhs) ++ ctxR) x := by
            rw [List.append_assoc]
            exact heq_post ▸ hfirst
          have hstepd : Derives G (l₂ ++ Sym.var B :: ctxR) (l₂ ++ rhs ++ ctxR) :=
            derives_single (Derives1.step (pre := l₂) (post := ctxR) hp)
          refine ih C l₁ (l₂ ++ Sym.var B :: ctxR) ?_ (Grammar.FirstList.backwards_derives
            x hstepd hpost')
          rw [emid', hctxL]
          rw [List.append_assoc]
        · -- the marked occurrence is inside `rhs ++ ctxR`
          have heq : r₁ ++ [Sym.var C] ++ r₂ = rhs ++ ctxR := hr.symm
          rcases occurrence_append (Sym.var C) rhs ctxR r₁ r₂ heq with
              ⟨m₁, m₂, hrhs, heq₁, heq₂⟩ | ⟨c₁, c₂, hctxR, heq₁, heq₂⟩
          · -- it comes from the right-hand side of the production that was just used
            have hpost : G.FirstList (m₂ ++ ctxR) x := heq₂ ▸ (heq_post ▸ hfirst)
            have hmidB : mid' = ctxL ++ [Sym.var B] ++ ctxR :=
              (append_cons_eq ctxL (Sym.var B) ctxR).symm ▸ emid'
            have hprod' : (B, m₁ ++ [Sym.var C] ++ m₂) ∈ G.productions := hrhs ▸ hp
            rcases x with t | rfl
            · -- a token lookahead: either it comes from FIRST(m₂) (rule R2), or m₂
              -- erases and it comes from ctxR (rule R3)
              rcases Grammar.FirstList.append_decomp m₂ ctxR (LTok.tok t) hpost with hf | hn
              · exact follow_of_first G (t := t) hprod'
                  (occurs_complete G B ⟨ctxL, ctxR, hmidB ▸ hrec⟩)
                  ((firstList_iff G m₂ (LTok.tok t)).mp hf)
              · obtain ⟨hm₂, hctx⟩ := hn
                have hall : m₂.all (firstNul G) = true :=
                  List.all_eq_true.mpr
                    (fun s hs => nullable_backward G m₂ [] hm₂ (by simp) s hs)
                exact follow_of_trans G (x := LTok.tok t) hprod' hall
                  (ih B ctxL ctxR hmidB hctx)
            · -- `eof`: both halves erase, so rule R3 transfers from FOLLOW(B)
              obtain ⟨hm₂, hctx⟩ := derives_nil_append m₂ ctxR hpost
              have hall : m₂.all (firstNul G) = true :=
                List.all_eq_true.mpr
                  (fun s hs => nullable_backward G m₂ [] hm₂ (by simp) s hs)
              exact follow_of_trans G (x := LTok.eof) hprod' hall
                (ih B ctxL ctxR hmidB hctx)
          · -- the marked occurrence is in the right context of the rewritten variable
            refine ih C (ctxL ++ [Sym.var B] ++ c₁) c₂ ?_ (heq₂ ▸ (heq_post ▸ hfirst))
            rw [emid', hctxR]
            simp
  exact key _ hform₀ A pre₀ post₀ rfl hfirst₀

end Completeness

section Characterisation

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The characterisation.**  The computation decides FOLLOW. -/
theorem follow_iff (G : Grammar T N) (A : N) (x : LTok T) :
    G.follow A x = true ↔ G.FollowSym A x :=
  ⟨fun h => follow_sound G G.followRounds A x ((Grammar.follow_eq_iterP G A x) ▸ h),
    fun h => follow_complete G A x h⟩

/-- **Correct end-of-input behaviour.**  `eof` is in `FOLLOW(A)` exactly when some
sentential form has `A` followed by a suffix that erases. -/
theorem follow_eof_iff (G : Grammar T N) (A : N) :
    G.follow A LTok.eof = true ↔
      ∃ pre post : List (Sym T N),
        Derives G [Sym.var G.start] (pre ++ [Sym.var A] ++ post) ∧ Derives G post [] := by
  rw [follow_iff]
  constructor
  · rintro ⟨pre, post, h1, h2⟩
    exact ⟨pre, post, h1, h2⟩
  · rintro ⟨pre, post, h1, h2⟩
    exact ⟨pre, post, h1, h2⟩

/-- The computed `FOLLOW` of the start symbol contains `eof`. -/
theorem follow_start_eof (G : Grammar T N) : G.follow G.start LTok.eof = true :=
  follow_start G

end Characterisation

end VerifiedLL1
