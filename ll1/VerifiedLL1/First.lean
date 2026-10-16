/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Nullable
import VerifiedLL1.Table

/-!
# Phase 4.2 — FIRST

## Specification

`G.FirstList xs x` says the symbol list `xs` can *begin* with the lookahead `x`:

* for a token `x = tok t`: `∃ ys, Derives G xs (Sym.tok t :: ys)` — `xs` derives a
  sequence whose first symbol is that token (the rest is an arbitrary sentential form,
  the classical `FIRST_1`; it makes the rules sound without assuming the trailing
  symbols generate anything);
* for `x = eof`: `Derives G xs []` — `xs` derives the empty sequence.

Encoding `eof` as "derives nothing" is what gives the correct ε-behaviour for free:
`G.FirstSym s eof ↔ s` is nullable, and `eof` is in the FIRST of a list exactly when all
of its symbols are nullable.

## Computation

`firstListTest S nul rhs x` implements the list rule: look at the head symbol; if it is
nullable the search continues into the tail (and `eof` can only be reached that way),
otherwise the head decides.  `firstTest G nul` implements the symbol rules: a terminal
`t` has lookahead `t`; a nonterminal `A` inherits the FIRST of the right-hand side of
any of its productions.  `NULLABLE` is an input, taken from Phase 4.1.

## Results

`first_sound` (computed ⇒ specification), `first_complete` (specification ⇒ computed),
`first_iff`, `first_eof_iff_nullable` (the ε/eof characterisation), `firstList_iff`.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

section
variable [FiniteEnum T]
/-- Lookaheads are finite: the tokens plus `eof`. -/
instance (priority := 100) LTok.finiteEnum : FiniteEnum (LTok T) where
  elems := (FiniteEnum.elems (α := T)).map LTok.tok ++ [LTok.eof]
  complete := by
    intro x
    cases x with
    | tok t =>
        refine List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, FiniteEnum.complete t, rfl⟩))
    | eof => exact List.mem_append.mpr (Or.inr (List.Mem.head _))
end

instance (priority := 100) Prod.finiteEnum [FiniteEnum α] [FiniteEnum β] :
    FiniteEnum (α × β) where
  elems := (FiniteEnum.elems (α := α)).flatMap fun a =>
    (FiniteEnum.elems (α := β)).map fun b => (a, b)
  complete := by
    intro p
    obtain ⟨a, b⟩ := p
    refine List.mem_flatMap.mpr ⟨a, FiniteEnum.complete a, ?_⟩
    exact List.mem_map.mpr ⟨b, FiniteEnum.complete b, rfl⟩

/-- **Specification.** `G.FirstList xs x`: the list `xs` can begin with `x`. -/
def Grammar.FirstList (G : Grammar T N) (xs : List (Sym T N)) (x : LTok T) : Prop :=
  match x with
  | LTok.tok t => ∃ ys, Derives G xs (Sym.tok t :: ys)
  | LTok.eof => Derives G xs []

/-- **Specification.** `G.FirstSym s x`: the symbol `s` can begin with `x`. -/
def Grammar.FirstSym (G : Grammar T N) (s : Sym T N) (x : LTok T) : Prop :=
  G.FirstList [s] x

/-- `isEof eof = true`, `isEof (tok t) = false`. -/
def isEof : LTok T → Bool
  | LTok.eof => true
  | LTok.tok _ => false

@[simp] theorem isEof_eof : isEof (LTok.eof : LTok T) = true := rfl
@[simp] theorem isEof_tok (t : T) : isEof (LTok.tok t) = false := rfl

theorem isEof_eq_true_iff {x : LTok T} : isEof x = true ↔ x = LTok.eof := by
  cases x <;> simp [isEof]

/-- The list rule of the FIRST computation. -/
def firstListTest (S : Sym T N → LTok T → Bool) (nul : Sym T N → Bool) :
    List (Sym T N) → LTok T → Bool
  | [], x => isEof x
  | s :: ss, x => (S s x && !isEof x) || (nul s && firstListTest S nul ss x)

/-- The symbol rules of the FIRST computation. -/
def firstTest [DecidableEq T] [DecidableEq N] (G : Grammar T N) (nul : Sym T N → Bool)
    (S : (Sym T N × LTok T) → Bool) (p : Sym T N × LTok T) : Bool :=
  match p with
  | (Sym.tok t, x) => x == LTok.tok t
  | (Sym.var A, x) => G.productions.any fun pr => pr.1 == A &&
      firstListTest (fun s y => S (s, y)) nul pr.2 x

/-- The monotone transformer whose least fixed point is FIRST. -/
def firstP [DecidableEq T] [DecidableEq N] (G : Grammar T N) (nul : Sym T N → Bool) :
    ((Sym T N × LTok T) → Bool) → (Sym T N × LTok T) → Bool :=
  firstTest G nul

theorem firstListTest_mono (nul : Sym T N → Bool) : ∀ (S S' : Sym T N → LTok T → Bool),
    (∀ s x, S s x = true → S' s x = true) →
      ∀ rhs x, firstListTest S nul rhs x = true → firstListTest S' nul rhs x = true := by
  intro S S' hle rhs
  induction rhs with
  | nil => intro x h; simpa [firstListTest] using h
  | cons s ss ih =>
      intro x h
      simp only [firstListTest] at h ⊢
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        exact Fixpoint.or_eq_true_iff.mpr
          (Or.inl (Fixpoint.and_eq_true_iff.mpr ⟨hle s x h1, h2⟩))
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        exact Fixpoint.or_eq_true_iff.mpr
          (Or.inr (Fixpoint.and_eq_true_iff.mpr ⟨h1, ih x h2⟩))

theorem firstP_mono [DecidableEq T] [DecidableEq N] (G : Grammar T N) (nul : Sym T N → Bool) :
    Fixpoint.PMono (firstP G nul) := by
  intro f g hfg p h
  unfold firstP firstTest at *
  cases p with
  | mk s x =>
      cases s with
      | tok t => simpa [firstTest] using h
      | var A =>
          obtain ⟨pr, hpr, hand⟩ := List.any_eq_true.mp h
          obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
          refine List.any_eq_true.mpr ⟨pr, hpr,
            Fixpoint.and_eq_true_iff.mpr ⟨h1, ?_⟩⟩
          exact firstListTest_mono nul (fun a y => f (a, y)) (fun a y => g (a, y))
            (fun a y hy => hfg (a, y) hy) pr.2 x h2

/-- One pass per pair (symbol, lookahead). -/
def Grammar.firstRounds [FiniteEnum T] [FiniteEnum N] (_G : Grammar T N) : Nat :=
  (FiniteEnum.elems (α := Sym T N × LTok T)).length

/-- The computed FIRST relation. -/
def Grammar.first [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N] (G : Grammar T N)
    (s : Sym T N) (x : LTok T) : Bool :=
  Fixpoint.iterP (firstP G (symNull G.nullable)) (G.firstRounds) (s, x)

/-- The nullability test consumed by the FIRST computation. -/
abbrev firstNul [BEq N] [FiniteEnum N] (G : Grammar T N) : Sym T N → Bool :=
  symNull (G.nullable)

theorem first_closed [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (G : Grammar T N) (s : Sym T N) (x : LTok T) :
    G.first s x = true ↔
      firstTest G (symNull G.nullable) (fun p => G.first p.1 p.2) (s, x) = true := by
  show Fixpoint.iterP (firstP G (symNull G.nullable)) (G.firstRounds) (s, x) = true ↔
      firstP G (symNull G.nullable)
        (Fixpoint.iterP (firstP G (symNull G.nullable)) (G.firstRounds)) (s, x) = true
  exact Fixpoint.iterP_closed (FiniteEnum.elems (α := Sym T N × LTok T))
    (firstP G (symNull G.nullable)) (firstP_mono G _) FiniteEnum.complete (s, x)

/-- The nullability test used by the FIRST computation really is nullability. -/
theorem symNull_iff [BEq N] [LawfulBEq N] [FiniteEnum N] (G : Grammar T N) (s : Sym T N) :
    symNull G.nullable s = true ↔ Derives G [s] [] := by
  cases s with
  | tok t =>
      constructor
      · intro h; exact absurd h (by simp [symNull])
      · intro h
        have h2 := derives_toks_inj (G := G) (ws := [t]) (vs := []) h
        exact absurd h2 (by simp)
  | var A => exact nullable_iff G A

section Soundness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

theorem firstListTest_sound (G : Grammar T N) (nul : Sym T N → Bool)
    (hnul : ∀ s, nul s = true ↔ Derives G [s] []) (S : Sym T N → LTok T → Bool)
    (hS : ∀ s x, S s x = true → G.FirstSym s x) :
    ∀ (rhs : List (Sym T N)) (x : LTok T),
      firstListTest S nul rhs x = true → G.FirstList rhs x := by
  intro rhs
  induction rhs with
  | nil =>
      intro x h
      have : x = LTok.eof := isEof_eq_true_iff.mp (by simpa [firstListTest] using h)
      subst this
      exact derives_refl []
  | cons s ss ih =>
      intro x h
      simp only [firstListTest] at h
      rcases Fixpoint.or_eq_true_iff.mp h with htok | hnull
      · obtain ⟨hs, hne⟩ := Fixpoint.and_eq_true_iff.mp htok
        obtain ⟨t, rfl⟩ : ∃ t : T, x = LTok.tok t := by
          cases x with
          | tok t => exact ⟨t, rfl⟩
          | eof => simp [isEof] at hne
        obtain ⟨ys, hder⟩ := hS s (LTok.tok t) hs
        refine ⟨ys ++ ss, ?_⟩
        exact derives_append hder (derives_refl ss)
      · obtain ⟨hn, hrest⟩ := Fixpoint.and_eq_true_iff.mp hnull
        have hsn : Derives G [s] [] := (hnul s).mp hn
        cases x with
        | eof => exact derives_append hsn (ih LTok.eof hrest)
        | tok t =>
            obtain ⟨ys, hder⟩ := ih (LTok.tok t) hrest
            refine ⟨ys, derives_append hsn hder⟩

/-- **Soundness of the computation.**  Every lookahead the iteration assigns to a
symbol is a lookahead the grammar really admits. -/
theorem first_sound (G : Grammar T N) : ∀ (k : Nat) (s : Sym T N) (x : LTok T),
    Fixpoint.iterP (firstP G (firstNul G)) k (s, x) = true → G.FirstSym s x := by
  intro k
  induction k with
  | zero => intro s x h; exact absurd h (by simp [Fixpoint.iterP])
  | succ k ih =>
      intro s x h
      unfold firstP firstTest at h
      rw [Fixpoint.iterP_succ] at h
      cases s with
      | tok t =>
          have hx : x = LTok.tok t := eq_of_beq h
          subst hx
          exact ⟨[], derives_refl _⟩
      | var A =>
          obtain ⟨pr, hpr, hand⟩ := List.any_eq_true.mp h
          obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
          have hA : pr.1 = A := eq_of_beq h1
          have hprod : (A, pr.2) ∈ G.productions := hA ▸ hpr
          have hlist : G.FirstList pr.2 x :=
            firstListTest_sound G (firstNul G) (symNull_iff G)
              (fun sy y => Fixpoint.iterP (firstP G (firstNul G)) k (sy, y))
              (fun sy y hy => ih sy y hy) pr.2 x h2
          cases x with
          | tok t =>
              obtain ⟨ys, hder⟩ := hlist
              refine ⟨ys, derives_trans (derives_production A pr.2 hprod) hder⟩
          | eof =>
              exact derives_trans (derives_production A pr.2 hprod) hlist

end Soundness

section ListLemmas

variable [BEq T] [BEq N] [LawfulBEq N] [FiniteEnum T] [FiniteEnum N]

/-- `eof` is in the FIRST of a list exactly when every symbol of the list is nullable. -/
theorem firstListTest_eof (S : Sym T N → LTok T → Bool) (nul : Sym T N → Bool) :
    ∀ (rhs : List (Sym T N)), firstListTest S nul rhs LTok.eof = true ↔
      ∀ s ∈ rhs, nul s = true := by
  intro rhs
  induction rhs with
  | nil => simp [firstListTest]
  | cons s ss ih =>
      constructor
      · intro h
        simp only [firstListTest] at h
        rcases Fixpoint.or_eq_true_iff.mp h with h | h
        · obtain ⟨_, hne⟩ := Fixpoint.and_eq_true_iff.mp h
          exact absurd hne (by simp [isEof])
        · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
          intro x hx
          rcases List.mem_cons.mp hx with heq | hmem
          · exact heq ▸ h1
          · exact (ih.mp h2) x hmem
      · intro hall
        rw [firstListTest, Fixpoint.or_eq_true_iff]
        right
        refine Fixpoint.and_eq_true_iff.mpr ⟨hall s (List.Mem.head _), ih.mpr ?_⟩
        intro x hx; exact hall x (List.Mem.tail _ hx)

end ListLemmas

section Completeness

variable {x : LTok T}

/-- Appending on the right cannot lose a *token* lookahead. (It can lose `eof`: a list
whose whole yield is empty stops being empty when something is appended.) -/
theorem firstListTest.prepend (S : Sym T N → LTok T → Bool) (nul : Sym T N → Bool) :
    ∀ (xs ys : List (Sym T N)), firstListTest S nul xs x = true → isEof x = false →
      firstListTest S nul (xs ++ ys) x = true := by
  intro xs
  induction xs with
  | nil => intro ys h hne; exact absurd h (by simpa [firstListTest] using hne)
  | cons s ss ih =>
      intro ys h hne
      simp only [List.cons_append, firstListTest] at h ⊢
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · exact Fixpoint.or_eq_true_iff.mpr (Or.inl h)
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        exact Fixpoint.or_eq_true_iff.mpr
          (Or.inr (Fixpoint.and_eq_true_iff.mpr ⟨h1, ih ys h2 hne⟩))

/-- If a prefix is all nullable, the FIRST of the tail is the FIRST of the whole. -/
theorem firstListTest.of_allNull (S : Sym T N → LTok T → Bool) (nul : Sym T N → Bool) :
    ∀ (xs ys : List (Sym T N)), (∀ s ∈ xs, nul s = true) →
      firstListTest S nul ys x = true → firstListTest S nul (xs ++ ys) x = true := by
  intro xs
  induction xs with
  | nil => intro ys _ h; exact h
  | cons s ss ih =>
      intro ys hall h
      simp only [List.cons_append, firstListTest]
      refine Fixpoint.or_eq_true_iff.mpr (Or.inr (Fixpoint.and_eq_true_iff.mpr
        ⟨hall s (List.Mem.head _), ih ys (fun x hx => hall x (List.Mem.tail _ hx)) h⟩))

/-- A lookahead of a concatenation comes from the prefix, or the prefix is all nullable
and it comes from the tail. -/
theorem firstListTest.append_imp (S : Sym T N → LTok T → Bool) (nul : Sym T N → Bool) :
    ∀ (xs ys : List (Sym T N)),
      firstListTest S nul (xs ++ ys) x = true → firstListTest S nul xs x = true ∨
        ((∀ s ∈ xs, nul s = true) ∧ firstListTest S nul ys x = true) := by
  intro xs
  induction xs with
  | nil => intro ys h; exact Or.inr ⟨by simp, h⟩
  | cons s ss ih =>
      intro ys h
      simp only [List.cons_append, firstListTest] at h ⊢
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · exact Or.inl (Fixpoint.or_eq_true_iff.mpr (Or.inl h))
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        rcases ih ys h2 with hrest | hall
        · exact Or.inl (Fixpoint.or_eq_true_iff.mpr (Or.inr (Fixpoint.and_eq_true_iff.mpr
            ⟨h1, hrest⟩)))
        · refine Or.inr ⟨?_, hall.2⟩
          intro z hz
          rcases List.mem_cons.mp hz with heq | hmem
          · exact heq ▸ h1
          · exact hall.1 z hmem

end Completeness

section Backwards

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]


/-- **One derivation step, backwards.**  Replacing a nonterminal by the right-hand side
of one of its productions cannot create a lookahead that was not already there. -/
theorem first_step_back (G : Grammar T N) {B : N} {rhs post pre : List (Sym T N)}
    (x : LTok T) (hp : (B, rhs) ∈ G.productions) :
    firstListTest G.first (firstNul G) (pre ++ rhs ++ post) x = true →
      firstListTest G.first (firstNul G) (pre ++ (Sym.var B :: post)) x = true := by
  induction pre with
  | nil =>
      intro h
      rw [List.nil_append] at h ⊢
      rcases firstListTest.append_imp G.first (firstNul G) rhs post h with h1 | h2
      · -- the lookahead comes from `rhs`: the production rule puts it on `var B`
        have hclosed : G.first (Sym.var B) x = true := by
          rw [first_closed G (Sym.var B) x]
          refine List.any_eq_true.mpr ⟨(B, rhs), hp,
            Fixpoint.and_eq_true_iff.mpr ⟨by simp, h1⟩⟩
        rw [firstListTest]
        by_cases hne : isEof x = false
        · exact Fixpoint.or_eq_true_iff.mpr
            (Or.inl (Fixpoint.and_eq_true_iff.mpr ⟨hclosed, by simp [hne]⟩))
        · -- x = eof: then all of rhs ++ post is nullable
          have hx : x = LTok.eof := by
            cases x with
            | tok t => exact absurd rfl hne
            | eof => rfl
          subst hx
          have hall : ∀ s ∈ rhs ++ post, firstNul G s = true :=
            (firstListTest_eof G.first (firstNul G) (rhs ++ post)).mp h
          have hpost : firstListTest G.first (firstNul G) post LTok.eof = true := by
            refine (firstListTest_eof G.first (firstNul G) post).mpr ?_
            intro s hs; exact hall s (List.mem_append.mpr (Or.inr hs))
          have hnullB : firstNul G (Sym.var B) = true := by
            have hder : Derives G rhs [] := derives_nil_of_symbols rhs
              (fun s hs => (symNull_iff G s).mp (hall s (List.mem_append.mpr (Or.inl hs))))
            simpa [firstNul, symNull] using
              (nullable_iff G B).mpr (derives_trans (derives_production B rhs hp) hder)
          exact Fixpoint.or_eq_true_iff.mpr
            (Or.inr (Fixpoint.and_eq_true_iff.mpr ⟨hnullB, hpost⟩))
      · -- rhs is all nullable and the lookahead comes from post
        obtain ⟨hall, hpost⟩ := h2
        have hnullB : firstNul G (Sym.var B) = true := by
          have hder : Derives G rhs [] := derives_nil_of_symbols rhs
            (fun s hs => (symNull_iff G s).mp (hall s hs))
          simpa [firstNul, symNull] using
            (nullable_iff G B).mpr (derives_trans (derives_production B rhs hp) hder)
        rw [firstListTest]
        exact Fixpoint.or_eq_true_iff.mpr
          (Or.inr (Fixpoint.and_eq_true_iff.mpr ⟨hnullB, hpost⟩))
  | cons s ss ih =>
      intro h
      simp only [List.cons_append] at h ⊢
      simp only [firstListTest] at h ⊢
      rcases Fixpoint.or_eq_true_iff.mp h with h | h
      · exact Fixpoint.or_eq_true_iff.mpr (Or.inl h)
      · obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp h
        refine Fixpoint.or_eq_true_iff.mpr
          (Or.inr (Fixpoint.and_eq_true_iff.mpr ⟨h1, ih h2⟩))

/-- **FIRST is preserved backwards along a derivation.** -/
theorem first_backwards (G : Grammar T N) (xs ys : List (Sym T N)) (x : LTok T)
    (h : Derives G xs ys) :
    firstListTest G.first (firstNul G) ys x = true →
      firstListTest G.first (firstNul G) xs x = true := by
  induction h with
  | refl => intro hl; exact hl
  | @tail mid fin hrec hstep ih =>
      intro hl
      refine ih ?_
      obtain ⟨B, rhs, pre, post, hp, e1, e2⟩ := derives1_decompose hstep
      rw [e1]
      rw [e2] at hl
      exact first_step_back G (B := B) (rhs := rhs) (post := post) (pre := pre) x hp hl

end Backwards

/-- A list containing an element has positive length. -/
theorem length_pos_of_mem {l : List α} (h : ∃ x, x ∈ l) : 1 ≤ l.length := by
  obtain ⟨x, hx⟩ := h
  cases l with
  | nil => cases hx
  | cons a as => exact Nat.succ_le_succ (Nat.zero_le _)

section Main

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- A terminal has itself as its only token lookahead, and the computation knows it. -/
theorem first_tok (G : Grammar T N) (t : T) : G.first (Sym.tok t) (LTok.tok t) = true := by
  have h1 : Fixpoint.iterP (firstP G (firstNul G)) 1 (Sym.tok t, LTok.tok t) = true := by
    rw [Fixpoint.iterP_succ]
    unfold firstP firstTest
    simp
  have hmem : (Sym.tok t, LTok.tok t) ∈ (FiniteEnum.elems (α := Sym T N × LTok T)) :=
    FiniteEnum.complete _
  have hpos : 1 ≤ (FiniteEnum.elems (α := Sym T N × LTok T)).length :=
    length_pos_of_mem ⟨_, hmem⟩
  refine Fixpoint.iterP_le_limit (firstP G (firstNul G)) (firstP_mono G _)
    (Sym.tok t, LTok.tok t) 1 (G.firstRounds) (by simpa [Grammar.firstRounds] using hpos) h1

/-- A nullable nonterminal has `eof` in its FIRST. -/
theorem first_var_eof (G : Grammar T N) (A : N) (h : G.nullable A = true) :
    G.first (Sym.var A) LTok.eof = true := by
  have hspec : G.Nullable A := (nullable_iff G A).mp h
  obtain ⟨rhs, hp, hder⟩ := derives_head_var hspec (by simp)
  have hall : ∀ s ∈ rhs, symNull G.nullable s = true :=
    nullable_backward G rhs [] hder (by simp)
  have hlist : firstListTest G.first (firstNul G) rhs LTok.eof = true :=
    (firstListTest_eof G.first (firstNul G) rhs).mpr hall
  rw [first_closed G (Sym.var A) LTok.eof]
  refine List.any_eq_true.mpr ⟨(A, rhs), hp, Fixpoint.and_eq_true_iff.mpr ⟨by simp, hlist⟩⟩

/-- **Completeness of the computation.**  Every lookahead the grammar really admits is
found by the iteration. -/
theorem first_complete (G : Grammar T N) (s : Sym T N) (x : LTok T)
    (h : G.FirstSym s x) : G.first s x = true := by
  cases x with
  | tok t =>
      obtain ⟨ys, hder⟩ := h
      have h2 : firstListTest G.first (firstNul G) (Sym.tok t :: ys) (LTok.tok t) = true := by
        rw [firstListTest]
        refine Fixpoint.or_eq_true_iff.mpr
          (Or.inl (Fixpoint.and_eq_true_iff.mpr ⟨first_tok G t, by simp [isEof]⟩))
      have h3 := first_backwards G [s] (Sym.tok t :: ys) (LTok.tok t) hder h2
      simpa [firstListTest, Grammar.FirstSym, Grammar.FirstList] using h3
  | eof =>
      have h2 : firstListTest G.first (firstNul G) ([] : List (Sym T N)) LTok.eof = true := by
        simp [firstListTest]
      have h3 := first_backwards G [s] [] LTok.eof h h2
      simp only [firstListTest, isEof_eof, Bool.not_true, Bool.and_false] at h3 ⊢
      cases s with
      | tok t => exact absurd h3 (by simp [symNull])
      | var A => exact first_var_eof G A (by simpa [firstNul, symNull] using h3)

/-- **The characterisation.**  The computation decides FIRST. -/
theorem first_iff (G : Grammar T N) (s : Sym T N) (x : LTok T) :
    G.first s x = true ↔ G.FirstSym s x :=
  ⟨fun h => first_sound G G.firstRounds s x h, fun h => first_complete G s x h⟩

/-- **Correct end-of-input behaviour.**  `eof` is in the FIRST of a symbol exactly when
the symbol derives nothing. -/
theorem first_eof_iff_nullable (G : Grammar T N) (s : Sym T N) :
    G.first s LTok.eof = true ↔ Derives G [s] [] := by
  rw [first_iff]
  simp [Grammar.FirstSym, Grammar.FirstList]

end Main

end VerifiedLL1
