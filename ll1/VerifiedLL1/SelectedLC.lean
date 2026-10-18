/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.LeftRec

/-!
# Phase 5.3 - reachable selected cycles are impossible

## The theorem

Vermillion's operational core is a *lookahead-indexed* left-corner relation: an edge
A -> B at lookahead x is a production of A whose right-hand side reaches B after an
erasable prefix, and which the x-column of SELECT actually claims for A.  A cycle of
such edges at a single lookahead is exactly what makes a recursive-descent parser loop
without consuming input.  This module proves that LL(1) excludes them for every
nonterminal that occurs:

    Grammar.noSelectedLCCycle : G.Ll1 -> G.Occurs A -> not (G.SelectedLCPath x A A)

The reachability hypothesis cannot be dropped: with S -> a and U -> U b | epsilon the
checker passes, the entry for (U, b) selects U b, and parsing U on the input b
exhausts every fuel, because this repository's FOLLOW only collects lookaheads from
*reachable* occurrences.  See Examples/UnreachableSelectedCycle.lean.

## Why Reduced is not needed here

The counting argument of LeftRec.lean needed productivity to turn a stopping position
into a FIRST statement.  Two observations remove that need:

* AtLookahead x ys already gives G.FirstList ys x - the witness is the form itself
  (Grammar.FirstList.of_atLookahead_free), so comparing stopping traces needs no
  hypothesis beyond Ll1 (headSteps_stop_length_unique_free).
* A selected edge carries its own productivity: G.Select A (alpha B beta) x means
  either x is in FIRST(alpha B beta) - a stopping witness - or alpha B beta erases and
  x is in FOLLOW(A).  The two cases are SelLCFirst and SelLCNErased, and every selected
  edge is one of them.

## The proof

A path is split into the case where some edge is justified by FIRST (SelPathF) and the
case where every edge erases (SelPathE).

* SelPathF: the FIRST edge supplies a head-expansion trace to a form sitting at x
  (headSteps_stop_of_first, proved by lifting head traces across one derivation step
  with headSteps_lift_derives1).  Appending an arbitrary continuation to that trace
  leaves its length untouched, so the stopping length from (var A :: psi) is a constant
  c independent of psi.  Going once around the cycle costs 0 < J head expansions and
  lands on (var A :: delta ++ psi), whose stopping length is the same c.  Uniqueness
  gives c = J + c.
* SelPathE: every production on the cycle erases, so A erases, the cycle tail delta
  erases, and x in FOLLOW(A) supplies a continuation post with x in FIRST(post).
  Now (var A :: delta^n ++ post) erases down to post, so it has a stopping witness of
  some length c_n, and uniqueness gives c_n = J + c_(n+1): an infinite descent in Nat.

## Contents

* SelectedLeftCorner / SelectedLCPath - the relation, as in the review artifact.
* SelLCFirst / SelLCNErased / SelPathF / SelPathE - the case split.
* headSteps_lift_derives1, headSteps_stop_of_first - stopping witnesses.
* noSelectedLCCycle, reachableSelectedLCAcyclic.
-/

set_option linter.unusedSectionVars false

universe u v w

namespace VerifiedLL1

variable {T : Type u} {N : Type v} {G : Grammar T N}

section Relations

/-- **Selected left corner.**  G.SelectedLeftCorner x A B: a production of A whose
right-hand side reaches B after an erasable prefix, and which the x-column of the
SELECT sets claims for A. -/
def Grammar.SelectedLeftCorner {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) (A B : N) : Prop := 
  ∃ pre post : List (Sym T N),
    (A, pre ++ Sym.var B :: post) ∈ G.productions ∧
    G.Select A (pre ++ Sym.var B :: post) x ∧ Derives G pre []

/-- **Selected left corner, justified by FIRST.**  The lookahead already appears in the
FIRST of the right-hand side; this is the case that produces a stopping witness. -/
def Grammar.SelLCFirst {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) (A B : N) : Prop :=
  ∃ pre post : List (Sym T N),
    (A, pre ++ Sym.var B :: post) ∈ G.productions ∧ isEof x = false ∧
    G.FirstList (pre ++ Sym.var B :: post) x ∧ Derives G pre []

/-- **Selected left corner, justified by erasure.**  The whole right-hand side erases and
x comes from FOLLOW(A): the parser stays at lookahead x and descends into B. -/
def Grammar.SelLCNErased {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) (A B : N) : Prop :=
  ∃ pre post : List (Sym T N),
    (A, pre ++ Sym.var B :: post) ∈ G.productions ∧
    Derives G (pre ++ Sym.var B :: post) [] ∧ Derives G pre [] ∧ G.FollowSym A x

/-- **Selected left corner paths** at a fixed lookahead: the transitive closure that keeps
the lookahead constant. -/
inductive Grammar.SelectedLCPath {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) : N -> N -> Prop where
  | single {A B} : G.SelectedLeftCorner x A B -> G.SelectedLCPath x A B
  | tail {A B C} : G.SelectedLCPath x A B -> G.SelectedLeftCorner x B C ->
      G.SelectedLCPath x A C

/-- **A selected path with at least one FIRST-justified edge.**  The constructors say:
a single FIRST edge, an arbitrary prefix followed by a FIRST edge, or a path that already
has one extended by any further edge. -/
inductive Grammar.SelPathF {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) : N → N → Prop where
  | single {A B} : G.SelLCFirst x A B → G.SelPathF x A B
  | pre {A B C} : G.SelectedLCPath x A B → G.SelLCFirst x B C → G.SelPathF x A C
  | tail {A B C} : G.SelPathF x A B → G.SelectedLeftCorner x B C → G.SelPathF x A C

/-- A selected path all of whose edges erase. -/
inductive Grammar.SelPathE {T : Type u} {N : Type v}
    (G : Grammar T N) (x : LTok T) : N → N → Prop where
  | single {A B} : G.SelLCNErased x A B → G.SelPathE x A B
  | step {A B C} : G.SelPathE x A B → G.SelLCNErased x B C → G.SelPathE x A C

/-- **Every selected edge is FIRST-justified or erasing**, by the shape of Select. -/
theorem selLeftCorner_cases {x : LTok T} {A B : N} (h : G.SelectedLeftCorner x A B) :
    G.SelLCFirst x A B ∨ G.SelLCNErased x A B := by
  obtain ⟨pre, post, hprod, hsel, hnul⟩ := h
  cases hsel with
  | inl hne => exact Or.inl ⟨pre, post, hprod, hne.1, hne.2, hnul⟩
  | inr hr => exact Or.inr ⟨pre, post, hprod, hr.1, hnul, hr.2⟩

/-- **The case split for paths**: a selected path either has a FIRST-justified edge or
every edge erases. -/
theorem selPathF_or_selPathE {x : LTok T} {A B : N} (h : G.SelectedLCPath x A B) :
    G.SelPathF x A B ∨ G.SelPathE x A B := by
  induction h with
  | single he =>
      rcases selLeftCorner_cases he with hf | he'
      · exact Or.inl (Grammar.SelPathF.single hf)
      · exact Or.inr (Grammar.SelPathE.single he')
  | tail hpath he ih =>
      rcases ih with hf | he'
      · exact Or.inl (Grammar.SelPathF.tail hf he)
      · rcases selLeftCorner_cases he with hf2 | he2
        · exact Or.inl (Grammar.SelPathF.pre hpath hf2)
        · exact Or.inr (Grammar.SelPathE.step he' he2)

/-- **Paths compose.** -/
theorem selectedLCPath_trans {x : LTok T} {A B C : N}
    (h : G.SelectedLCPath x A B) (h' : G.SelectedLCPath x B C) : G.SelectedLCPath x A C := by
  induction h' with
  | single he => exact Grammar.SelectedLCPath.tail h he
  | tail hpath he ih => exact Grammar.SelectedLCPath.tail ih he

end Relations
section Stopping

/-- A one-step derivation can be lifted through an appended left context. -/
theorem derives1_append_left {xs ys : List (Sym T N)} (h : Derives1 G xs ys) :
    (l : List (Sym T N)) → Derives1 G (l ++ xs) (l ++ ys) := by
  intro l
  induction l with
  | nil => exact h
  | cons s rest ih => exact derives1_cons ih s

/-- **Lifting a head-expansion trace across one derivation step.**  If `y' \u21d2\u2081 ys` and head
expansion of `ys` lands on `w`, then some head expansion of `y'` lands on a form with the
same head symbol as `w` (`none` being the head of the empty form).  The redex of the step
drifts to the right as the trace advances, which is why the trace is inducted on and the
step stays in the goal. -/
theorem headSteps_lift_derives1 :
    ∀ {ys w : List (Sym T N)} {k : Nat}, HeadSteps G ys w k → ∀ {y' : List (Sym T N)},
      Derives1 G y' ys → ∃ w' k', HeadSteps G y' w' k' ∧ w.head? = w'.head? := by
  intro ys w k htr
  induction htr with
  | refl =>
      intro y' hs
      obtain ⟨A, rhs, pre, post, hp, hy', hw⟩ := derives1_decompose hs
      cases pre with
      | nil =>
          refine ⟨_, 1, ?_, rfl⟩
          rw [hy', hw]
          exact HeadSteps.step hp (HeadSteps.refl _)
      | cons s rest =>
          refine ⟨y', 0, HeadSteps.refl _, by rw [hy', hw]; rfl⟩
  | @step B rhs₀ cont w' k₁ hp htr ih =>
      intro y' hs
      obtain ⟨A, rhs, pre, post, hprod, hy', hys⟩ := derives1_decompose hs
      cases pre with
      | nil =>
          refine ⟨w', 1 + (k₁ + 1), ?_, rfl⟩
          have h1 : HeadSteps G y' (Sym.var B :: cont) 1 := by
            rw [hy', hys]
            exact HeadSteps.step hprod (HeadSteps.refl _)
          exact HeadSteps.trans h1 (HeadSteps.step hp htr)
      | cons s rest =>
          have hsB : Sym.var B = s := (List.cons.inj hys).1
          have hcont : cont = rest ++ rhs ++ post := by
            simpa [List.cons_append] using (List.cons.inj hys).2
          subst hsB
          have hstep1 : HeadSteps G y' (rhs₀ ++ (rest ++ (Sym.var A :: post))) 1 := by
            rw [hy']
            exact HeadSteps.step hp (HeadSteps.refl _)
          have hderiv : Derives1 G (rhs₀ ++ (rest ++ (Sym.var A :: post))) (rhs₀ ++ cont) := by
            have hh := Derives1.step (pre := (rest : List (Sym T N))) (post := post) hprod
            have hh2 := derives1_append_left hh rhs₀
            simp only [hcont, List.append_assoc] at hh2 ⊢
            exact hh2
          obtain ⟨u, k', ht2, heq⟩ := ih hderiv
          exact ⟨u, 1 + k', HeadSteps.trans hstep1 ht2, heq⟩
/-- `HeadAt G xs h`: some head expansion of `xs` lands on a form whose head is `h`, where
`none` stands for the empty form. -/
def HeadAt {T : Type u} {N : Type v} (G : Grammar T N) (xs : List (Sym T N))
    (h : Option (Sym T N)) : Prop :=
  ∃ ys k, HeadSteps G xs ys k ∧ ys.head? = h

theorem headAt_self (xs : List (Sym T N)) : HeadAt G xs xs.head? :=
  ⟨xs, 0, HeadSteps.refl _, rfl⟩

/-- **Head shapes are reflected backwards along a derivation.**  If `xs =* ys` and a head
expansion of `ys` can land on a form with head `h`, then a head expansion of `xs` can too.
This is the replacement for a diamond property: we never reorder an arbitrary derivation,
we only lift its head part. -/
theorem headAt_of_derives {xs ys : List (Sym T N)} (h : Derives G xs ys) :
    ∀ {h₁ : Option (Sym T N)}, HeadAt G ys h₁ → HeadAt G xs h₁ := by
  induction h with
  | refl => intro _ hh; exact hh
  | tail h' hs ih =>
      intro h₁ hh
      obtain ⟨w, k, ht, hw⟩ := hh
      obtain ⟨w', k', ht', heq⟩ := headSteps_lift_derives1 ht hs
      exact ih ⟨w', k', ht', by rw [← heq]; exact hw⟩

/-- **Stopping witness from a FIRST witness.**  If `xs` can begin with the lookahead `x`,
then some head expansion of `xs` lands on a form that *sits* at `x`.  No productivity
hypothesis is needed: the derivation that witnesses `FirstList` is itself the source of the
head expansions, and the stopping form inherits the head of that derivation's target. -/
theorem headSteps_stop_of_first {xs : List (Sym T N)} {x : LTok T}
    (hf : G.FirstList xs x) :
    ∃ ys k, HeadSteps G xs ys k ∧ AtLookahead x ys := by
  cases x with
  | tok t =>
      obtain ⟨ys, hder⟩ := hf
      obtain ⟨w, k, ht, hw⟩ :=
        headAt_of_derives hder (h₁ := some (Sym.tok t)) (by simpa using headAt_self (Sym.tok t :: ys))
      cases w with
      | nil => exact absurd hw (by simp)
      | cons s rest =>
          have hst : s = Sym.tok t := Option.some.inj hw
          subst hst
          exact ⟨Sym.tok t :: rest, k, ht, ⟨rest, rfl⟩⟩
  | eof =>
      obtain ⟨w, k, ht, hw⟩ :=
        headAt_of_derives hf (h₁ := none) (by simpa using headAt_self ([] : List (Sym T N)))
      cases w with
      | nil => exact ⟨[], k, ht, rfl⟩
      | cons s rest => exact absurd hw (by simp)

/-- A selected edge is a positive head-expansion trace from its source to in front of the
accumulated tail. -/
theorem headSteps_of_selLeftCorner {x : LTok T} {A B : N}
    (h : G.SelectedLeftCorner x A B) :
    ∃ γ k, 0 < k ∧ HeadSteps G [Sym.var A] (Sym.var B :: γ) k := by
  obtain ⟨pre, post, hprod, hsel, hnul⟩ := h
  have hc : G.LeftCorner A B := ⟨pre, post, by simpa using hprod, hnul⟩
  exact headSteps_of_leftCorner hc

/-- A FIRST-justified edge is a selected path. -/
theorem selLCFirst_to_path {x : LTok T} {A B : N} (h : G.SelLCFirst x A B) :
    G.SelectedLCPath x A B := by
  obtain ⟨pre, post, hprod, hne, hf', hnul⟩ := h
  exact Grammar.SelectedLCPath.single ⟨pre, post, hprod, Or.inl ⟨hne, hf'⟩, hnul⟩

/-- A selected path is a positive head-expansion trace: each edge expands the head through
its erasable prefix and lands in front of the accumulated tail. -/
theorem selectedLCPath_trace {x : LTok T} {A B : N} (h : G.SelectedLCPath x A B) :
    ∃ δ k, 0 < k ∧ HeadSteps G [Sym.var A] (Sym.var B :: δ) k := by
  induction h with
  | single he => exact headSteps_of_selLeftCorner he
  | tail hpath he ih =>
      obtain ⟨δ₁, k₁, hk₁, ht₁⟩ := ih
      obtain ⟨δ₂, k₂, hk₂, ht₂⟩ := headSteps_of_selLeftCorner he
      refine ⟨δ₂ ++ δ₁, k₁ + k₂, by omega, HeadSteps.trans ht₁ ?_⟩
      have h2 := HeadSteps.append_right δ₁ ht₂
      simpa [List.cons_append, List.append_assoc] using h2

/-- A `SelPathF` is in particular a selected path. -/
theorem selPathF_to_path {x : LTok T} {A B : N} (h : G.SelPathF x A B) :
    G.SelectedLCPath x A B := by
  induction h with
  | single hf => exact selLCFirst_to_path hf
  | pre hpath hf => exact selectedLCPath_trans hpath (selLCFirst_to_path hf)
  | tail hp he ih => exact Grammar.SelectedLCPath.tail ih he
end Stopping

section Cycles

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- A FIRST-justified edge yields a **uniform** stopping witness: the number of head
expansions that reaches a form sitting at `x` from `var A :: psi` does not depend on the
continuation `psi`, because the trace stops inside the right-hand side the edge expands
to and merely carries `psi` along. -/
theorem selLCFirst_uniform_stop {x : LTok T} {A B : N} (h : G.SelLCFirst x A B) :
    ∃ c, ∀ psi, ∃ ys, HeadSteps G (Sym.var A :: psi) ys c ∧ AtLookahead x ys := by
  obtain ⟨pre, post, hprod, hne, hf, hnul⟩ := h
  obtain ⟨t, rfl⟩ : ∃ t, x = LTok.tok t := by
    cases x with
    | tok t => exact ⟨t, rfl⟩
    | eof => exact absurd hne (by simp [isEof])
  obtain ⟨ys, k, ht, ha⟩ := headSteps_stop_of_first hf
  obtain ⟨zs, hys⟩ := ha
  refine ⟨1 + k, fun psi => ⟨ys ++ psi, ?_, ?_⟩⟩
  · have h1 : HeadSteps G (Sym.var A :: psi) ((pre ++ Sym.var B :: post) ++ psi) 1 :=
      HeadSteps.step hprod (HeadSteps.refl _)
    have h2 : HeadSteps G ((pre ++ Sym.var B :: post) ++ psi) (ys ++ psi) k :=
      HeadSteps.append_right psi ht
    exact HeadSteps.trans h1 h2
  · rw [hys]
    exact ⟨zs ++ psi, rfl⟩

/-- A path with a FIRST-justified edge has a uniform stopping witness at its start: walk
the prefix, then use the FIRST edge's witness with the prefix tail appended. -/
theorem selPathF_uniform_stop {x : LTok T} {A B : N} (h : G.SelPathF x A B) :
    ∃ c, ∀ psi, ∃ ys, HeadSteps G (Sym.var A :: psi) ys c ∧ AtLookahead x ys := by
  induction h with
  | single hf => exact selLCFirst_uniform_stop hf
  | pre hpath hf =>
      obtain ⟨δ, J, hJ, htr⟩ := selectedLCPath_trace hpath
      obtain ⟨c, hc⟩ := selLCFirst_uniform_stop hf
      refine ⟨J + c, fun psi => ?_⟩
      obtain ⟨ys, ht, ha⟩ := hc (δ ++ psi)
      have h1 := HeadSteps.append_right psi htr
      exact ⟨ys, HeadSteps.trans h1 ht, ha⟩
  | tail hp he ih => exact ih

/-- **One edge, landing exactly on the production's own tail.**  The tail is a parameter,
not an existential witness, so later lemmas can talk about erasing it. -/
theorem headSteps_of_edge {A B : N} (pre post : List (Sym T N))
    (hprod : (A, pre ++ Sym.var B :: post) ∈ G.productions) (hnul : Derives G pre []) :
    ∃ k, 0 < k ∧ HeadSteps G [Sym.var A] (Sym.var B :: post) k := by
  obtain ⟨ts, hm, hy⟩ := derives_forest (ws := []) hnul
  obtain ⟨ys, k, ht₁, ha⟩ := headSteps_of_match hm
  have heq : ys = [] := by
    rw [hy] at ha
    exact ha
  subst heq
  have hnil : pre ++ Sym.var B :: post ++ [] = pre ++ Sym.var B :: post := List.append_nil _
  have h0 : HeadSteps G [Sym.var A] (pre ++ Sym.var B :: post) 1 := by
    rw [← hnil]
    exact HeadSteps.step hprod (HeadSteps.refl _)
  have h1 : HeadSteps G (pre ++ Sym.var B :: post) (Sym.var B :: post) k := by
    have := HeadSteps.append_right (Sym.var B :: post) ht₁
    simpa [List.append_assoc] using this
  have h2 : HeadSteps G [Sym.var A] (Sym.var B :: post) (1 + k) := HeadSteps.trans h0 h1
  have hEq : 1 + k = k + 1 := by omega
  exact ⟨k + 1, Nat.zero_lt_succ _, hEq ▸ h2⟩

/-- An erasing edge erases its own target and its tail, and gives a positive trace whose
tail is the production's own tail. -/
theorem selLCNErased_erases {x : LTok T} {A B : N} (h : G.SelLCNErased x A B) :
    ∃ γ k, 0 < k ∧ HeadSteps G [Sym.var A] (Sym.var B :: γ) k ∧
      Derives G [Sym.var B] [] ∧ Derives G γ [] := by
  obtain ⟨pre, post, hprod, her, hnul, hfol⟩ := h
  obtain ⟨k, hk, htr⟩ := headSteps_of_edge pre post hprod hnul
  obtain ⟨_, h2⟩ := derives_nil_append pre (Sym.var B :: post) her
  obtain ⟨hB, hpost⟩ := derives_nil_append [Sym.var B] post h2
  exact ⟨post, k, hk, htr, hB, hpost⟩
/-- Every edge of a `SelPathE` erases: the target nonterminal erases, the accumulated tail
erases, and the lookahead belongs to the source's FOLLOW. -/
theorem selPathE_erases {x : LTok T} {A B : N} (h : G.SelPathE x A B) :
    ∃ δ k, 0 < k ∧ HeadSteps G [Sym.var A] (Sym.var B :: δ) k ∧
      Derives G [Sym.var B] [] ∧ Derives G δ [] ∧ G.FollowSym A x := by
  induction h with
  | single he =>
      obtain ⟨γ, k, hk, htr, hB, hγ⟩ := selLCNErased_erases he
      obtain ⟨_, _, _, _, _, hfol⟩ := he
      exact ⟨γ, k, hk, htr, hB, hγ, hfol⟩
  | step he he' ih =>
      obtain ⟨δ₁, k₁, hk₁, ht₁, hB, hδ₁, hfol⟩ := ih
      obtain ⟨δ₂, k₂, hk₂, ht₂, hC, hδ₂⟩ := selLCNErased_erases he'
      have h2' := HeadSteps.append_right δ₁ ht₂
      have hder : Derives G (δ₂ ++ δ₁) [] := derives_append hδ₂ hδ₁
      refine ⟨δ₂ ++ δ₁, k₁ + k₂, by omega, HeadSteps.trans ht₁ h2', hC, hder, hfol⟩

/-- **The FIRST case.**  A reachable cycle with a FIRST-justified edge contradicts the
uniqueness of the stopping length: the uniform constant `c` must equal `J + c`. -/
theorem noSelPathF_cycle (hall : G.Ll1) {A : N} (hocc : G.Occurs A) {x : LTok T}
    (h : G.SelPathF x A A) : False := by
  obtain ⟨c, hc⟩ := selPathF_uniform_stop h
  obtain ⟨δ, J, hJ, htr⟩ := selectedLCPath_trace (selPathF_to_path h)
  obtain ⟨pre, post, hpre⟩ := hocc
  have hR : G.Reachable (Sym.var A :: post) :=
    ⟨pre, by rw [← append_cons_eq]; exact hpre⟩
  obtain ⟨ys, ht, ha⟩ := hc post
  obtain ⟨ys', ht', ha'⟩ := hc (δ ++ post)
  have h1 : HeadSteps G (Sym.var A :: post) (Sym.var A :: δ ++ post) J := by
    have := HeadSteps.append_right post htr
    simpa [List.cons_append] using this
  have hcomp : HeadSteps G (Sym.var A :: post) ys' (J + c) := HeadSteps.trans h1 ht'
  have huni : c = J + c :=
    headSteps_stop_length_unique_free hall ht x hR ha ys' (J + c) hcomp ha'
  omega

/-- **The erasing case.**  When every edge erases, `var A :: δⁿ ++ post` erases down to a
form with `x` in its FIRST, so it has a stopping witness of some length `cₙ`; uniqueness
gives `cₙ = J + cₙ₊₁`, hence `n * J ≤ c₀` for every `n`. -/
theorem noSelPathE_cycle (hall : G.Ll1) {A : N} (_hocc : G.Occurs A) {x : LTok T}
    (h : G.SelPathE x A A) : False := by
  obtain ⟨δ, J, hJ, htr, hA, hδ, hfol⟩ := selPathE_erases h
  obtain ⟨pre', post', hpre', hfirst⟩ := hfol
  have hR : ∀ n, G.Reachable (Sym.var A :: listPow δ n ++ post') := by
    intro n
    induction n with
    | zero =>
        refine ⟨pre', ?_⟩
        simpa [listPow_zero] using hpre'
    | succ n ih =>
        have hcy : HeadSteps G (Sym.var A :: listPow δ n ++ post')
            (Sym.var A :: listPow δ (n + 1) ++ post') J := by
          have := HeadSteps.append_right (listPow δ n ++ post') htr
          simpa [listPow_succ, List.cons_append, List.append_assoc] using this
        exact Grammar.reachable_of_derives ih (HeadSteps.derives hcy)
  have herase : ∀ n, Derives G (Sym.var A :: listPow δ n) [] := by
    intro n
    refine derives_append hA ?_
    induction n with
    | zero => exact derives_refl []
    | succ m ih =>
        show Derives G (δ ++ listPow δ m) []
        exact derives_append hδ ih
  have hstop : ∀ n, ∃ ys k, HeadSteps G (Sym.var A :: listPow δ n ++ post') ys k ∧
      AtLookahead x ys := by
    intro n
    refine headSteps_stop_of_first
      (Grammar.FirstList.append_left_of_null (Sym.var A :: listPow δ n) post' x (herase n) hfirst)
  obtain ⟨ys₀, k₀, ht₀, ha₀⟩ := hstop 0
  have hiter : ∀ n, HeadSteps G (Sym.var A :: post')
      (Sym.var A :: listPow δ n ++ post') (n * J) := by
    intro n
    induction n with
    | zero =>
        rw [Nat.zero_mul, listPow_zero]
        exact HeadSteps.refl _
    | succ m ih =>
        have hcy : HeadSteps G (Sym.var A :: listPow δ m ++ post')
            (Sym.var A :: listPow δ (m + 1) ++ post') J := by
          have := HeadSteps.append_right (listPow δ m ++ post') htr
          simpa [listPow_succ, List.cons_append, List.append_assoc] using this
        have h := HeadSteps.trans ih hcy
        have hEq : m * J + J = (m + 1) * J := by
          rw [Nat.add_mul, Nat.one_mul]
        exact hEq ▸ h
  have hbound : ∀ n, n * J ≤ k₀ := by
    intro n
    induction n with
    | zero => omega
    | succ m ih =>
        obtain ⟨ys₁, k₁, ht₁, ha₁⟩ := hstop (m + 1)
        have hcomp : HeadSteps G (Sym.var A :: post') ys₁ ((m + 1) * J + k₁) :=
          HeadSteps.trans (hiter (m + 1)) ht₁
        have huni : k₀ = (m + 1) * J + k₁ :=
          headSteps_stop_length_unique_free hall ht₀ x (hR 0) ha₀ ys₁ _ hcomp ha₁
        omega
  have hge := hbound (k₀ + 1)
  have h1 : k₀ + 1 ≤ k₀ := by
    have hJ' : 1 ≤ J := by omega
    have hmul := Nat.mul_le_mul (Nat.le_refl (k₀ + 1)) hJ'
    omega
  omega

/-- **Phase 5.3 main theorem.**  Under LL(1) no occurring nonterminal lies on a cycle of
selected left corners at a single lookahead: the parser can never loop without consuming
input. -/
theorem Grammar.noSelectedLCCycle (hall : G.Ll1) {A : N} (hocc : G.Occurs A) (x : LTok T)
    (h : G.SelectedLCPath x A A) : False := by
  rcases selPathF_or_selPathE h with hf | he
  · exact noSelPathF_cycle hall hocc hf
  · exact noSelPathE_cycle hall hocc he

/-- **Acyclicity of reachable selected left corners** (the statement the review asks for). -/
def Grammar.ReachableSelectedLCAcyclic {T : Type u} {N : Type v}
    (G : Grammar T N) : Prop :=
  ∀ x A, G.Occurs A → ¬ G.SelectedLCPath x A A

/-- LL(1) implies it. -/
theorem Grammar.reachableSelectedLCAcyclic (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hall : G.Ll1) : G.ReachableSelectedLCAcyclic :=
  fun x _A hocc hpath => Grammar.noSelectedLCCycle hall hocc x hpath

end Cycles

end VerifiedLL1
