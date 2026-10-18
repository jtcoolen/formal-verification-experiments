/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Exec

/-!
# Phase 5.7 - an executable fuel bound and a total generated parser

Phase 5.3 says no occurring nonterminal lies on a selected left-corner cycle.  This module
turns that into a *number*: a recursion-depth bound for the generated parser that holds on
every input, valid or not, and then an executable `fuelFor` and a `parseGenerated` wrapper
that never exhausts fuel.

## The counting argument

Fuel is the length of a call path, and every call on a path except the last one
*succeeded*: a failed subparse aborts its parent.  So along a path the input position never
moves backwards (Phase 5.6 `parseSym_ok_suffix`), and a step that does not move it descends
through an erasable prefix, i.e. along a *selected* edge at the current lookahead
(Phase 5.6 `selectedLC_of_empty_prefix_parse`, Phase 5.3 for the acyclicity).

Group the nonterminal expansions by the input position at which they happen.  Between two
position increases all expansions happen at one fixed lookahead, and the ones that do not
consume input form a selected chain; a chain from an occurring nonterminal cannot repeat a
node, so by the pigeonhole it has at most `n` nodes (`Grammar.chainBdd_universal`).

## The measure

With `n = G.numVars` (distinct nonterminals) and `W = G.maxRhsLen` (maximum production
width), a *symbol* call and a *forest* call at an input of length `l` are charged

    muS l k    = (l * (n + 2) + k) * (W + 1) + 1
    muF l kb m = (l * (n + 2) + kb) * (W + 1) + m + 1

`k` bounds the selected chains from the head nonterminal at the current lookahead; `kb`
bounds the chains from every symbol of the forest whose prefix inside the forest is
erasable - the other symbols are only reachable after a token has been consumed, so they
get the universal bound `n + 1` and a strictly shorter input.  Each parser step strictly
decreases the measure:

* an expansion `muS l kb` to `muF l (kb-1) |rhs|` costs one budget unit and gains at most
  `W + 1` blocks, which is why the production width appears;
* a sibling step that consumes nothing keeps `kb` and drops `m` by one;
* a sibling step that consumes a token drops `l` by at least one, and one input block
  `(n + 2) * (W + 1)` pays for resetting the budget to `n + 1`;
* a terminal match does not recurse.

Production width matters because `parseForest` spends one fuel unit per sibling as well as
per nesting level.

## The API

    Grammar.fuelFor        G ws = muF (ws.length + 1) (n + 1) 1
    Grammar.parseGenerated G ws = Parser.parse G G.genTable (fuelFor G ws) (ltoks ws ++ [eof])

`Grammar.fuelFor_bound` is the review's `FuelBoundTarget`: under `ll1Check = true` alone -
no `Reduced`, no `wellFormed` - the parser never exhausts fuel, and it succeeds exactly on
the valid start-rooted trees that yield the whole input.  The failing half is what makes
`parseGenerated` a decision procedure rather than only a recognizer.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v} {G : Grammar T N}

section Chains

/-- **A selected chain**: an explicit list of nonterminals, consecutive ones joined by a
selected left corner at a fixed lookahead.  Unlike `SelectedLCPath` it carries its own
length, which is what the pigeonhole needs. -/
inductive Grammar.SelChain {T : Type u} {N : Type v} (G : Grammar T N) (x : LTok T) :
    List N → Prop where
  | single : ∀ A, G.SelChain x [A]
  | cons : ∀ {A B : N} {rest : List N}, G.SelectedLeftCorner x A B → G.SelChain x (B :: rest) →
      G.SelChain x (A :: B :: rest)

/-- **Chain budget.**  `G.ChainBdd x A kb`: every selected chain at lookahead `x` that
starts at `A` has at most `kb` nodes. -/
def Grammar.ChainBdd {T : Type u} {N : Type v} (G : Grammar T N) (x : LTok T) (A : N)
    (kb : Nat) : Prop :=
  ∀ rest, G.SelChain x (A :: rest) → rest.length < kb

/-- The start symbol occurs: it occurs in the sentential form it *is*. -/
theorem Grammar.occurs_start (G : Grammar T N) : G.Occurs G.start :=
  ⟨[], [], by simpa using derives_refl [Sym.var G.start]⟩

/-- A selected edge preserves occurrence: a child of an occurring nonterminal occurs. -/
theorem Grammar.occurs_of_selectedLeftCorner {T : Type u} {N : Type v}
    (G : Grammar T N) {x : LTok T} {A B : N} (hocc : G.Occurs A)
    (h : G.SelectedLeftCorner x A B) : G.Occurs B := by
  obtain ⟨pre₀, post₀, hder⟩ := hocc
  obtain ⟨pre, post, hprod, _hsel, _hnul⟩ := h
  have h1 : Derives1 G ([] ++ [Sym.var A]) ([] ++ (pre ++ Sym.var B :: post) ++ []) :=
    Derives1.step (pre := []) (post := []) hprod
  have hstep : Derives G [Sym.var A] (pre ++ Sym.var B :: post) := by
    simpa using derives_single h1
  have hmid : Derives G [Sym.var G.start] (pre₀ ++ (pre ++ Sym.var B :: post) ++ post₀) :=
    derives_trans hder (derives_ctx hstep pre₀ post₀)
  refine ⟨pre₀ ++ pre, post ++ post₀, ?_⟩
  have hrew : pre₀ ++ pre ++ [Sym.var B] ++ (post ++ post₀) =
      pre₀ ++ (pre ++ Sym.var B :: post) ++ post₀ := by simp [List.append_assoc]
  rw [hrew]
  exact hmid

/-- Every node of a selected chain after the head occurs, provided the head does. -/
theorem chain_occurs {T : Type u} {N : Type v} {G : Grammar T N} {x : LTok T}
    {As : List N} (h : G.SelChain x As) :
    ∀ A rest, As = A :: rest → G.Occurs A → ∀ B ∈ rest, G.Occurs B := by
  induction h with
  | single =>
      intro A rest hEq _ B hB
      obtain ⟨rfl, hrest⟩ := List.cons.inj hEq
      subst hrest
      exact absurd hB (by simp)
  | @cons A' B' rest' hcorner hchain ih =>
      intro A rest hEq hocc C hC
      obtain ⟨rfl, hrest⟩ := List.cons.inj hEq
      subst hrest
      rcases List.mem_cons.mp hC with h1 | h2
      · subst h1
        exact G.occurs_of_selectedLeftCorner hocc hcorner
      · exact ih B' rest' rfl (G.occurs_of_selectedLeftCorner hocc hcorner) C h2

/-- A chain suffix is a selected path from the head. -/
theorem chain_path {T : Type u} {N : Type v} {G : Grammar T N} {x : LTok T}
    {As : List N} (h : G.SelChain x As) :
    ∀ A rest, As = A :: rest → ∀ B ∈ rest, G.SelectedLCPath x A B := by
  induction h with
  | single =>
      intro A rest hEq B hB
      obtain ⟨rfl, hrest⟩ := List.cons.inj hEq
      subst hrest
      exact absurd hB (by simp)
  | @cons A' B' rest' hcorner hchain ih =>
      intro A rest hEq C hC
      obtain ⟨rfl, hrest⟩ := List.cons.inj hEq
      subst hrest
      rcases List.mem_cons.mp hC with h1 | h2
      · subst h1
        exact Grammar.SelectedLCPath.single hcorner
      · exact selectedLCPath_trans (Grammar.SelectedLCPath.single hcorner)
          (ih B' rest' rfl C h2)

/-- **No repetition.**  Under LL(1) a selected chain that starts at an occurring
nonterminal is duplicate-free: a repeat would be a reachable selected cycle, which
Phase 5.3 excludes. -/
theorem chain_nodup {T : Type u} {N : Type v} (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N] (hall : G.Ll1)
    {x : LTok T} {As : List N} (h : G.SelChain x As) :
    ∀ A rest, As = A :: rest → G.Occurs A → (A :: rest).Nodup := by
  induction h with
  | single =>
      intro A rest hEq _
      obtain ⟨rfl, hrest⟩ := List.cons.inj hEq
      subst hrest
      exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | @cons A' B' rest' hcorner hchain ih =>
      intro A rest hEq hocc
      obtain ⟨rfl, hrest⟩ := List.cons.inj hEq
      subst hrest
      refine List.nodup_cons.mpr ⟨?_,
        ih B' rest' rfl (G.occurs_of_selectedLeftCorner hocc hcorner)⟩
      intro hmem
      rcases List.mem_cons.mp hmem with h1 | h2
      · subst h1
        exact Grammar.noSelectedLCCycle hall hocc x (Grammar.SelectedLCPath.single hcorner)
      · have hpath : G.SelectedLCPath x A' A' :=
          selectedLCPath_trans (Grammar.SelectedLCPath.single hcorner)
            (chain_path hchain B' rest' rfl A' h2)
        exact Grammar.noSelectedLCCycle hall hocc x hpath

/-- **Pigeonhole.**  A duplicate-free list included in a list is no longer
than that list. -/
theorem length_le_of_mem_of_nodup {α : Type _} [DecidableEq α] (l : List α) :
    ∀ (l' : List α), l'.Nodup → (∀ a ∈ l', a ∈ l) → l'.length ≤ l.length := by
  induction l with
  | nil =>
      intro l' _ hsub
      cases l' with
      | nil => simp
      | cons a as => exact absurd (hsub a (List.Mem.head _)) (by simp)
  | cons x xs ih =>
      intro l' hl' hsub
      by_cases hx : x ∈ l'
      · obtain ⟨l₁, l₂, hsplit⟩ := exists_split_of_mem x l' hx
        have hsplit' : l' = l₁ ++ x :: l₂ := by rw [hsplit, append_cons_eq]
        rw [hsplit'] at hl'
        obtain ⟨hn1, hn2, hdisj⟩ := List.nodup_append.mp hl'
        obtain ⟨hxl₂, hn3⟩ := List.nodup_cons.mp hn2
        have hxl₁ : ∀ a ∈ l₁, a ≠ x := fun a ha => hdisj a ha x (List.Mem.head _)
        have hnd' : (l₁ ++ l₂).Nodup :=
          List.nodup_append.mpr ⟨hn1, hn3, fun a ha b hb => hdisj a ha b (List.Mem.tail _ hb)⟩
        have hsub' : ∀ b ∈ l₁ ++ l₂, b ∈ xs := by
          intro b hb
          have hmem : b ∈ l' := by
            rw [hsplit']
            rcases List.mem_append.mp hb with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.Mem.tail _ h)
          rcases List.mem_cons.mp (hsub b hmem) with h1 | h2
          · rcases List.mem_append.mp hb with h | h
            · exact absurd h1 (hxl₁ b h)
            · exact absurd (h1 ▸ h) hxl₂
          · exact h2
        have := ih (l₁ ++ l₂) hnd' hsub'
        have hlen : l'.length = l₁.length + 1 + l₂.length := by
          rw [hsplit']
          simp [List.length_append]
          omega
        have hlen2 : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append
        have hlen3 : (x :: xs).length = xs.length + 1 := rfl
        omega
      · have hsub' : ∀ b ∈ l', b ∈ xs := by
          intro b hb
          rcases List.mem_cons.mp (hsub b hb) with h1 | h2
          · exact absurd (h1 ▸ hb) hx
          · exact h2
        have := ih l' hl' hsub'
        have hlen3 : (x :: xs).length = xs.length + 1 := rfl
        omega

/-- **The number of nonterminals.**  The enumeration may repeat elements, which only makes
the bound coarser. -/
def Grammar.numVars (G : Grammar T N) [FiniteEnum N] : Nat :=
  (FiniteEnum.elems (α := N)).length

/-- **The universal chain bound.**  Under LL(1), every selected chain from an occurring
nonterminal has at most §n + 1§ nodes, where §n§ is the size of the nonterminal enumeration. -/
theorem Grammar.chainBdd_universal (G : Grammar T N) [DecidableEq T] [DecidableEq N]
    [FiniteEnum T] [FiniteEnum N] (hall : G.Ll1) {x : LTok T} {A : N} (hocc : G.Occurs A) :
    G.ChainBdd x A (G.numVars + 1) := by
  intro rest hchain
  have hnd := chain_nodup G hall hchain A rest rfl hocc
  have hsub : ∀ C ∈ (A :: rest), C ∈ (FiniteEnum.elems (α := N)) := fun C _ =>
    FiniteEnum.complete C
  have hlen := length_le_of_mem_of_nodup (FiniteEnum.elems (α := N)) (A :: rest) hnd hsub
  have h1 : (A :: rest).length = rest.length + 1 := rfl
  rw [h1] at hlen
  unfold Grammar.numVars
  omega

end Chains

section Measures

/-- The maximum production width of `G`: the longest right-hand side, or `0` if `G` has no
productions. -/
def Grammar.maxRhsLen (G : Grammar T N) : Nat :=
  (G.productions.map fun p => p.2.length).foldl max 0

/-- The fold is at least its seed. -/
theorem le_foldl_max_seed : ∀ (l : List Nat) (acc : Nat), acc ≤ l.foldl max acc := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl acc
  | cons b bs ih =>
      intro acc
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (max acc b))

/-- Every element of a list is at most its `max`-fold. -/
theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat), ∀ a ∈ l, a ≤ l.foldl max acc := by
  intro l
  induction l with
  | nil => intro acc a h; exact absurd h (by simp)
  | cons b bs ih =>
      intro acc a h
      rcases List.mem_cons.mp h with h1 | h2
      · subst h1
        exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max_seed bs (max acc a))
      · exact ih (max acc b) a h2

theorem Grammar.le_maxRhsLen {A : N} {rhs : List (Sym T N)} (hp : (A, rhs) ∈ G.productions) :
    rhs.length ≤ G.maxRhsLen := by
  unfold Grammar.maxRhsLen
  have hmem : rhs.length ∈ G.productions.map fun p => p.2.length :=
    List.mem_map.mpr ⟨(A, rhs), hp, rfl⟩
  exact le_foldl_max _ 0 _ hmem

/-- The fuel a **symbol** call needs at input length `l` with chain budget `k`. -/
def Grammar.muS (G : Grammar T N) [FiniteEnum N] (l k : Nat) : Nat :=
  (l * (G.numVars + 2) + k) * (G.maxRhsLen + 1) + 1

/-- The fuel a **forest** call needs at input length `l`, head chain budget `kb` and `m`
symbols. -/
def Grammar.muF (G : Grammar T N) [FiniteEnum N] (l kb m : Nat) : Nat :=
  (l * (G.numVars + 2) + kb) * (G.maxRhsLen + 1) + m + 1

theorem Grammar.muF_succ (G : Grammar T N) [FiniteEnum N] (l kb m : Nat) :
    G.muF l kb (m + 1) = G.muF l kb m + 1 := by
  unfold Grammar.muF
  omega

/-- A forest call is at least as expensive as its head symbol call. -/
theorem Grammar.muF_ge_muS (G : Grammar T N) [FiniteEnum N] (l kb m : Nat) :
    G.muS l kb ≤ G.muF l kb m := by
  unfold Grammar.muF Grammar.muS
  omega

/-- A forest call has at least one fuel per symbol. -/
theorem Grammar.muF_ge_length (G : Grammar T N) [FiniteEnum N] (l kb m : Nat) :
    m + 1 ≤ G.muF l kb m := by
  unfold Grammar.muF
  omega

/-- Dropping the budget by one releases exactly one block. -/
theorem fuel_expansion {n W l kb r : Nat} (hr : r ≤ W) (hk : 1 ≤ kb) :
    (l * (n + 2) + (kb - 1)) * (W + 1) + r + 1 ≤ (l * (n + 2) + kb) * (W + 1) := by
  have h1 : l * (n + 2) + kb = (l * (n + 2) + (kb - 1)) + 1 := by omega
  have h2 : ((l * (n + 2) + (kb - 1)) + 1) * (W + 1) =
      (l * (n + 2) + (kb - 1)) * (W + 1) + (W + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [h1, h2]
  omega

/-- One input block is worth the universal budget plus the width of one production. -/
theorem fuel_shrink_aux {n W l kb m : Nat} (hl : 1 ≤ l) :
    ((l - 1) * (n + 2) + (n + 1)) * (W + 1) + m + 1 ≤
      (l * (n + 2) + kb) * (W + 1) + m + 1 := by
  have h1 : (l - 1) * (n + 2) + (n + 1) ≤ l * (n + 2) := by
    have h2 : (l - 1) + 1 = l := Nat.sub_add_cancel hl
    have h3 : ((l - 1) + 1) * (n + 2) = l * (n + 2) := by rw [h2]
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega
  have h4 : ((l - 1) * (n + 2) + (n + 1)) * (W + 1) ≤ (l * (n + 2)) * (W + 1) :=
    Nat.mul_le_mul_right _ h1
  have h5 : (l * (n + 2)) * (W + 1) ≤ (l * (n + 2) + kb) * (W + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  omega

/-- The block term is monotone in the input length. -/
theorem fuel_mono_aux {n W l₁ l₂ kb m : Nat} (hl : l₁ ≤ l₂) :
    (l₁ * (n + 2) + kb) * (W + 1) + m + 1 ≤ (l₂ * (n + 2) + kb) * (W + 1) + m + 1 := by
  have h1 : l₁ * (n + 2) ≤ l₂ * (n + 2) := Nat.mul_le_mul_right _ hl
  have h2 : l₁ * (n + 2) + kb ≤ l₂ * (n + 2) + kb := Nat.add_le_add_right h1 _
  have h3 : (l₁ * (n + 2) + kb) * (W + 1) ≤ (l₂ * (n + 2) + kb) * (W + 1) :=
    Nat.mul_le_mul_right _ h2
  omega

/-- An expansion step: the child forest fits in the fuel the symbol call had, provided the
budget drops by one and no right-hand side is wider than `W`. -/
theorem Grammar.muF_expansion (G : Grammar T N) [FiniteEnum N] (l kb r : Nat)
    (hr : r ≤ G.maxRhsLen) (hk : 1 ≤ kb) :
    G.muF l (kb - 1) r ≤ G.muS l kb - 1 := by
  unfold Grammar.muF Grammar.muS
  have h1 : (l * (G.numVars + 2) + kb) * (G.maxRhsLen + 1) + 1 - 1 =
      (l * (G.numVars + 2) + kb) * (G.maxRhsLen + 1) := by omega
  rw [h1]
  exact fuel_expansion hr hk

/-- A sibling step that consumed a token: one input block pays for the universal budget. -/
theorem Grammar.muF_shrink (G : Grammar T N) [FiniteEnum N] (l kb m : Nat) (hl : 1 ≤ l) :
    G.muF (l - 1) (G.numVars + 1) m ≤ G.muF l kb (m + 1) - 1 := by
  unfold Grammar.muF
  have h1 : (l * (G.numVars + 2) + kb) * (G.maxRhsLen + 1) + (m + 1) + 1 - 1 =
      (l * (G.numVars + 2) + kb) * (G.maxRhsLen + 1) + m + 1 := by omega
  rw [h1]
  exact fuel_shrink_aux hl

/-- The forest measure is monotone in the input length. -/
theorem Grammar.muF_mono (G : Grammar T N) [FiniteEnum N] {l₁ l₂ kb m : Nat}
    (hl : l₁ ≤ l₂) : G.muF l₁ kb m ≤ G.muF l₂ kb m := by
  unfold Grammar.muF
  exact fuel_mono_aux hl

/-- Any budget at least `n + 1` is a universal budget. -/
theorem Grammar.chainBdd_mono (G : Grammar T N) {x : LTok T} {A : N} {kb kb' : Nat}
    (h : G.ChainBdd x A kb) (hkb : kb ≤ kb') : G.ChainBdd x A kb' :=
  fun rest hchain => Nat.lt_of_lt_of_le (h rest hchain) hkb

end Measures

section Analysis

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- Every variable of `syms` occurs in a sentential form of `G`; terminals are ignored. -/
def Grammar.AllOccurs (G : Grammar T N) : List (Sym T N) → Prop := fun syms =>
  ∀ s ∈ syms, match s with
    | Sym.var A => G.Occurs A
    | Sym.tok _ => True

theorem Grammar.allOccurs_tail {s : Sym T N} {ss : List (Sym T N)}
    (h : G.AllOccurs (s :: ss)) : G.AllOccurs ss := fun t ht => h t (List.Mem.tail _ ht)

theorem Grammar.allOccurs_start (G : Grammar T N) : G.AllOccurs [Sym.var G.start] := by
  intro s hs
  have h1 : s = Sym.var G.start := by simpa using hs
  subst h1
  exact G.occurs_start

/-- The symbols of a production of an occurring nonterminal all occur. -/
theorem Grammar.allOccurs_of_production (G : Grammar T N) {A : N} (hocc : G.Occurs A)
    {rhs : List (Sym T N)} (hp : (A, rhs) ∈ G.productions) : G.AllOccurs rhs := by
  obtain ⟨pre₀, post₀, hder⟩ := hocc
  have h1 : Derives1 G ([] ++ [Sym.var A]) ([] ++ rhs ++ []) :=
    Derives1.step (pre := []) (post := []) hp
  have hstep : Derives G [Sym.var A] rhs := by simpa using derives_single h1
  have hbig : Derives G [Sym.var G.start] (pre₀ ++ rhs ++ post₀) :=
    derives_trans hder (derives_ctx hstep pre₀ post₀)
  intro s hs
  obtain ⟨l₁, l₂, hsplit⟩ := exists_split_of_mem s rhs hs
  cases s with
  | tok t => exact trivial
  | var B =>
      refine ⟨pre₀ ++ l₁, l₂ ++ post₀, ?_⟩
      have hrew : pre₀ ++ rhs ++ post₀ = pre₀ ++ l₁ ++ [Sym.var B] ++ (l₂ ++ post₀) := by
        rw [hsplit]
        simp [List.append_assoc, append_cons_eq]
      rw [← hrew]
      exact hbig

/-- **Syntactic erasure.**  `G.Erasable syms = true` when every symbol of `syms` is a
computed-nullable nonterminal; `Grammar.erasable_iff` says this is exactly `Derives syms []`. -/
def Grammar.Erasable (G : Grammar T N) : List (Sym T N) → Bool :=
  fun syms => syms.all (firstNul G)

theorem Grammar.erasable_iff (G : Grammar T N) (syms : List (Sym T N)) :
    G.Erasable syms = true ↔ Derives G syms [] := all_nul_iff G syms

theorem Grammar.erasable_nil (G : Grammar T N) : G.Erasable [] = true := by
  simp [Grammar.Erasable]

/-- **The budget invariant.**  Every variable of `syms` whose prefix *inside* `syms`
erases has chain budget `kb` at lookahead `x`.  A symbol whose prefix does not erase is
only reachable after a token has been consumed, so the invariant says nothing about it. -/
def Grammar.Budget (G : Grammar T N) (x : LTok T) (kb : Nat) (syms : List (Sym T N)) : Prop :=
  ∀ (pre : List (Sym T N)) (s : Sym T N) (post : List (Sym T N)),
    syms = pre ++ s :: post → G.Erasable pre = true →
    match s with
    | Sym.var A => G.ChainBdd x A kb
    | Sym.tok _ => True

/-- The head position has an erasable prefix, so it carries the budget. -/
theorem budget_head {A : N} {ss : List (Sym T N)} (h : G.Budget x kb (Sym.var A :: ss)) :
    G.ChainBdd x A kb :=
  h [] (Sym.var A) ss (by simp) G.erasable_nil

/-- Dropping an *erasable* head keeps the budget: the sibling step that consumed nothing. -/
theorem budget_tail {s : Sym T N} {ss : List (Sym T N)} (x : LTok T) (kb : Nat)
    (hs : G.Erasable [s] = true) (h : G.Budget x kb (s :: ss)) : G.Budget x kb ss := by
  intro pre t post hEq heras
  have hpre : G.Erasable ([s] ++ pre) = true := by
    have h1 : G.Erasable ([s] ++ pre) = (G.Erasable [s] && G.Erasable pre) := by
      simp [Grammar.Erasable, List.all_append]
    rw [h1, hs, heras]
    simp
  exact h ([s] ++ pre) t post (by rw [hEq]; simp [List.append_assoc]) hpre

/-- **An expansion drops the budget by one.**  A variable standing at an erasable position
of the right-hand side the table proposes is a *selected* child, so its chains are one
shorter than the parent's. -/
theorem budget_of_get {A : N} (x : LTok T) {rhs : List (Sym T N)}
    (hget : G.genTable.get A x = some rhs) (hkb : G.ChainBdd x A kb) :
    G.Budget x (kb - 1) rhs := by
  obtain ⟨hprod, hsel⟩ := Grammar.genTable_entry hget
  intro pre s post hEq heras
  cases s with
  | tok t => exact trivial
  | var B =>
      have hnul : Derives G pre [] := (Grammar.erasable_iff G pre).mp heras
      have hsel' : G.Select A (pre ++ Sym.var B :: post) x := by rw [← hEq]; exact hsel
      have hcorner : G.SelectedLeftCorner x A B :=
        ⟨pre, post, by rw [← hEq]; exact hprod, hsel', hnul⟩
      intro rest hchain
      have hbig := hkb (B :: rest) (Grammar.SelChain.cons hcorner hchain)
      have h1 : (B :: rest).length = rest.length + 1 := rfl
      omega

/-- The universal budget applies to every list of occurring variables. -/
theorem budget_of_allOccurs (hall : G.Ll1) (x : LTok T) {syms : List (Sym T N)}
    (hocc : G.AllOccurs syms) : G.Budget x (G.numVars + 1) syms := by
  intro pre s post hEq _
  cases s with
  | tok t => exact trivial
  | var A =>
      exact G.chainBdd_universal hall (hocc (Sym.var A) (by
        rw [hEq]
        exact List.mem_append_right _ (List.Mem.head _)))

end Analysis

section Fuel

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

open Parser

/-- A terminal call never runs out of fuel: it does not recurse. -/
theorem parseSym_tok_ne_fuel (a : T) (f : Nat) (input : List (LTok T)) :
    parseSym G.genTable f (Sym.tok a) input ≠ PRes.error ParseError.outOfFuel := by
  cases input with
  | nil => intro h; exact absurd h (by simp [Parser.parseSym])
  | cons x xs =>
      cases x with
      | eof => intro h; exact absurd h (by simp [Parser.parseSym])
      | tok b =>
          rw [parseSym_terminal]
          split <;> intro h <;> cases h

/-- With no input left a symbol call fails with `malformed`, never for want of fuel. -/
theorem parseSym_nil {M : Table T N} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N]
    {f : Nat} {s : Sym T N} (hf : 1 ≤ f) :
    parseSym M f s [] = PRes.error ParseError.malformed := by
  cases s with
  | tok a => cases f <;> simp [Parser.parseSym]
  | var A =>
      cases f with
      | zero => exact absurd hf (by omega)
      | succ f => simp [Parser.parseSym]

/-- With no input left a forest call fails at its first symbol, never for want of fuel. -/
theorem parseForest_nil_input {M : Table T N} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N]
    {f : Nat} (syms : List (Sym T N)) (hf : syms.length + 1 ≤ f) :
    parseForest M f syms [] ≠ PRes.error ParseError.outOfFuel := by
  cases f with
  | zero => exact absurd hf (by omega)
  | succ f =>
      cases syms with
      | nil => intro h; exact absurd h (by simp [Parser.parseForest])
      | cons s ss =>
          have h1 : (s :: ss).length = ss.length + 1 := rfl
          rw [h1] at hf
          rw [parseForest_cons, parseSym_nil (by omega : 1 ≤ f)]
          intro h
          exact absurd h (by simp [pbind])

/-- Sequencing two parser results runs out of fuel only if the first does, or if the
continuation applied to its value does. -/
theorem pbind_ne_fuel {r : PRes T N α} {f : α → List (LTok T) → PRes T N β}
    (hr : r ≠ PRes.error ParseError.outOfFuel)
    (hok : ∀ (a : α) (rest : List (LTok T)), r = PRes.ok a rest →
      f a rest ≠ PRes.error ParseError.outOfFuel) :
    pbind r f ≠ PRes.error ParseError.outOfFuel := by
  cases r with
  | ok a rest => simp only [pbind]; exact hok a rest rfl
  | error e =>
      intro hh
      exact hr (by rw [PRes.error.inj hh])

/-- **The fuel bound.**  For every fuel `f`, a forest call whose symbol list consists of
occurring variables, whose budget is `kb` at the current lookahead, and which satisfies
`f ≥ muF input.length kb syms.length`, does not run out of fuel; and the same for a symbol
call with `f ≥ muS l kb`.  Both halves are proved together by induction on `f`, and the
argument never assumes that the parse *succeeds*: it only uses that a call reached from a
successful one consumed a suffix of its input. -/
theorem fuel_not_outOfFuel (hall : G.Ll1) : ∀ (f : Nat),
    (∀ (syms : List (Sym T N)) (input : List (LTok T)) (x : LTok T) (xs : List (LTok T))
        (kb : Nat), input = x :: xs → G.AllOccurs syms → G.Budget x kb syms →
          f ≥ G.muF input.length kb syms.length →
          parseForest G.genTable f syms input ≠ PRes.error ParseError.outOfFuel) ∧
    (∀ (A : N) (x : LTok T) (xs : List (LTok T)) (kb : Nat),
        G.Occurs A → G.ChainBdd x A kb →
          f ≥ G.muS (x :: xs).length kb →
          parseSym G.genTable f (Sym.var A) (x :: xs) ≠ PRes.error ParseError.outOfFuel) := by
  intro f
  induction f with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro syms input x xs kb hinput _ _ hf
        have hge : 1 ≤ G.muF input.length kb syms.length := by
          unfold Grammar.muF
          omega
        have hbad : False := by omega
        exact hbad.elim
      · intro A x xs kb _ _ hf
        have hge : 1 ≤ G.muS (x :: xs).length kb := by
          unfold Grammar.muS
          omega
        have hbad : False := by omega
        exact hbad.elim
  | succ f ih =>
      refine ⟨?_, ?_⟩
      · -- ---- the forest call ----
        intro syms input x xs kb hinput hocc hbud hf
        subst hinput
        cases syms with
        | nil => intro h; exact absurd h (by simp [Parser.parseForest])
        | cons s ss =>
            have hsub : f ≥ G.muF (x :: xs).length kb ss.length := by
              have h1 : (s :: ss).length = ss.length + 1 := rfl
              rw [h1] at hf
              rw [G.muF_succ] at hf
              omega
            rw [parseForest_cons]
            have hsym : parseSym G.genTable f s (x :: xs)
                ≠ PRes.error ParseError.outOfFuel := by
              cases s with
              | tok a => exact parseSym_tok_ne_fuel a f (x :: xs)
              | var A =>
                  refine ih.2 A x xs kb ?_ ?_ ?_
                  · exact hocc (Sym.var A) (List.Mem.head _)
                  · exact budget_head hbud
                  · exact Nat.le_trans (G.muF_ge_muS _ _ _) hsub
            refine pbind_ne_fuel hsym ?_
            intro t rest hsymok
            refine pbind_ne_fuel ?_ (fun ts _ _ => by intro h; cases h)
            -- the tail forest call
            obtain ⟨mid, hmid⟩ : ∃ mid, (x :: xs) = mid ++ rest :=
              parseSym_ok_suffix hsymok
            obtain ⟨hmatch, hyield⟩ :=
              parseSym_sound (Grammar.genTable_sound G) f s (x :: xs) t rest hsymok
            have hss : G.AllOccurs ss := G.allOccurs_tail hocc
            cases rest with
            | nil =>
                exact parseForest_nil_input ss
                  (Nat.le_trans (G.muF_ge_length _ _ _) hsub)
            | cons x₂ xs₂ =>
                by_cases hsame : (x₂ :: xs₂) = x :: xs
                · -- nothing was consumed: the head erased, the budget carries over
                  have hlen0 : List.length (Tree.yield t) = 0 := by
                    have h2 : List.length (tokensOf (x :: xs)) =
                        List.length (Tree.yield t ++ tokensOf (x₂ :: xs₂)) := by rw [hyield]
                    have h3 : List.length (Tree.yield t ++ tokensOf (x₂ :: xs₂)) =
                        List.length (Tree.yield t) + List.length (tokensOf (x₂ :: xs₂)) :=
                      List.length_append
                    have h4 : List.length (tokensOf (x₂ :: xs₂)) =
                        List.length (tokensOf (x :: xs)) := by rw [hsame]
                    omega
                  have hnocon : Tree.yieldForest [t] = [] := by
                    rw [Tree.yieldForest_cons, Tree.yieldForest_nil,
                      (List.length_eq_zero_iff.mp hlen0)]
                    simp
                  have hs_er : G.Erasable [s] = true :=
                    (G.erasable_iff [s]).mpr (derives_nil_of_match hmatch hnocon)
                  exact ih.1 ss (x₂ :: xs₂) x₂ xs₂ kb rfl hss
                    (by
                      have hx2 : x₂ = x := (List.cons.inj hsame).1
                      subst hx2
                      exact budget_tail _ _ hs_er hbud)
                    (by rw [hsame]; exact hsub)
                · -- a token was consumed: the universal budget, a shorter input
                  have hlt : List.length (x₂ :: xs₂) + 1 ≤ List.length (x :: xs) := by
                    have hne : mid ≠ [] := by
                      intro hnil
                      rw [hnil, List.nil_append] at hmid
                      exact hsame hmid.symm
                    have h1 : List.length (x :: xs) =
                        List.length mid + List.length (x₂ :: xs₂) := by
                      rw [hmid, List.length_append]
                    have h2 : 1 ≤ List.length mid := by
                      cases mid with
                      | nil => exact absurd hne (by simp)
                      | cons a as => simp [List.length_cons]
                    omega
                  have hshrunk : G.muF (List.length (x₂ :: xs₂)) (G.numVars + 1) ss.length ≤
                      G.muF (List.length (x :: xs)) kb (ss.length + 1) - 1 := by
                    have h2 := G.muF_shrink (List.length (x :: xs)) kb ss.length
                      (by simp : 1 ≤ List.length (x :: xs))
                    exact Nat.le_trans (G.muF_mono (by omega)) h2
                  exact ih.1 ss (x₂ :: xs₂) x₂ xs₂ (G.numVars + 1) rfl hss
                    (budget_of_allOccurs hall x₂ hss)
                    (by rw [G.muF_succ] at *; omega)
      · -- ---- the symbol call ----
        intro A x xs kb hocc hkb hf
        rw [parseSym_var]
        cases hget : G.genTable.get A x with
        | none => intro h; cases h
        | some rhs =>
            obtain ⟨hprod, _hsel⟩ := Grammar.genTable_entry hget
            by_cases hk : kb = 0
            · have hbad : ([] : List N).length < kb := hkb [] (Grammar.SelChain.single A)
              rw [hk] at hbad
              exact absurd hbad (by simp)
            · have hk' : 1 ≤ kb := Nat.pos_of_ne_zero hk
              have hne : parseForest G.genTable f rhs (x :: xs)
                  ≠ PRes.error ParseError.outOfFuel :=
                ih.1 rhs (x :: xs) x xs (kb - 1) rfl
                  (G.allOccurs_of_production hocc hprod)
                  (budget_of_get x hget hkb)
                  (by
                    have := G.muF_expansion (List.length (x :: xs)) kb rhs.length
                      (G.le_maxRhsLen hprod) hk'
                    omega)
              cases hfor : parseForest G.genTable f rhs (x :: xs) with
              | ok ts rest => simp only [hfor]; intro h; cases h
              | error e =>
                  simp only [hfor]
                  intro h
                  exact hne (hfor.trans (by rw [PRes.error.inj h]))

end Fuel

section API

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The executable fuel chooser.**  Enough fuel for the start parser on the input `ws`,
whether or not `ws` is a word of the language. -/
def Grammar.fuelFor (G : Grammar T N) (ws : List T) : Nat :=
  G.muF (ws.length + 1) (G.numVars + 1) 1

/-- **The generated parser with automatic fuel.** -/
def Grammar.parseGenerated (G : Grammar T N) (ws : List T) : PRes T N (Tree T N) :=
  Parser.parse G G.genTable (G.fuelFor ws) (ltoks ws ++ [LTok.eof])

/-- The top-level `parse` runs out of fuel only if its forest call does. -/
theorem parse_ne_fuel {M : Table T N} {f : Nat} {input : List (LTok T)}
    (h : Parser.parseForest M f [Sym.var G.start] input ≠ PRes.error ParseError.outOfFuel) :
    Parser.parse G M f input ≠ PRes.error ParseError.outOfFuel := by
  intro hh
  cases hfor : Parser.parseForest M f [Sym.var G.start] input with
  | ok ts rest =>
      -- `parse` on a successful forest is either a success or a `trailing` error.
      have key : Parser.parse G M f input ≠ PRes.error ParseError.outOfFuel := by
        rw [Parser.parse, hfor]
        cases ts with
        | nil => simp
        | cons t ts' =>
            cases ts' with
            | cons y ys => simp
            | nil =>
                cases rest with
                | nil => simp
                | cons x rest' =>
                    cases rest' with
                    | cons b br => simp
                    | nil =>
                        cases x with
                        | tok c => simp
                        | eof => simp
      exact absurd hh key
  | error e =>
      have key : Parser.parse G M f input = PRes.error e := by
        simp [Parser.parse, hfor]
      rw [key] at hh
      exact h (by rw [hfor, PRes.error.inj hh])

/-- **No fuel exhaustion, ever**: the operational half of the review's request. -/
theorem Grammar.parseGenerated_ne_outOfFuel (hall : G.ll1Check = true) (ws : List T) :
    G.parseGenerated ws ≠ PRes.error ParseError.outOfFuel := by
  have hall' : G.Ll1 := (Grammar.ll1Check_iff G).mp hall
  unfold Grammar.parseGenerated
  refine parse_ne_fuel ?_
  cases ws with
  | nil =>
      exact (fuel_not_outOfFuel hall' (G.fuelFor [])).1 [Sym.var G.start] [LTok.eof]
        LTok.eof [] (G.numVars + 1) rfl (G.allOccurs_start)
        (budget_of_allOccurs hall' LTok.eof (G.allOccurs_start))
        (by simp [Grammar.fuelFor, Grammar.muF])
  | cons t vs =>
      exact (fuel_not_outOfFuel hall' (G.fuelFor (t :: vs))).1 [Sym.var G.start]
        (LTok.tok t :: (ltoks vs ++ [LTok.eof])) (LTok.tok t) (ltoks vs ++ [LTok.eof])
        (G.numVars + 1) rfl (G.allOccurs_start)
        (budget_of_allOccurs hall' (LTok.tok t) (G.allOccurs_start))
        (by simp [Grammar.fuelFor, Grammar.muF, List.length_append, List.length_cons,
          ltoks, List.length_map])

/-- **Soundness at the chosen fuel.** -/
theorem Grammar.parseGenerated_ok_imp {ws : List T} {t : Tree T N}
    (h : G.parseGenerated ws = PRes.ok t [LTok.eof]) :
    Valid G t ∧ t.root? = some G.start ∧ Tree.yield t = ws := by
  obtain ⟨hcall, _⟩ := parse_ok h
  obtain ⟨hmatch, hyield⟩ :=
    parseForest_sound (Grammar.genTable_sound G) (G.fuelFor ws) [Sym.var G.start]
      (ltoks ws ++ [LTok.eof]) [t] [LTok.eof] hcall
  obtain ⟨ts, rhs, r, hts, hp, hchild, hr⟩ := MatchList.eq_node_cons hmatch
  obtain ⟨h1, h2⟩ := List.cons.inj hts
  subst h1; subst h2
  refine ⟨Valid.mk hp hchild, by simp [Tree.root?], ?_⟩
  rw [Tree.yield_node]
  have := hyield
  simp [Tree.yieldForest_cons, Tree.yieldForest_nil, Tree.yield_node, List.append_nil,
    tokensOf_append, tokensOf_ltoks, tokensOf_cons_eof] at this
  exact this.symm

/-- If a top-level parse does not exhaust fuel at `fuel`, every larger fuel gives the same
result.  This is `parse_stable` read from the other side. -/
theorem parse_eq_of_not_outOfFuel {M : Table T N} {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {input : List (LTok T)}
    (h : Parser.parse G M fuel input ≠ PRes.error ParseError.outOfFuel) :
    Parser.parse G M fuel' input = Parser.parse G M fuel input :=
  parse_stable hle rfl h

/-- **Completeness at the chosen fuel.**  Phase 5.1 supplies *some* fuel; fuel stability
for non-`outOfFuel` outcomes lifts it to `fuelFor`. -/
theorem Grammar.parseGenerated_imp_ok (hall : G.ll1Check = true) {ws : List T}
    {t : Tree T N} (hv : Valid G t) (hr : t.root? = some G.start) (hy : Tree.yield t = ws) :
    G.parseGenerated ws = PRes.ok t [LTok.eof] := by
  obtain ⟨fuel, hrun⟩ :=
    Grammar.generated_parse_tree G ((Grammar.ll1Check_iff G).mp hall) hv hr
  rw [hy] at hrun
  have hne := G.parseGenerated_ne_outOfFuel hall ws
  have hbig := parse_stable (Nat.le_max_left fuel (G.fuelFor ws)) hrun
    (fun hh => by cases hh)
  have h2 := parse_eq_of_not_outOfFuel (Nat.le_max_right fuel (G.fuelFor ws)) hne
  rw [Grammar.parseGenerated, ← h2, hbig]

/-- **Exact-tree characterisation at the chosen fuel.** -/
theorem Grammar.parseGenerated_iff (hall : G.ll1Check = true) (ws : List T)
    (t : Tree T N) :
    G.parseGenerated ws = PRes.ok t [LTok.eof] ↔
      Valid G t ∧ t.root? = some G.start ∧ Tree.yield t = ws :=
  ⟨fun h => G.parseGenerated_ok_imp h,
    fun ⟨hv, hr, hy⟩ => G.parseGenerated_imp_ok hall hv hr hy⟩

/-- **The returned tree is the unique one.**  Combining the exact-tree characterisation
with Phase 5.1 unambiguity: at the chosen fuel the parser returns *the* valid start-rooted
tree that yields the input, if there is one. -/
theorem Grammar.parseGenerated_tree_unique (hall : G.ll1Check = true) {ws : List T}
    {t t' : Tree T N} (h : G.parseGenerated ws = PRes.ok t [LTok.eof])
    (hv : Valid G t') (hr : t'.root? = some G.start) (hy : Tree.yield t' = ws) : t = t' := by
  obtain ⟨ht, htr, hyt⟩ := G.parseGenerated_ok_imp h
  exact G.parseTree_unique ((Grammar.ll1Check_iff G).mp hall) ht hv htr hr
    (hyt.trans hy.symm)

/-- **The review's `FuelBoundTarget`, as a property of a fuel chooser.** -/
def Grammar.FuelBound (G : Grammar T N) (fuelFor : List T → Nat) : Prop :=
  G.ll1Check = true →
    (∀ ws, Parser.parse G G.genTable (fuelFor ws) (ltoks ws ++ [LTok.eof]) ≠
      PRes.error ParseError.outOfFuel) ∧
    (∀ ws t, Parser.parse G G.genTable (fuelFor ws) (ltoks ws ++ [LTok.eof]) =
      PRes.ok t [LTok.eof] ↔
      Valid G t ∧ t.root? = some G.start ∧ Tree.yield t = ws)

/-- **Stage 4.**  `Grammar.fuelFor` satisfies the target under `ll1Check = true` alone. -/
theorem Grammar.fuelFor_bound (hall : G.ll1Check = true) : G.FuelBound G.fuelFor :=
  fun _ =>
    ⟨fun ws => G.parseGenerated_ne_outOfFuel hall ws,
      fun ws t => G.parseGenerated_iff hall ws t⟩

/-- **Membership is decidable**: the language of an LL(1) grammar is a decision procedure. -/
def Grammar.decideMembership (G : Grammar T N) (ws : List T) : Bool :=
  match G.parseGenerated ws with
  | PRes.ok _ _ => true
  | PRes.error _ => false

/-- **The decision procedure is correct.**  Under `ll1Check = true`, `decideMembership ws` is
`true` exactly for the words of the language: the parser terminates on every input, so this
is a decision procedure and not merely a recognizer. -/
theorem Grammar.decideMembership_iff (hall : G.ll1Check = true) (ws : List T) :
    G.decideMembership ws = true ↔ G.language ws := by
  constructor
  · intro h
    unfold Grammar.decideMembership at h
    cases hgen : G.parseGenerated ws with
    | ok t rest =>
        obtain ⟨_, hrest⟩ := parse_ok hgen
        have h2 : G.parseGenerated ws = PRes.ok t [LTok.eof] := by rw [hgen, hrest]
        obtain ⟨hv, hr, hy⟩ := G.parseGenerated_ok_imp h2
        cases t with
        | leaf a => exact absurd hr (by simp [Tree.root?])
        | node A ts =>
            have hA : A = G.start := Option.some.inj hr
            subst hA
            exact (Grammar.language_iff_tree G ws).mpr ⟨ts, hv, hy⟩
    | error e => exact absurd h (by simp [hgen])
  · intro hlang
    obtain ⟨ts, hv, hy⟩ := (Grammar.language_iff_tree G ws).mp hlang
    have hok := G.parseGenerated_imp_ok hall hv (by simp [Tree.root?]) hy
    unfold Grammar.decideMembership
    rw [hok]

end API

end VerifiedLL1