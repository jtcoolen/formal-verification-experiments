/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Follow
import VerifiedLL1.Completeness

/-!
# Phase 5 — the LL(1) parser generator

## Contents

* `Select` / `selectTest` / `select_iff` — the `SELECT` set of a production, specified
  with `Derives` and computed from the Phase 4 analyses.
* `Conflict` / `Ll1` / `ll1Check` / `ll1Check_iff` — the LL(1) condition, and a decidable
  test for it; the generator refuses a conflicted grammar.
* `genTable` / `genTable_get` / `genTable_sound` — the generated table and its lookup.
* `select_of_derives` — the bridge between a real derivation and `SELECT`.
* `genTable_adequate`, `genTable_complete`, `genTable_correct` — a conflict-free grammar
  yields a table satisfying the *independent* Phase 2 correctness predicate.

## Why the bridge lemma is the heart of the proof

`Table.Correct` (Phase 2) is stated purely with `Derives`; `genTable` is built purely from
`FIRST`/`FOLLOW`.  The only place where the two worlds meet is

    Derives G (var A :: cont) (toks w)  ==>  the production of A that starts a derivation
                                           of w is selected by lookaheadOf w

which is `select_of_derives`: `FirstList.append_decomp` says a lookahead of `rhs ++ cont`
either comes from `rhs` (so it is in `FIRST(rhs)`) or `rhs` erases and it comes from
`cont` (so, because `var A :: cont` is reachable, it is in `FOLLOW(A)`).  Everything else
is bookkeeping around that fact.

## Where the hypotheses are used

* `Adequate`: the table proposes `rhs` for `(A, x)`; the derivation of the input uses
  *some* production `rhs'` of `A` (found by `derives_forest` + `MatchList.eq_node_cons`,
  so no leftmost-derivation reordering is needed); both are selected by `x`, so
  conflict-freeness forces `rhs = rhs'`.
* `Complete`: the production that works is selected by `x`, so it is the unique entry for
  `(A, x)`.
* Both need `G.Reachable (var A :: cont)`: the `FOLLOW` half of `SELECT` is only
  meaningful for continuations a parser can actually reach (see `Examples/Continuation.lean`).
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

section Specification

/-- **Specification.** `G.Select A rhs x`: the lookahead `x` tells the parser to expand
`A` with the production `A -> rhs`.  Classically,

    SELECT(A -> rhs) = (FIRST(rhs) without eof)  union  (if rhs erases then FOLLOW(A)).

The `isEof x = false` guard is what removes `eof` from the first component. -/
def Grammar.Select (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) : Prop :=
  (isEof x = false ∧ G.FirstList rhs x) ∨ (Derives G rhs [] ∧ G.FollowSym A x)

/-- **Specification.** `G.Conflict A x`: two *different* productions of `A` both claim the
lookahead `x`, so no deterministic table can answer `(A, x)`. -/
def Grammar.Conflict (G : Grammar T N) (A : N) (x : LTok T) : Prop :=
  ∃ rhs₁ rhs₂, (A, rhs₁) ∈ G.productions ∧ (A, rhs₂) ∈ G.productions ∧ rhs₁ ≠ rhs₂ ∧
    G.Select A rhs₁ x ∧ G.Select A rhs₂ x

/-- **The LL(1) condition**: no nonterminal/lookahead pair is conflicted. -/
def Grammar.Ll1 (G : Grammar T N) : Prop := ∀ (A : N) (x : LTok T), ¬ G.Conflict A x

end Specification

section SelectComputation

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- A list erases exactly when every symbol is computed-nullable. -/
theorem all_nul_iff (G : Grammar T N) (rhs : List (Sym T N)) :
    rhs.all (firstNul G) = true ↔ Derives G rhs [] := by
  constructor
  · intro h
    exact derives_nil_of_symbols rhs (fun s hs =>
      (symNull_iff G s).mp ((List.all_eq_true.mp h) s hs))
  · intro h
    have hc := (firstList_iff G rhs LTok.eof).mp h
    exact List.all_eq_true.mpr ((firstListTest_eof G.first (firstNul G) rhs).mp hc)

/-- The computed `SELECT` membership test. -/
def Grammar.selectTest (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) : Bool :=
  ((!isEof x && firstListTest G.first (firstNul G) rhs x) ||
    (rhs.all (firstNul G) && G.follow A x))

/-- **The `SELECT` computation is correct.** -/
theorem Grammar.select_iff (G : Grammar T N) (A : N) (rhs : List (Sym T N)) (x : LTok T) :
    G.selectTest A rhs x = true ↔ G.Select A rhs x := by
  constructor
  · intro h
    rcases Fixpoint.or_eq_true_iff.mp h with h | h
    · obtain ⟨hne, hf⟩ := Fixpoint.and_eq_true_iff.mp h
      exact Or.inl ⟨by simpa using hne, (firstList_iff G rhs x).mpr hf⟩
    · obtain ⟨hall, hfol⟩ := Fixpoint.and_eq_true_iff.mp h
      exact Or.inr ⟨(all_nul_iff G rhs).mp hall, (follow_iff G A x).mp hfol⟩
  · intro h
    rcases h with ⟨hne, hf⟩ | ⟨hr, hfol⟩
    · exact Fixpoint.or_eq_true_iff.mpr (Or.inl (Fixpoint.and_eq_true_iff.mpr
        ⟨by simpa using hne, (firstList_iff G rhs x).mp hf⟩))
    · exact Fixpoint.or_eq_true_iff.mpr (Or.inr (Fixpoint.and_eq_true_iff.mpr
        ⟨(all_nul_iff G rhs).mpr hr, (follow_iff G A x).mpr hfol⟩))

/-- The right-hand sides of `A` that the lookahead `x` selects. -/
def Grammar.selectRhs (G : Grammar T N) (A : N) (x : LTok T) : List (List (Sym T N)) :=
  (G.productions.filter fun pr => (pr.1 == A && G.selectTest A pr.2 x)).map Prod.snd

theorem Grammar.mem_selectRhs (G : Grammar T N) (A : N) (x : LTok T) (rhs : List (Sym T N)) :
    rhs ∈ G.selectRhs A x ↔ ((A, rhs) ∈ G.productions ∧ G.Select A rhs x) := by
  unfold Grammar.selectRhs
  constructor
  · intro h
    obtain ⟨pr, hpr, hEq⟩ := List.mem_map.mp h
    obtain ⟨hpp, hand⟩ := List.mem_filter.mp hpr
    obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
    obtain ⟨B, rhs'⟩ := pr
    have hAB : A = B := (eq_of_beq h1).symm
    have hrhs : rhs' = rhs := by simpa [Prod.snd] using hEq
    subst hrhs
    subst hAB
    exact ⟨hpp, (select_iff G A rhs' x).mp h2⟩
  · intro ⟨hpp, hsel⟩
    refine List.mem_map.mpr ⟨(A, rhs), List.mem_filter.mpr ⟨hpp,
      Fixpoint.and_eq_true_iff.mpr ⟨by simp, (select_iff G A rhs x).mpr hsel⟩⟩, rfl⟩

end SelectComputation

section Ll1Check

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The decidable LL(1) test.**  For every pair `(A, x)` all selected right-hand sides
agree; a pair that selects two different ones is a conflict the generator refuses. -/
def Grammar.ll1Check (G : Grammar T N) : Bool :=
  (FiniteEnum.elems (α := N × LTok T)).all fun p =>
    (G.selectRhs p.1 p.2).all fun a => (G.selectRhs p.1 p.2).all fun b => (a == b)

/-- **The LL(1) test is correct.** -/
theorem Grammar.ll1Check_iff (G : Grammar T N) : G.ll1Check = true ↔ G.Ll1 := by
  constructor
  · intro hall A x hconf
    obtain ⟨rhs₁, rhs₂, hp₁, hp₂, hne, s₁, s₂⟩ := hconf
    have h1 : rhs₁ ∈ G.selectRhs A x := (mem_selectRhs G A x rhs₁).mpr ⟨hp₁, s₁⟩
    have h2 : rhs₂ ∈ G.selectRhs A x := (mem_selectRhs G A x rhs₂).mpr ⟨hp₂, s₂⟩
    have htest := (List.all_eq_true.mp hall) (A, x) (FiniteEnum.complete _)
    have h1' := (List.all_eq_true.mp htest) rhs₁ h1
    have h2' := (List.all_eq_true.mp h1') rhs₂ h2
    exact hne (eq_of_beq h2')
  · intro hall
    show (FiniteEnum.elems (α := N × LTok T)).all _ = true
    rw [List.all_eq_true]
    intro p hp
    rw [List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro b hb
    by_cases hne : a = b
    · exact hne ▸ by simp
    · have hconf : G.Conflict p.1 p.2 := ⟨a, b,
        ((mem_selectRhs G p.1 p.2 a).mp ha).1,
        ((mem_selectRhs G p.1 p.2 b).mp hb).1, hne,
        ((mem_selectRhs G p.1 p.2 a).mp ha).2,
        ((mem_selectRhs G p.1 p.2 b).mp hb).2⟩
      exact absurd hconf (hall p.1 p.2)

end Ll1Check

section Bridge

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **The bridge lemma.**  If `var A :: cont` is a reachable stack and `A -> rhs` starts a
derivation of the remaining input `w`, then the first lookahead of `w` selects that
production.  This is the only place where the derivation-level semantics and the
`FIRST`/`FOLLOW` analysis are connected. -/
theorem Grammar.select_of_derives {G : Grammar T N} {A : N} {rhs cont : List (Sym T N)}
    (hR : G.Reachable (Sym.var A :: cont)) (_hp : (A, rhs) ∈ G.productions)
    (w : List T) (hder : Derives G (rhs ++ cont) (toks w)) :
    G.Select A rhs (lookaheadOf w) := by
  have hfollow : ∀ (x : LTok T), G.FirstList cont x → G.FollowSym A x := by
    intro x hx
    obtain ⟨pre, hpre⟩ := hR
    refine ⟨pre, cont, ?_, hx⟩
    rw [append_cons_eq]
    exact hpre
  cases w with
  | nil =>
    obtain ⟨hr, hc⟩ := derives_nil_append rhs cont hder
    exact Or.inr ⟨hr, hfollow LTok.eof hc⟩
  | cons t w' =>
    have hconcat : G.FirstList (rhs ++ cont) (LTok.tok t) := ⟨toks w', hder⟩
    rcases Grammar.FirstList.append_decomp rhs cont (LTok.tok t) hconcat with hf | hn
    · exact Or.inl ⟨by simp [isEof], hf⟩
    · exact Or.inr ⟨hn.1, hfollow (LTok.tok t) hn.2⟩

end Bridge

section Generation

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- The entry the generator writes for the pair `(A, x)`: the unique selected production,
or nothing at all if `x` selects no production of `A`. -/
def Grammar.genEntry (G : Grammar T N) (p : N × LTok T) :
    Option (N × (LTok T × List (Sym T N))) :=
  match p with
  | (A, x) => match G.selectRhs A x with
      | [] => none
      | rhs :: _ => some (A, (x, rhs))

/-- **The generated parsing table**: one entry per pair `(A, x)` that selects a
production.  Conflicts have already been excluded by `ll1Check`. -/
def Grammar.genTable (G : Grammar T N) : Table T N :=
  ⟨(FiniteEnum.elems (α := N × LTok T)).filterMap G.genEntry⟩

/-- Any entry the generator produces for `(B, y)` is indexed by `(B, y)`. -/
theorem Grammar.genEntry_shape (G : Grammar T N) (B : N) (y : LTok T)
    (e : N × (LTok T × List (Sym T N))) (h : G.genEntry (B, y) = some e) :
    ∃ rhs, e = (B, (y, rhs)) := by
  cases hsel : G.selectRhs B y with
  | nil => exact absurd h (by simp [Grammar.genEntry, hsel])
  | cons rhs rest =>
    have h2 : G.genEntry (B, y) = some (B, (y, rhs)) := by simp [Grammar.genEntry, hsel]
    rw [h2] at h
    exact ⟨rhs, (Option.some.inj h).symm⟩

/-- The entry generated for `(A, x)` passes the lookup test for `(A, x)`. -/
theorem Grammar.genEntry_match (G : Grammar T N) (A : N) (x : LTok T)
    (e : N × (LTok T × List (Sym T N))) (h : G.genEntry (A, x) = some e) :
    (e.1 == A && lbeq e.2.1 x) = true := by
  obtain ⟨rhs, rfl⟩ := genEntry_shape G A x e h
  exact Fixpoint.and_eq_true_iff.mpr ⟨by simp, by rw [lbeq_eq_iff]⟩

/-- An entry generated from any *other* pair fails the lookup test for `(A, x)`. -/
theorem Grammar.genEntry_not_match (G : Grammar T N) (A : N) (x : LTok T) (p : N × LTok T)
    (hp : p ≠ (A, x)) : ∀ e, G.genEntry p = some e → (e.1 == A && lbeq e.2.1 x) = false := by
  intro e he
  obtain ⟨B, y⟩ := p
  obtain ⟨rhs, he'⟩ := genEntry_shape G B y e he
  subst he'
  cases hmatch : (B == A && lbeq y x) with
  | true =>
    obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hmatch
    exact absurd (Prod.ext (eq_of_beq h1) (lbeq_eq_iff.mp h2)) hp
  | false => rfl

/-- Scanning the enumeration: the first entry matching the lookup for `(A, x)` is the one
generated from `(A, x)` itself; if the pair is absent, nothing matches. -/
theorem Grammar.genTable_find (G : Grammar T N) (A : N) (x : LTok T) :
    ∀ (l : List (N × LTok T)),
      (l.filterMap G.genEntry).find? (fun e => e.1 == A && lbeq e.2.1 x) =
        if (A, x) ∈ l then G.genEntry (A, x) else none := by
  intro l
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.filterMap_cons]
    by_cases hy : y = (A, x)
    · subst hy
      cases hgen : G.genEntry (A, x) with
      | none =>
        show (ys.filterMap G.genEntry).find? (fun e => e.1 == A && lbeq e.2.1 x) =
          if (A, x) ∈ (A, x) :: ys then none else none
        rw [ih]
        simp [hgen]
      | some e =>
        show (e :: ys.filterMap G.genEntry).find?
          (fun e' => e'.1 == A && lbeq e'.2.1 x) =
          if (A, x) ∈ (A, x) :: ys then some e else none
        have h1 : (e :: ys.filterMap G.genEntry).find?
            (fun e' => e'.1 == A && lbeq e'.2.1 x) = some e :=
          List.find?_cons_of_pos
            (p := fun (e' : N × (LTok T × List (Sym T N))) => e'.1 == A && lbeq e'.2.1 x)
            (genEntry_match G A x e hgen)
        have h2 : (if (A, x) ∈ (A, x) :: ys then some e else none) =
            (some e : Option (N × (LTok T × List (Sym T N)))) := by simp
        exact h1.trans h2.symm
    · have hmem : ((A, x) ∈ y :: ys ↔ (A, x) ∈ ys) := by
        constructor
        · intro hh
          rcases List.mem_cons.mp hh with heq | hym
          · exact absurd heq.symm hy
          · exact hym
        · intro hh
          exact List.Mem.tail _ hh
      have hn : ∀ e, G.genEntry y = some e → (e.1 == A && lbeq e.2.1 x) = false :=
        genEntry_not_match G A x y hy
      cases hgen : G.genEntry y with
      | none =>
        show (ys.filterMap G.genEntry).find? (fun e => e.1 == A && lbeq e.2.1 x) =
          if (A, x) ∈ y :: ys then G.genEntry (A, x) else none
        rw [ih]
        by_cases hm : (A, x) ∈ ys
        · rw [ite_eq_left hm, ite_eq_left ((hmem.mpr hm))]
        · rw [ite_eq_right hm, ite_eq_right (fun hh => hm (hmem.mp hh))]
      | some e =>
        show (e :: ys.filterMap G.genEntry).find?
          (fun e' => e'.1 == A && lbeq e'.2.1 x) =
          if (A, x) ∈ y :: ys then G.genEntry (A, x) else none
        rw [List.find?_cons_of_neg (by simpa using hn e hgen), ih]
        by_cases hm : (A, x) ∈ ys
        · rw [ite_eq_left hm, ite_eq_left (hmem.mpr hm)]
        · rw [ite_eq_right hm, ite_eq_right (fun hh => hm (hmem.mp hh))]

/-- **Lookup in the generated table.** -/
theorem Grammar.genTable_get (G : Grammar T N) (A : N) (x : LTok T) :
    G.genTable.get A x =
      match G.selectRhs A x with
      | [] => none
      | rhs :: _ => some rhs := by
  have hfind : (G.genTable.entries.find? (fun e => e.1 == A && lbeq e.2.1 x)) =
      G.genEntry (A, x) := by
    show ((FiniteEnum.elems (α := N × LTok T)).filterMap G.genEntry).find?
        (fun e => e.1 == A && lbeq e.2.1 x) = G.genEntry (A, x)
    rw [genTable_find G A x (FiniteEnum.elems (α := N × LTok T))]
    simp [FiniteEnum.complete]
  show (G.genTable.entries.find? (fun e => e.1 == A && lbeq e.2.1 x)).map (fun e => e.2.2) = _
  rw [hfind]
  cases hsel : G.selectRhs A x with
  | nil => simp [Grammar.genEntry, hsel]
  | cons rhs rest =>
    have h : G.genEntry (A, x) = some (A, (x, rhs)) := by simp [Grammar.genEntry, hsel]
    rw [h]
    rfl

/-- What a lookup can tell us: the answer is a production, and it is selected by `x`. -/
theorem Grammar.genTable_entry {G : Grammar T N} {A : N} {x : LTok T} {rhs : List (Sym T N)}
    (h : G.genTable.get A x = some rhs) :
    (A, rhs) ∈ G.productions ∧ G.Select A rhs x := by
  rw [genTable_get] at h
  cases hsel : G.selectRhs A x with
  | nil =>
    rw [hsel] at h
    exact absurd h (by simp)
  | cons rhs' rest =>
    rw [hsel] at h
    have hrhs : rhs' = rhs := by simpa using h
    have hmem : rhs' ∈ G.selectRhs A x := by rw [hsel]; exact List.Mem.head _
    obtain ⟨hpp, hsel'⟩ := (mem_selectRhs G A x rhs').mp hmem
    rw [← hrhs]
    exact ⟨hpp, hsel'⟩

/-- **Conflict-freeness makes the selected production unique.** -/
theorem Grammar.selectRhs_unique (G : Grammar T N) (hall : G.Ll1) (A : N) (x : LTok T)
    (a b : List (Sym T N)) (ha : a ∈ G.selectRhs A x) (hb : b ∈ G.selectRhs A x) :
    a = b := by
  by_cases hne : a = b
  · exact hne
  · obtain ⟨hp₁, s₁⟩ := (mem_selectRhs G A x a).mp ha
    obtain ⟨hp₂, s₂⟩ := (mem_selectRhs G A x b).mp hb
    have hconf : G.Conflict A x := ⟨a, b, hp₁, hp₂, hne, s₁, s₂⟩
    exact absurd hconf (hall A x)

/-- **The generated table is sound**: every entry names a production. -/
theorem Grammar.genTable_sound (G : Grammar T N) : G.genTable.Sound G := by
  intro A x rhs h
  exact (genTable_entry h).1

end Generation

section Adequacy

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **Adequacy of the generated table.**  Following the table never destroys a derivation:
the production the table proposes is the one the derivation had to use. -/
theorem Grammar.genTable_adequate (G : Grammar T N) (hall : G.ll1Check = true) :
    G.genTable.Adequate G := by
  intro A x rhs hget cont u v hR hlook hder
  obtain ⟨hrhs, hsel⟩ := genTable_entry hget
  -- the derivation of the input must start by expanding `A` with some production
  obtain ⟨ts, hm, hy⟩ := derives_forest hder
  cases ts with
  | nil => exact absurd hm (by intro h; cases h)
  | cons t ts' =>
    obtain ⟨ts₁, rhs', ts₂, ht, hp', hchild, hrest⟩ := MatchList.eq_node_cons hm
    have hy' : Tree.yieldForest ts₁ ++ Tree.yieldForest ts₂ = u ++ v := by
      rw [← hy, ht]
      simp [Tree.yieldForest_cons, Tree.yield_node]
    have hder' : Derives G (rhs' ++ cont) (toks (u ++ v)) := by
      have h1 : Derives G rhs' (toks (Tree.yieldForest ts₁)) := matchList_derives hchild
      have h2 : Derives G cont (toks (Tree.yieldForest ts₂)) := matchList_derives hrest
      have h3 := derives_append h1 h2
      rw [← toks_append, hy'] at h3
      exact h3
    -- that production is selected by the real lookahead
    have hsel' : G.Select A rhs' (lookaheadOf (u ++ v)) :=
      select_of_derives hR hp' (u ++ v) hder'
    have hmem : rhs' ∈ G.selectRhs A x :=
      (mem_selectRhs G A x rhs').mpr ⟨hp', hlook ▸ hsel'⟩
    have huni : rhs' = rhs :=
      selectRhs_unique G (ll1Check_iff G |>.mp hall) A x rhs' rhs hmem
        ((mem_selectRhs G A x rhs).mpr ⟨hrhs, hsel⟩)
    subst huni
    exact hder'

end Adequacy

section Completeness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **Completeness of the generated table.**  Whenever some production of `A` can start a
derivation of the remaining input, the table offers one that can. -/
theorem Grammar.genTable_complete (G : Grammar T N) (hall : G.ll1Check = true) :
    G.genTable.Complete G := by
  intro A cont u v hR hex
  obtain ⟨rhs, hrhs, hder⟩ := hex
  have hsel : G.Select A rhs (lookaheadOf (u ++ v)) :=
    select_of_derives hR hrhs (u ++ v) hder
  have hmem : rhs ∈ G.selectRhs A (lookaheadOf (u ++ v)) :=
    (mem_selectRhs G A (lookaheadOf (u ++ v)) rhs).mpr ⟨hrhs, hsel⟩
  cases hsel' : G.selectRhs A (lookaheadOf (u ++ v)) with
  | nil => exact absurd hmem (by rw [hsel']; simp)
  | cons rhs' rest =>
    have huni : rhs' = rhs :=
      selectRhs_unique G (ll1Check_iff G |>.mp hall) A (lookaheadOf (u ++ v)) rhs' rhs
        (by rw [hsel']; exact List.Mem.head _) hmem
    refine ⟨rhs, ?_, hder⟩
    rw [genTable_get, hsel', huni]

end Completeness

section Correctness

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- **Main theorem of Phase 5.**  When the conflict check passes, the generated table
satisfies the independent Phase 2 correctness predicate: it is sound, adequate and
complete for the grammar. -/
theorem Grammar.genTable_correct (G : Grammar T N) (hall : G.ll1Check = true) :
    G.genTable.Correct G :=
  ⟨genTable_sound G, genTable_adequate G hall, genTable_complete G hall⟩

end Correctness

end VerifiedLL1
