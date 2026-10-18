/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Classical
import VerifiedLL1.SelectedLC

/-!
# Phase 5.6 - parser execution invariants

The operational theorem the review asks for has two halves.  This module proves the first
half: the invariants every recursive call of the table-driven parser maintains.  They hold
for *any* execution, successful or not, and no fuel choice is assumed.

* **Reachable context** (`parseForest_reachable_suffix`, `reachable_of_table_entry`): the
  parser only ever asks about suffixes of a sentential form.  Sibling steps take suffixes
  (`Grammar.reachable_tail`); expansion steps rewrite a reachable stack top by a production
  (`Grammar.reachable_of_derives`).
* **Successful subparses leave a suffix** (`parseForest_ok_suffix`,
  `parseSym_ok_suffix`): the remaining input of a successful subparse is a suffix of the
  input it was given - the parser never reorders or invents tokens.  No soundness hypothesis
  is needed: it is a property of the interpreter's structure.
* **Non-consuming descent is a selected edge** (`selectedLC_of_match_child`): if the table
  expands `A` to `alpha B beta` at lookahead `x` and the prefix `alpha` is matched by a
  forest with empty yield, then `A -> alpha B beta` is a *selected* left corner at `x`.
  Together with Phase 5.3 - no reachable selected cycle - this is the reason the parser
  cannot loop without consuming input, and it is the shape a fuel bound is built from.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1
variable {T : Type u} {N : Type v} {G : Grammar T N}

section Context

variable [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] {M : Table T N}

/-- Every suffix of a reachable symbol list is reachable: a sibling step preserves the
invariant. -/
theorem parseForest_reachable_suffix {ss : List (Sym T N)} :
    ∀ (syms : List (Sym T N)), G.Reachable syms → (∃ mid, syms = mid ++ ss) → G.Reachable ss := by
  intro syms
  induction syms with
  | nil =>
      intro hR hsub
      cases ss with
      | nil => exact hR
      | cons a as =>
          obtain ⟨mid, hmid⟩ := hsub
          cases mid with
          | nil => exact absurd hmid (by simp [List.cons_append])
          | cons m rest => exact absurd hmid (by simp [List.cons_append])
  | cons s rest ih =>
      intro hR hsub
      obtain ⟨mid, hmid⟩ := hsub
      cases mid with
      | nil =>
          simp at hmid
          subst hmid
          exact hR
      | cons m mid' =>
          obtain ⟨h1, h2⟩ := List.cons.inj hmid
          subst h1
          exact ih (Grammar.reachable_tail hR) ⟨mid', h2⟩

/-- The right-hand side the table proposes for a reachable stack top is again reachable:
an expansion step preserves the invariant. -/
theorem reachable_of_table_entry {A : N} {cont : List (Sym T N)}
    (hR : G.Reachable (Sym.var A :: cont)) {x : LTok T} {rhs : List (Sym T N)}
    (hM : M.Sound G) (hget : M.get A x = some rhs) : G.Reachable (rhs ++ cont) := by
  obtain ⟨pre, hpre⟩ := hR
  have hstep : Derives G (Sym.var A :: cont) (rhs ++ cont) :=
    derives_single (Derives1.step (pre := []) (post := cont) (hM A x rhs hget))
  exact ⟨pre, derives_trans hpre (derives_prefix hstep pre)⟩

end Context

section Suffix

open Parser

variable [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] {M : Table T N}

/-- **A successful subparse leaves a suffix of its input.**  The two statements are proved
together by induction on the fuel; no table property is used. -/
theorem parse_ok_suffix : ∀ fuel : Nat,
    (∀ (syms : List (Sym T N)) (input : List (LTok T)) (ts : List (Tree T N))
        (rest : List (LTok T)),
        parseForest M fuel syms input = PRes.ok ts rest → ∃ mid, input = mid ++ rest) ∧
    (∀ (s : Sym T N) (input : List (LTok T)) (t : Tree T N) (rest : List (LTok T)),
        parseSym M fuel s input = PRes.ok t rest → ∃ mid, input = mid ++ rest) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro syms input ts rest h
        cases syms <;> exact absurd h (by simp [parseForest])
      · intro s input t rest h
        cases s with
        | tok a =>
            cases input with
            | nil => exact absurd h (by simp [parseSym])
            | cons x xs =>
                cases x with
                | eof => exact absurd h (by simp [parseSym])
                | tok b =>
                    rw [parseSym_terminal] at h
                    split at h
                    · cases h; exact ⟨[LTok.tok b], rfl⟩
                    · exact absurd h (by simp)
        | var A =>
            exact absurd h (by
              intro hh
              have hz : parseSym M 0 (Sym.var A) input =
                  PRes.error ParseError.outOfFuel := rfl
              rw [hz] at hh
              cases hh)
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · intro syms input ts rest h
        cases syms with
        | nil =>
            rw [parseForest_nil] at h
            obtain ⟨h1, h2⟩ := PRes.ok.inj h
            subst h1; subst h2
            exact ⟨[], rfl⟩
        | cons s ss =>
            rw [parseForest_cons] at h
            obtain ⟨t, r1, ht, hfor⟩ := pbind_ok h
            obtain ⟨us, r2, h1, h2⟩ := pbind_ok hfor
            cases h2
            obtain ⟨m1, hm1⟩ := ih.2 s input t r1 ht
            obtain ⟨m2, hm2⟩ := ih.1 ss r1 us rest h1
            exact ⟨m1 ++ m2, by rw [hm1, hm2]; simp [List.append_assoc]⟩
      · intro s input t rest h
        cases s with
        | tok a =>
            have h' : parseSym M fuel (Sym.tok a) input = PRes.ok t rest := by
              rw [parseSym_tok_fuel (a := a) (input := input) (f := fuel) (f' := fuel + 1)]
              exact h
            exact ih.2 (Sym.tok a) input t rest h'
        | var A =>
            cases fuel with
            | zero =>
                cases input with
                | nil => exact absurd h (by simp [parseSym])
                | cons x xs =>
                    rw [parseSym_var] at h
                    cases hget : M.get A x with
                    | none => rw [hget] at h; exact absurd h (by simp)
                    | some rhs =>
                        simp only [hget] at h
                        have h0 : parseForest M 0 rhs (x :: xs) =
                            PRes.error ParseError.outOfFuel := rfl
                        cases hfor : parseForest M 0 rhs (x :: xs) with
                        | ok ts r =>
                            rw [h0] at hfor
                            exact absurd hfor (by intro hh; cases hh)
                        | error e => rw [hfor] at h; exact absurd h (by simp)
            | succ f =>
                cases input with
                | nil => exact absurd h (by simp [parseSym])
                | cons x xs =>
                    rw [parseSym_var] at h
                    cases hget : M.get A x with
                    | none => rw [hget] at h; exact absurd h (by simp)
                    | some rhs =>
                        simp only [hget] at h
                        cases hfor : parseForest M (f + 1) rhs (x :: xs) with
                        | ok ts r =>
                            rw [hfor] at h
                            obtain ⟨_, hr⟩ := PRes.ok.inj h
                            obtain ⟨mid, hmid⟩ := ih.1 rhs (x :: xs) ts r hfor
                            subst hr
                            exact ⟨mid, hmid⟩
                        | error e => rw [hfor] at h; exact absurd h (by simp)

theorem parseForest_ok_suffix {fuel : Nat} {syms : List (Sym T N)} {input : List (LTok T)}
    {ts : List (Tree T N)} {rest : List (LTok T)}
    (h : parseForest M fuel syms input = PRes.ok ts rest) :
    ∃ mid, input = mid ++ rest := (parse_ok_suffix fuel).1 syms input ts rest h

theorem parseSym_ok_suffix {fuel : Nat} {s : Sym T N} {input : List (LTok T)}
    {t : Tree T N} {rest : List (LTok T)}
    (h : parseSym M fuel s input = PRes.ok t rest) : ∃ mid, input = mid ++ rest :=
  (parse_ok_suffix fuel).2 s input t rest h

end Suffix

section Descent

open Parser

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- A forest with empty yield matches an erasable symbol list. -/
theorem derives_nil_of_match {syms : List (Sym T N)} {ts : List (Tree T N)}
    (hm : MatchList G syms ts) (hy : Tree.yieldForest ts = []) : Derives G syms [] := by
  have h := matchList_derives hm
  rw [hy] at h
  exact h

/-- **Non-consuming descent follows a selected edge.**  The table expands `A` to
`alpha B beta` at lookahead `x`, and the prefix `alpha` is parsed successfully without
consuming any input, with an empty-yield forest - so the parse reaches `B` at the same
lookahead, and the edge is a selected left corner at `x`. -/
theorem selectedLC_of_empty_prefix_parse {A B : N} {x : LTok T} {xs : List (LTok T)}
    {pre post : List (Sym T N)} {ts_pre : List (Tree T N)} (f : Nat)
    (hget : G.genTable.get A x = some (pre ++ Sym.var B :: post))
    (hrun : parseForest G.genTable f pre (x :: xs) = PRes.ok ts_pre (x :: xs))
    (hyield : Tree.yieldForest ts_pre = []) : G.SelectedLeftCorner x A B := by
  obtain ⟨hprod, hsel⟩ := Grammar.genTable_entry hget
  obtain ⟨hmatch, _⟩ := parseForest_sound (Grammar.genTable_sound G) f pre (x :: xs)
    ts_pre (x :: xs) hrun
  exact ⟨pre, post, hprod, hsel, derives_nil_of_match hmatch hyield⟩

/-- The purely relational form of the same fact. -/
theorem selectedLC_of_match_child {A B : N} {x : LTok T}
    {pre post : List (Sym T N)} {ts_pre : List (Tree T N)}
    (hget : G.genTable.get A x = some (pre ++ Sym.var B :: post))
    (hmatch : MatchList G pre ts_pre)
    (hyield : Tree.yieldForest ts_pre = []) : G.SelectedLeftCorner x A B := by
  obtain ⟨hprod, hsel⟩ := Grammar.genTable_entry hget
  exact ⟨pre, post, hprod, hsel, derives_nil_of_match hmatch hyield⟩
end Descent

end VerifiedLL1
