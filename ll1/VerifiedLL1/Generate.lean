/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.SelectedLC

/-!
# Phase 5.4 - checked generation

`Grammar.genTable` is unconditional: it writes an entry for every pair that selects a
production and silently keeps the first one when several do.  The LL(1) guarantee lives
in the theorems' hypotheses instead of in the API, so a caller who forgets to run
`ll1Check` gets a table that is still *sound* but no longer complete: the review artifact
`UncheckedGenerator.lean` shows `S -> a | ab` rejecting the valid word `ab`.

This module wraps the check and the generation in one function that cannot hand out a
bad table.  `Grammar.generate` either returns a table together with the certificate that
the grammar is LL(1), or it names two concrete distinct productions of one nonterminal
that both claim one lookahead:

* `generate_eq_ok_iff` : generate = ok genTable <-> ll1Check = true
* `generate_iff_Ll1`   : (exists M, generate = ok M) <-> G.Ll1
* `generate_conflict`  : generate = conflict A x r1 r2 -> G.Conflict A x
* `generate_not_ok`    : ll1Check = false -> generate names a conflict

Production identity is the right-hand side throughout, matching the rest of the
development: two alternatives with the same RHS are the same production.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

namespace Grammar

/-- **The result of checked generation**: either a table, or two distinct productions of
one nonterminal that both claim one lookahead. -/
inductive GenResult (G : Grammar T N) where
  | ok : Table T N -> GenResult G
  | conflict : (A : N) -> (x : LTok T) -> (rhs₁ rhs₂ : List (Sym T N)) -> GenResult G

end Grammar

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

namespace Grammar

variable {G : Grammar T N}

/-- **All conflicts, enumerated.**  For every pair `(A, x)` of the carrier, every pair of
distinct right-hand sides that `x` selects for `A`.  Finite, because the carrier and each
`selectRhs` list are finite. -/
def conflictList (G : Grammar T N) :
    List (N × LTok T × List (Sym T N) × List (Sym T N)) :=
  (FiniteEnum.elems (α := N × LTok T)).flatMap fun p =>
    (G.selectRhs p.1 p.2).flatMap fun a =>
      ((G.selectRhs p.1 p.2).filter fun b => !(a == b)).map fun b => (p.1, p.2, a, b)

/-- An entry of the conflict list really is a conflict. -/
theorem exists_conflict_of_mem {t : N × LTok T × List (Sym T N) × List (Sym T N)}
    (h : t ∈ G.conflictList) :
    ∃ A x r₁ r₂, t = (A, x, r₁, r₂) ∧ r₁ ∈ G.selectRhs A x ∧ r₂ ∈ G.selectRhs A x ∧
      r₁ ≠ r₂ := by
  unfold Grammar.conflictList at h
  obtain ⟨p, hp, hmid⟩ := List.mem_flatMap.mp h
  obtain ⟨a, ha, hinner⟩ := List.mem_flatMap.mp hmid
  obtain ⟨b, hb, heq⟩ := List.mem_map.mp hinner
  obtain ⟨h1, hne⟩ := List.mem_filter.mp hb
  refine ⟨p.1, p.2, a, b, heq.symm, ha, h1, ?_⟩
  intro hEq
  rw [hEq] at hne
  simp at hne

/-- The conflict list is empty exactly when the checker passes. -/
theorem conflictList_eq_nil_iff : G.conflictList = [] ↔ G.ll1Check = true := by
  constructor
  · intro hall
    refine (Grammar.ll1Check_iff G).mpr (fun A x hconf => ?_)
    obtain ⟨r₁, r₂, hp₁, hp₂, hne, s₁, s₂⟩ := hconf
    have h1 : r₁ ∈ G.selectRhs A x := (Grammar.mem_selectRhs G A x r₁).mpr ⟨hp₁, s₁⟩
    have h2 : r₂ ∈ G.selectRhs A x := (Grammar.mem_selectRhs G A x r₂).mpr ⟨hp₂, s₂⟩
    have hmem : (A, x, r₁, r₂) ∈ G.conflictList := by
      unfold Grammar.conflictList
      refine List.mem_flatMap.mpr ⟨(A, x), FiniteEnum.complete _,
        List.mem_flatMap.mpr ⟨r₁, h1, List.mem_map.mpr ⟨r₂,
          List.mem_filter.mpr ⟨h2, by simp [hne]⟩, rfl⟩⟩⟩
    rw [hall] at hmem
    exact absurd hmem (by simp)
  · intro hchk
    rw [List.eq_nil_iff_forall_not_mem]
    intro t ht
    obtain ⟨A, x, r₁, r₂, rfl, h1, h2, hne⟩ := exists_conflict_of_mem ht
    obtain ⟨c₁, s₁⟩ := (Grammar.mem_selectRhs G A x r₁).mp h1
    obtain ⟨c₂, s₂⟩ := (Grammar.mem_selectRhs G A x r₂).mp h2
    exact absurd ⟨r₁, r₂, c₁, c₂, hne, s₁, s₂⟩
      ((Grammar.ll1Check_iff G).mp hchk A x)

/-- **Checked generation.**  Hand out the generated table only when the conflict list is
empty; otherwise report the first conflict it finds. -/
def generate (G : Grammar T N) : GenResult G :=
  match G.conflictList with
  | [] => GenResult.ok G.genTable
  | (A, x, r₁, r₂) :: _ => GenResult.conflict A x r₁ r₂

/-- If the conflict list is empty, generation hands out the generated table. -/
theorem generate_eq_of_nil (hcl : G.conflictList = []) :
    G.generate = GenResult.ok G.genTable := by
  unfold Grammar.generate
  rw [hcl]

/-- Otherwise it reports the first conflict, which is a genuine one. -/
theorem generate_eq_of_cons {A x r₁ r₂ rest}
    (hcl : G.conflictList = (A, x, r₁, r₂) :: rest) :
    G.generate = GenResult.conflict A x r₁ r₂ := by
  unfold Grammar.generate
  rw [hcl]

/-- A nonempty conflict list carries a real conflict. -/
theorem conflict_of_cons {A x r₁ r₂ rest}
    (hcl : G.conflictList = (A, x, r₁, r₂) :: rest) :
    G.Conflict A x ∧ r₁ ≠ r₂ ∧ (A, r₁) ∈ G.productions ∧
      (A, r₂) ∈ G.productions := by
  have htm : (A, x, r₁, r₂) ∈ G.conflictList := by rw [hcl]; exact List.Mem.head _
  obtain ⟨A', x', r₁', r₂', heq, h1, h2, hne⟩ := exists_conflict_of_mem htm
  cases heq
  obtain ⟨c₁, s₁⟩ := (Grammar.mem_selectRhs G A x r₁).mp h1
  obtain ⟨c₂, s₂⟩ := (Grammar.mem_selectRhs G A x r₂).mp h2
  exact ⟨⟨r₁, r₂, c₁, c₂, hne, s₁, s₂⟩, hne, c₁, c₂⟩

/-- **Checked generation succeeds exactly when the checker does.** -/
theorem generate_eq_ok_iff :
    G.generate = GenResult.ok G.genTable ↔ G.ll1Check = true := by
  cases hcl : G.conflictList with
  | nil =>
      exact ⟨fun _ => conflictList_eq_nil_iff.mp hcl, fun _ => generate_eq_of_nil hcl⟩
  | cons t rest =>
      obtain ⟨A, x, r₁, r₂, heq, _, _, _⟩ := exists_conflict_of_mem
        (by rw [hcl]; exact List.Mem.head _)
      have hcl' : G.conflictList = (A, x, r₁, r₂) :: rest := by rw [hcl, heq]
      obtain ⟨hconf, _, _, _⟩ := conflict_of_cons hcl'
      refine ⟨fun h => absurd h (by simp [generate_eq_of_cons hcl']),
        fun h => False.elim ((Grammar.ll1Check_iff G).mp h A x hconf)⟩

/-- **Successful generation is equivalent to the LL(1) condition.** -/
theorem generate_iff_Ll1 : (∃ M, G.generate = GenResult.ok M) ↔ G.Ll1 := by
  constructor
  · rintro ⟨M, hM⟩
    cases hcl : G.conflictList with
    | nil =>
        exact (Grammar.ll1Check_iff G).mp (generate_eq_ok_iff.mp (generate_eq_of_nil hcl))
    | cons t rest =>
        obtain ⟨A, x, r₁, r₂, heq, _, _, _⟩ := exists_conflict_of_mem
          (by rw [hcl]; exact List.Mem.head _)
        have hcl' : G.conflictList = (A, x, r₁, r₂) :: rest := by rw [hcl, heq]
        exact absurd (hM.symm.trans (generate_eq_of_cons hcl')) (by simp)
  · intro hall
    exact ⟨G.genTable, generate_eq_ok_iff.mpr ((Grammar.ll1Check_iff G).mpr hall)⟩

/-- A successful generation returns the generated table. -/
theorem generate_ok_table (M : Table T N) (h : G.generate = GenResult.ok M) :
    M = G.genTable := by
  cases hcl : G.conflictList with
  | nil => exact GenResult.ok.inj (h.symm.trans (generate_eq_of_nil hcl))
  | cons t rest =>
      obtain ⟨A, x, r₁, r₂, heq, _, _, _⟩ := exists_conflict_of_mem
        (by rw [hcl]; exact List.Mem.head _)
      have hcl' : G.conflictList = (A, x, r₁, r₂) :: rest := by rw [hcl, heq]
      exact absurd (h.symm.trans (generate_eq_of_cons hcl')) (by simp)

/-- **A successful generation certifies the grammar and the table.** -/
theorem generate_ok (M : Table T N) (h : G.generate = GenResult.ok M) :
    G.Ll1 ∧ M.Sound G := by
  refine ⟨generate_iff_Ll1.mp ⟨M, h⟩, ?_⟩
  rw [generate_ok_table M h]
  exact Grammar.genTable_sound G

/-- **A failed generation names a real conflict.** -/
theorem generate_conflict {A : N} {x : LTok T} {r₁ r₂ : List (Sym T N)}
    (h : G.generate = GenResult.conflict A x r₁ r₂) :
    G.Conflict A x ∧ r₁ ≠ r₂ ∧ (A, r₁) ∈ G.productions ∧ (A, r₂) ∈ G.productions := by
  cases hcl : G.conflictList with
  | nil => exact absurd h (by simp [generate_eq_of_nil hcl])
  | cons t rest =>
      obtain ⟨A', x', r₁', r₂', heq, _, _, _⟩ := exists_conflict_of_mem
        (by rw [hcl]; exact List.Mem.head _)
      have hcl' : G.conflictList = (A', x', r₁', r₂') :: rest := by rw [hcl, heq]
      obtain ⟨hA, hx, hr1, hr2⟩ :=
        GenResult.conflict.inj ((generate_eq_of_cons hcl').symm.trans h)
      subst hA; subst hx; subst hr1; subst hr2
      exact conflict_of_cons hcl'

/-- **Generation is complete**: a grammar the checker rejects yields a reported conflict. -/
theorem generate_not_ok (h : G.ll1Check = false) :
    ∃ A x r₁ r₂, G.generate = GenResult.conflict A x r₁ r₂ := by
  cases hcl : G.conflictList with
  | nil =>
      have htrue : G.ll1Check = true := conflictList_eq_nil_iff.mp hcl
      exact absurd htrue (by intro hh; rw [hh] at h; simp at h)
  | cons t rest =>
      obtain ⟨A, x, r₁, r₂, heq, _, _, _⟩ := exists_conflict_of_mem
        (by rw [hcl]; exact List.Mem.head _)
      have hcl' : G.conflictList = (A, x, r₁, r₂) :: rest := by rw [hcl, heq]
      exact ⟨A, x, r₁, r₂, generate_eq_of_cons hcl'⟩
end Grammar

section Validation

open Sym

inductive GTok where
  | a | b
  deriving DecidableEq, Repr

inductive GVar where
  | S | U
  deriving DecidableEq, Repr

open GTok GVar in
instance : FiniteEnum GTok where
  elems := [a, b]
  complete := by intro t; cases t <;> simp

open GTok GVar in
instance : FiniteEnum GVar where
  elems := [S, U]
  complete := by intro v; cases v <;> simp

open GTok GVar

/-- A conflicted grammar: `S -> a` and `S -> a b` both claim the lookahead `a`. -/
def bad : Grammar GTok GVar where
  productions := [(S, [tok a]), (S, [tok a, tok b]), (U, [tok b])]
  start := S

/-- A clean grammar. -/
def good : Grammar GTok GVar where
  productions := [(S, [tok a]), (S, [tok b]), (U, [])]
  start := S

/-- Checked generation *rejects* the conflicted grammar and names the two productions. -/
theorem bad_generate : bad.generate =
    Grammar.GenResult.conflict S (LTok.tok a) [tok a] [tok a, tok b] := rfl

/-- So the reported pair is a genuine conflict. -/
theorem bad_conflict : bad.Conflict S (LTok.tok a) :=
  (Grammar.generate_conflict bad_generate).1

theorem bad_not_ll1 : bad.ll1Check = false := by decide

/-- Checked generation *accepts* the clean grammar and hands out the generated table. -/
theorem good_generate : good.generate = Grammar.GenResult.ok good.genTable := rfl

theorem good_ll1 : good.Ll1 := (Grammar.generate_iff_Ll1.mp ⟨_, good_generate⟩)

end Validation

end VerifiedLL1
