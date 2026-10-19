import VerifiedLL1
namespace VerifiedLL1.Review20261018
universe u v
variable {T : Type u} {N : Type v}
variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
variable {G : Grammar T N}

theorem generate_ok_correct (M : Table T N)
    (h : G.generate = Grammar.GenResult.ok M) : M.Correct G := by
  have hall : G.Ll1 := Grammar.generate_iff_Ll1.mp ⟨M, h⟩
  have hcheck := (Grammar.ll1Check_iff G).mpr hall
  rw [Grammar.generate_ok_table M h]
  exact Grammar.genTable_correct G hcheck

theorem generate_conflict_exact {A : N} {x : LTok T}
    {rhs₁ rhs₂ : List (Sym T N)}
    (h : G.generate = Grammar.GenResult.conflict A x rhs₁ rhs₂) :
    rhs₁ ≠ rhs₂ ∧ (A, rhs₁) ∈ G.productions ∧ (A, rhs₂) ∈ G.productions ∧
      G.Select A rhs₁ x ∧ G.Select A rhs₂ x := by
  cases hcl : G.conflictList with
  | nil =>
      have hn := Grammar.generate_eq_of_nil hcl
      exact False.elim (by rw [hn] at h; cases h)
  | cons t rest =>
      have hmem : t ∈ G.conflictList := by rw [hcl]; exact List.Mem.head _
      obtain ⟨B, y, r₁, r₂, heq, h₁, h₂, hne⟩ := Grammar.exists_conflict_of_mem hmem
      have hcl' : G.conflictList = (B, y, r₁, r₂) :: rest := by rw [hcl, heq]
      have hg := Grammar.generate_eq_of_cons hcl'
      have hh := Grammar.GenResult.conflict.inj (hg.symm.trans h)
      rcases hh with ⟨hA, hx, hr₁, hr₂⟩
      subst hA; subst hx; subst hr₁; subst hr₂
      obtain ⟨hp₁, hs₁⟩ := (Grammar.mem_selectRhs G B y r₁).mp h₁
      obtain ⟨hp₂, hs₂⟩ := (Grammar.mem_selectRhs G B y r₂).mp h₂
      exact ⟨hne, hp₁, hp₂, hs₁, hs₂⟩
#print axioms generate_ok_correct
#print axioms generate_conflict_exact
end VerifiedLL1.Review20261018
