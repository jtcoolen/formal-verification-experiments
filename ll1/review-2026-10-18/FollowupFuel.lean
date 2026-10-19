import VerifiedLL1.Fuel
open VerifiedLL1
universe u v
namespace FuelAudit
variable {T : Type u} {N : Type v}
variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

-- This is the original requested specification, independent of its implementation name.
def Target (G : Grammar T N) (fuelFor : List T → Nat) : Prop :=
  G.ll1Check = true →
    (∀ ws, Parser.parse G G.genTable (fuelFor ws) (ltoks ws ++ [LTok.eof]) ≠
      PRes.error ParseError.outOfFuel) ∧
    (∀ ws t, Parser.parse G G.genTable (fuelFor ws) (ltoks ws ++ [LTok.eof]) =
      PRes.ok t [LTok.eof] ↔
      Valid G t ∧ t.root? = some G.start ∧ Tree.yield t = ws)

theorem target_fully_proved (G : Grammar T N) : Target G G.fuelFor := by
  intro hall
  exact ⟨G.parseGenerated_ne_outOfFuel hall, G.parseGenerated_iff hall⟩

theorem actual_error_rejects (G : Grammar T N) (hall : G.ll1Check = true)
    (ws : List T) (e : ParseError T N) (h : G.parseGenerated ws = PRes.error e) :
    e ≠ ParseError.outOfFuel ∧ ¬ G.language ws := by
  constructor
  · intro heq
    subst heq
    exact G.parseGenerated_ne_outOfFuel hall ws h
  · intro hlang
    obtain ⟨ts,hv,hy⟩ := (G.language_iff_tree ws).mp hlang
    have hok := G.parseGenerated_imp_ok hall hv (by simp [Tree.root?]) hy
    rw [h] at hok
    cases hok

#print axioms target_fully_proved
#print axioms actual_error_rejects
#print VerifiedLL1.Grammar.parseGenerated_ne_outOfFuel
#check VerifiedLL1.Grammar.fuelFor_bound
#check VerifiedLL1.Grammar.parseGenerated_iff
#check VerifiedLL1.Grammar.decideMembership_iff
end FuelAudit
