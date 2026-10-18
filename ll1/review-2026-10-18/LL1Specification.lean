/-
Review artifact, 18 October 2026.

ClassicalLL1 is independent of FIRST, FOLLOW, SELECT, tables and parsing.
The two implication theorems below are proved. The propositions named Target
describe further work; their definitions do not establish those propositions.

Reference: Wilhelm, Seidl and Hack, Compiler Design, chapter 3,
printed pages 62 and 66, definition and Theorem 3.3.3:
https://compilers.cs.uni-saarland.de/teaching/cc/2011/book/cha3.pdf
-/
import VerifiedLL1
namespace VerifiedLL1
universe u v
variable {T : Type u} {N : Type v}
/-- One-token determinacy at a common reachable leftmost configuration. -/
def Grammar.ClassicalLL1 (G : Grammar T N) : Prop :=
  ∀ (pre w₁ w₂ : List T) (A : N) (cont rhs₁ rhs₂ : List (Sym T N)),
    LeftDerives G [Sym.var G.start] (toks pre ++ Sym.var A :: cont) →
    (A, rhs₁) ∈ G.productions → (A, rhs₂) ∈ G.productions →
    LeftDerives G (rhs₁ ++ cont) (toks w₁) →
    LeftDerives G (rhs₂ ++ cont) (toks w₂) →
    lookaheadOf w₁ = lookaheadOf w₂ → rhs₁ = rhs₂

theorem Grammar.classicalLL1_of_ll1 (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hall : G.Ll1) : G.ClassicalLL1 := by
  intro pre w₁ w₂ A cont rhs₁ rhs₂ hreach hp₁ hp₂ hd₁ hd₂ hlook
  have hR : G.Reachable (Sym.var A :: cont) :=
    ⟨toks pre, leftDerives_imp_derives hreach⟩
  have hs₁ := Grammar.select_of_derives hR hp₁ w₁ (leftDerives_imp_derives hd₁)
  have hs₂ := Grammar.select_of_derives hR hp₂ w₂ (leftDerives_imp_derives hd₂)
  by_cases h : rhs₁ = rhs₂
  · exact h
  · exact False.elim (hall A (lookaheadOf w₁) ⟨rhs₁, rhs₂, hp₁, hp₂, h, hs₁, hlook.symm ▸ hs₂⟩)

theorem Grammar.classicalLL1_of_ll1Check (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (hall : G.ll1Check = true) : G.ClassicalLL1 :=
  G.classicalLL1_of_ll1 ((Grammar.ll1Check_iff G).mp hall)

/-- Proposed characterization theorem. The reverse implication is not proved here. -/
def Grammar.ClassicalLL1CharacterizationTarget (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N] : Prop :=
  G.Reduced → (G.ll1Check = true ↔ G.ClassicalLL1)

/-- Proposed operational specification for a supplied executable fuel chooser.
Neither an executable fuel chooser nor this property is established here.
An input-only bound must work on invalid words too. Exact-tree completeness is
retained, rather than requiring only that some tree be returned on valid words. -/
def Grammar.FuelBoundTarget (G : Grammar T N)
    [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]
    (fuelFor : List T → Nat) : Prop :=
  G.ll1Check = true →
    (∀ ws, Parser.parse G G.genTable (fuelFor ws) (ltoks ws ++ [LTok.eof]) ≠
      PRes.error ParseError.outOfFuel) ∧
    (∀ ws t, Parser.parse G G.genTable (fuelFor ws) (ltoks ws ++ [LTok.eof]) =
      PRes.ok t [LTok.eof] ↔
      Valid G t ∧ t.root? = some G.start ∧ Tree.yield t = ws)

#print axioms Grammar.classicalLL1_of_ll1
#print axioms Grammar.classicalLL1_of_ll1Check
end VerifiedLL1
