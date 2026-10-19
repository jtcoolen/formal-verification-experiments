import ProtSat.Examples

open ProtSat Term OneHot Bounded Attacker Encode Encoding Certificate Analyzer DPLL
namespace ProtSatReview
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def P : Protocol :=
  { roles := [{ acts := [.commit 0 (.agent 1) (.agent 0)] }],
    sessions := [{ role := 0, self := 0, peer := 1 }],
    agents := [0,1], nonceDomain := [0], compromised := [], secrets := [], auths := [{tag := 0}] }
def B : Bounds := { steps := 1, rounds := 0 }
def tr : List Ev := [.act 0 (.agent 0) 0]
def c := Examples.certOfTrace P tr
example : univClosedBool (shapeOf P B) P = true := by decide
example : checkCertificate P c = true := by decide
example : analyze P B = Verdict.safe := by
  have hu : univClosedBool (shapeOf P B) P = true := by decide
  have hn : dpll (encode P B) = none := by decide
  rw [analyze, if_neg (by simp [hu]), hn]
example : Attack P tr := by
  have h := checkCertificate_sound (P := P) c (by decide)
  simpa [c, Examples.certOfTrace_trace] using h
example : BoundedAttack P B := by
  refine ⟨certTrace c, certCfgs c, ⟨?_, by decide, ?_⟩, Or.inr ?_⟩
  · exact checkSteps_runs P c.steps (initCfg P) (by decide)
  · change ∀ C ∈ certCfgs c, cfgInUniverse C (univ P B) = true
    decide
  · exact (authBreakBool_iff P (certCfgs c) (certTrace c)).mp (by decide)
end ProtSatReview
