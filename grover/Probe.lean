import Grover
open Complex Real
noncomputable section
example (x : ℝ) : star (Complex.cos ↑x) = Complex.cos ↑x := by simp
example (x : ℝ) : star (Complex.sin ↑x) = Complex.sin ↑x := by simp
example (x : ℝ) : star (Complex.cos ↑x) = Complex.cos ↑x := by
  rw [Complex.conj_cos]
#check @Complex.conj_cos
example (x : ℝ) : (Real.cos x : ℂ) = Complex.cos ↑x := by simp
example (x : ℝ) : star ↑(Real.cos x) = (Real.cos x : ℂ) := by simp
