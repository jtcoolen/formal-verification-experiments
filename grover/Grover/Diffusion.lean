/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 2 (part 2): the diffusion operator and the Grover iteration

For the uniform starting state `s = state θ` of a search over `N` items the diffusion
(reflection-about-the-mean) operator is `D = 2 |s⟩⟨s| - I`; in the reduced model the outer
product `|s⟩⟨s|` is `Matrix.vecMulVec s s`.

The central result of this file is `groverIter_eq_rot`: the product `G = D * O` — oracle first,
then diffusion — is *exactly* the rotation `rot (2 * θ)`.  `G` is defined as that product; the
rotation formula is derived from the definitions of `D` and `O`, never assumed.
-/
import Grover.Oracle

open Matrix

noncomputable section

namespace Grover

/-- The reflection `D = 2 |s⟩⟨s| - I` about the uniform state `s = state θ`. -/
def diffusion (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 : ℝ) • Matrix.vecMulVec (state θ) (state θ) - 1

/-- One Grover iteration: apply the phase oracle, then the diffusion operator. -/
def groverIter (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diffusion θ * phaseOracle

section Diffusion

variable (θ : ℝ)

@[simp] theorem diffusion_00 : diffusion θ 0 0 = 2 * Real.sin θ * Real.sin θ - 1 := by
  simp [diffusion, Matrix.vecMulVec_apply]
  ring

@[simp] theorem diffusion_01 : diffusion θ 0 1 = 2 * Real.sin θ * Real.cos θ := by
  simp [diffusion, Matrix.vecMulVec_apply]
  ring

@[simp] theorem diffusion_10 : diffusion θ 1 0 = 2 * Real.sin θ * Real.cos θ := by
  simp [diffusion, Matrix.vecMulVec_apply]
  ring

@[simp] theorem diffusion_11 : diffusion θ 1 1 = 2 * Real.cos θ * Real.cos θ - 1 := by
  simp [diffusion, Matrix.vecMulVec_apply]
  ring

/-- The diffusion operator in closed form. -/
theorem diffusion_eq :
    diffusion θ = !![- Real.cos (2 * θ), Real.sin (2 * θ);
                      Real.sin (2 * θ), Real.cos (2 * θ)] := by
  have hsin : 2 * Real.sin θ * Real.cos θ = Real.sin (2 * θ) := (Real.sin_two_mul θ).symm
  have hcos : 2 * Real.cos θ * Real.cos θ - 1 = Real.cos (2 * θ) := by
    rw [Real.cos_two_mul]; ring
  have hcos' : 2 * Real.sin θ * Real.sin θ - 1 = -Real.cos (2 * θ) := by
    have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [Real.cos_two_mul]
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hsin, hcos, hcos']

theorem diffusion_mulVec_apply (x : State) :
    diffusion θ *ᵥ x
      = ![- Real.cos (2 * θ) * x 0 + Real.sin (2 * θ) * x 1,
          Real.sin (2 * θ) * x 0 + Real.cos (2 * θ) * x 1] := by
  rw [diffusion_eq, mulVec_fin_two]
  simp

/-- The diffusion operator is orthogonal. -/
theorem diffusion_orthogonal : diffusion θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [diffusion_eq, Matrix.mem_orthogonalGroup_iff']
  have h : Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * θ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, transpose_apply, one_apply, Fin.sum_univ_two, neg_mul, mul_neg]
  · nlinarith [h]
  · nlinarith [h]
  · nlinarith [h]
  · nlinarith [h]

/-- The diffusion operator preserves the squared norm. -/
theorem normSq_diffusion_mulVec (x : State) : normSq (diffusion θ *ᵥ x) = normSq x := by
  rw [diffusion_mulVec_apply, normSq_apply, normSq_apply]
  simp only [cons_val_zero, cons_val_one, cons_val_succ]
  have key : (-Real.cos (2 * θ) * x 0 + Real.sin (2 * θ) * x 1) ^ 2
      + (Real.sin (2 * θ) * x 0 + Real.cos (2 * θ) * x 1) ^ 2
      = (Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by ring
  rw [key, Real.sin_sq_add_cos_sq, one_mul]

/-- The diffusion operator preserves normalization. -/
theorem Normalized.diffusion_mulVec {x : State} (hx : Normalized x) :
    Normalized (diffusion θ *ᵥ x) := by
  have h1 : normSq x = 1 := hx
  exact (normSq_diffusion_mulVec θ x).trans h1

end Diffusion

section GroverIter

variable (θ : ℝ)

/-- **The Grover iteration is a rotation.**  With `O = diag (-1, 1)` and
`D = 2 |state θ⟩⟨state θ| - I`, the product `G = D * O` equals

```
[ cos 2θ   sin 2θ ]
[ -sin 2θ  cos 2θ ]
```

so each iteration rotates the state by `2θ` towards the marked axis. -/
theorem groverIter_eq_rot : groverIter θ = rot (2 * θ) := by
  rw [groverIter, diffusion_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, phaseOracle, mul_apply, Fin.sum_univ_two]

theorem groverIter_orthogonal : groverIter θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [groverIter_eq_rot]
  exact rot_orthogonal (2 * θ)

theorem groverIter_det : (groverIter θ).det = 1 := by
  rw [groverIter_eq_rot, rot_det]

theorem groverIter_mulVec_apply (x : State) :
    groverIter θ *ᵥ x
      = ![Real.cos (2 * θ) * x 0 + Real.sin (2 * θ) * x 1,
          -Real.sin (2 * θ) * x 0 + Real.cos (2 * θ) * x 1] := by
  rw [groverIter_eq_rot, rot_mulVec_apply]

theorem normSq_groverIter_mulVec (x : State) : normSq (groverIter θ *ᵥ x) = normSq x := by
  rw [groverIter_eq_rot]
  exact normSq_rot_mulVec (2 * θ) x

theorem Normalized.groverIter_mulVec {x : State} (hx : Normalized x) :
    Normalized (groverIter θ *ᵥ x) := by
  have h1 : normSq x = 1 := hx
  exact (normSq_groverIter_mulVec θ x).trans h1

/-- The `k`-th power of the Grover iteration is a rotation by `2 k θ`. -/
theorem groverIter_pow (k : ℕ) : groverIter θ ^ k = rot (↑k * (2 * θ)) := by
  rw [groverIter_eq_rot, rot_pow]

end GroverIter

end Grover
