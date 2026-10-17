/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 5: the genuine `N`-dimensional quantum search

Everything proved in Phases 1–4 lives in an idealized two-dimensional real plane.  This file
builds the actual search problem on Mathlib's finite-dimensional complex Hilbert space
`EuclideanSpace ℂ (Fin N)` and *proves* that the two-dimensional computation describes it:

* `ket w` = |w⟩, the marked computational basis state;
* `uniform` = |s⟩, the uniform superposition over all `N` basis states;
* `unmarked w` = |r⟩, the normalized superposition of all unmarked basis states;
* `oracleFull w` = the phase oracle `O_w` (sign flip of the marked coordinate);
* `diffusionFull` = `D = 2|s⟩⟨s| - I`;
* `groverFull w = D ∘ O_w`.

The transfer results are `coord_oracle`, `coord_diffusion`, `coord_grover` (the restrictions of
the physical operators to the invariant plane have *exactly* the matrices of Phase 2),
`iterateFull_eq` (closed form of the state after `k` iterations), `probMeasure_iterateFull` /
`probMeasure_eq_pSuccess` (the Born probability of measuring `w` equals the reduced-model
success probability) and `pSuccess_full_kOpt` (success ≥ 1 - 1/N with ≤ (π/4)√N oracle calls).
-/
import Grover.Complexity

open BigOperators Finset Complex Matrix Real

noncomputable section

namespace Grover

/-- Local notation for the complex inner product (Mathlib's own notation is `local` to its
files).  It is conjugate-linear in the first argument and linear in the second, matching the
Dirac convention `⟪x, y⟫ = ⟨x|y⟩`. -/
local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The Hilbert space of the physical model: `N`-dimensional complex Euclidean space. -/
abbrev HilbertSpace (N : ℕ) : Type _ := EuclideanSpace ℂ (Fin N)

variable {N : ℕ}

/-- The inner product of `ℂ` over itself. -/
theorem inner_complex_def (z w : ℂ) : ⟪z, w⟫ = star z * w := by
  simp [inner, mul_comm]

/-- The computational basis state |x⟩. -/
def ket (x : Fin N) : HilbertSpace N := EuclideanSpace.single x 1

/-- The uniform superposition |s⟩ = (1/√N) ∑_x |x⟩. -/
def uniform : HilbertSpace N := WithLp.toLp 2 fun _ : Fin N => (1 / Real.sqrt N : ℂ)

/-- The normalized uniform superposition |r⟩ over all basis states except the marked one. -/
def unmarked (w : Fin N) : HilbertSpace N :=
  WithLp.toLp 2 fun x => if x = w then 0 else (1 / Real.sqrt ((N : ℝ) - 1) : ℂ)

section Coordinates

@[simp] theorem ket_apply (x y : Fin N) : ket x y = (if y = x then (1 : ℂ) else 0) := by
  simp [ket]

@[simp] theorem uniform_apply (x : Fin N) : uniform x = ((1 / Real.sqrt N : ℝ) : ℂ) := by
  simp [uniform]

@[simp] theorem unmarked_apply (w x : Fin N) :
    unmarked w x = (if x = w then (0 : ℂ) else ((1 / Real.sqrt ((N : ℝ) - 1) : ℝ) : ℂ)) := by
  simp [unmarked]

/-- Complex conjugation fixes a real number. -/
theorem star_ofReal_c (r : ℝ) : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) :=
  Complex.conj_ofReal r

/-- The amplitudes of \|s⟩ and \|r⟩ are real, hence fixed by complex conjugation. -/
@[simp] theorem star_uniform (x : Fin N) : star (uniform x) = uniform x := by
  simp only [uniform_apply]
  exact Complex.conj_ofReal _

@[simp] theorem star_unmarked (w x : Fin N) : star (unmarked w x) = unmarked w x := by
  classical
  by_cases h : x = w
  · simp only [unmarked_apply, if_pos h]
    exact star_zero _
  · simp only [unmarked_apply, if_neg h]
    exact Complex.conj_ofReal _

/-- Reading off the marked amplitude is the same as pairing with |w⟩. -/
theorem inner_ket_left (w : Fin N) (ψ : HilbertSpace N) : ⟪ket w, ψ⟫ = ψ w := by
  simp [ket, EuclideanSpace.inner_single_left]

theorem inner_ket_right (w : Fin N) (ψ : HilbertSpace N) : ⟪ψ, ket w⟫ = star (ψ w) := by
  simp [ket, EuclideanSpace.inner_single_right]

end Coordinates

section Norms

/-- The marked state is normalized. -/
theorem norm_ket (w : Fin N) : ‖ket w‖ = 1 := by
  classical
  simp [ket]

theorem normSq_uniform_eq (hN : (1 : ℝ) ≤ N) :
    ∑ i : Fin N, ‖(uniform : HilbertSpace N).ofLp i‖ ^ 2 = (1 : ℝ) := by
  classical
  have h₁ : ∀ i : Fin N, ‖(uniform : HilbertSpace N).ofLp i‖ ^ 2 = (1 : ℝ) / N := by
    intro i
    rw [uniform_apply]
    show ‖((1 / Real.sqrt N : ℝ) : ℂ)‖ ^ 2 = 1 / N
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt N),
      div_pow, one_pow, sq, Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ N)]
  calc ∑ i : Fin N, ‖(uniform : HilbertSpace N).ofLp i‖ ^ 2
      = ∑ _i : Fin N, ((1 : ℝ) / N) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h₁ i]
    _ = (N : ℝ) * (1 / N) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 1 := by
        have : (N : ℝ) ≠ 0 := by linarith
        field_simp [this]

/-- The uniform superposition is normalized: `N · |1/√N|² = 1`. -/
theorem norm_uniform (hN : (1 : ℝ) ≤ N) : ‖(uniform : HilbertSpace N)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, normSq_uniform_eq hN, Real.sqrt_one]

theorem normSq_unmarked (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    ∑ i : Fin N, ‖(unmarked w : HilbertSpace N).ofLp i‖ ^ 2 = (1 : ℝ) := by
  classical
  have hne : (0 : ℝ) < N - 1 := by linarith
  have h₁ : ∀ i : Fin N, ‖(unmarked w : HilbertSpace N).ofLp i‖ ^ 2 =
      (if i = w then (0 : ℝ) else 1 / (N - 1)) := by
    intro i
    simp only [unmarked_apply]
    by_cases hi : i = w
    · rw [hi]
      simp
    · simp only [unmarked_apply, if_neg hi]
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt (N - 1)), div_pow, one_pow, sq,
        Real.mul_self_sqrt (le_of_lt hne)]
  calc ∑ i : Fin N, ‖(unmarked w : HilbertSpace N).ofLp i‖ ^ 2
      = ∑ i : Fin N, (if i = w then (0 : ℝ) else 1 / (N - 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h₁ i]
    _ = 1 := by
        have hf : (fun i => (if i = w then (0 : ℝ) else 1 / (N - 1))) =
            (fun i => (1 : ℝ) / (N - 1) - (if w = i then (1 : ℝ) / (N - 1) else 0)) := by
          funext i
          by_cases hi : i = w
          · subst hi
            simp
          · rw [if_neg hi, if_neg (Ne.symm hi)]
            simp
        rw [hf, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.sum_ite_eq Finset.univ w, if_pos (Finset.mem_univ w)]
        have hN0 : (N : ℝ) ≠ 0 := by linarith
        have hsub : (N : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hN0, hsub]

/-- The unmarked superposition is normalized: `(N-1) · |1/√(N-1)|² = 1`. -/
theorem norm_unmarked (hN : (2 : ℝ) ≤ N) (w : Fin N) : ‖unmarked w‖ = 1 := by
  rw [EuclideanSpace.norm_eq, normSq_unmarked hN w, Real.sqrt_one]

end Norms

section Orthonormal

/-- The marked state and the unmarked superposition are orthogonal. -/
theorem inner_ket_unmarked (w : Fin N) : ⟪ket w, unmarked w⟫ = 0 := by
  classical
  rw [inner_ket_left, unmarked_apply, if_pos (Eq.refl w)]

theorem inner_unmarked_ket (w : Fin N) : ⟪unmarked w, ket w⟫ = 0 := by
  classical
  rw [inner_ket_right, unmarked_apply, if_pos (Eq.refl w), star_zero]

theorem inner_ket_ket (w : Fin N) : ⟪ket w, ket w⟫ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_ket]
  simp

theorem inner_unmarked_unmarked (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    ⟪unmarked w, unmarked w⟫ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_unmarked hN w]
  simp

/-- **|w⟩ and |r⟩ are orthonormal.** -/
theorem orthonormal_ket_unmarked (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    Orthonormal ℂ (fun i : Fin 2 => if i = 0 then ket w else unmarked w) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using inner_ket_ket w
  · simpa using inner_ket_unmarked w
  · simpa using inner_unmarked_ket w
  · simpa using inner_unmarked_unmarked hN w

end Orthonormal

section Plane

/-- The Grover invariant plane: the span of the marked state and the unmarked superposition. -/
def plane (w : Fin N) : Submodule ℂ (HilbertSpace N) :=
  Submodule.span ℂ {ket w, unmarked w}

/-- The state with marked amplitude `a` and unmarked amplitude `b`. -/
def ampState (w : Fin N) (a b : ℂ) : HilbertSpace N := a • ket w + b • unmarked w

theorem ket_mem_plane (w : Fin N) : ket w ∈ plane w :=
  Submodule.subset_span (by simp)

theorem unmarked_mem_plane (w : Fin N) : unmarked w ∈ plane w :=
  Submodule.subset_span (by simp)

/-- `cos θ = √(N-1) / √N`. -/
theorem cos_theta_eq_sqrt_div (hN : (2 : ℝ) ≤ N) :
    Real.cos (theta N) = Real.sqrt (N - 1) / Real.sqrt N := by
  have hne : (0 : ℝ) < N - 1 := by linarith
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have h : Real.cos (theta N) = Real.sqrt (1 - 1 / N) := cos_theta_eq_sqrt N (by linarith)
  rw [h, show (1 - 1 / N : ℝ) = (N - 1) / N by field_simp [hN0]]
  rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ N - 1)]

/-- **|s⟩ lies in the plane**: `|s⟩ = sin θ |w⟩ + cos θ |r⟩`. -/
theorem uniform_decomp (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    uniform = (Real.sin (theta N) : ℂ) • ket w + (Real.cos (theta N) : ℂ) • unmarked w := by
  classical
  have hsin : (Real.sin (theta N) : ℂ) = ((1 / Real.sqrt N : ℝ) : ℂ) := by
    rw [sin_theta N (by linarith : (1 : ℝ) ≤ N)]
  have hcos : (Real.cos (theta N) : ℂ) * ((1 / Real.sqrt (N - 1) : ℝ) : ℂ)
      = ((1 / Real.sqrt N : ℝ) : ℂ) := by
    have hne : (0 : ℝ) < N - 1 := by linarith
    have h₁ : Real.cos (theta N) * (1 / Real.sqrt (N - 1)) = 1 / Real.sqrt N := by
      rw [cos_theta_eq_sqrt_div hN]
      field_simp [Real.sqrt_ne_zero'.mpr hne,
        Real.sqrt_ne_zero'.mpr (by linarith : (0 : ℝ) < N)]
    rw [← Complex.ofReal_mul, h₁]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, uniform_apply, unmarked_apply, ket_apply]
  by_cases hi : i = w
  · rw [if_pos hi, if_pos hi]
    rw [← hsin]
    simp
  · rw [if_neg hi, if_neg hi]
    rw [← hcos]
    simp

/-- `⟪w|s⟩ = sin θ`. -/
theorem inner_ket_uniform (hN : (1 : ℝ) ≤ N) (w : Fin N) :
    ⟪ket w, uniform⟫ = (Real.sin (theta N) : ℂ) := by
  rw [inner_ket_left, uniform_apply]
  show ((1 / Real.sqrt N : ℝ) : ℂ) = (Real.sin (theta N) : ℂ)
  rw [sin_theta N hN]

/-- `⟪s|w⟩ = sin θ`. -/
theorem inner_uniform_ket (hN : (1 : ℝ) ≤ N) (w : Fin N) :
    ⟪uniform, ket w⟫ = (Real.sin (theta N) : ℂ) := by
  classical
  have h := inner_conj_symm (𝕜 := ℂ) uniform (ket w)
  rw [← h, inner_ket_uniform hN w]
  exact Complex.conj_ofReal _

/-- `⟪s|r⟩ = cos θ`. -/
theorem inner_uniform_unmarked (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    ⟪uniform, unmarked w⟫ = (Real.cos (theta N) : ℂ) := by
  rw [uniform_decomp hN w, inner_add_left, inner_smul_left, inner_smul_left,
    inner_ket_unmarked, inner_unmarked_unmarked hN]
  simp only [mul_zero, zero_add, mul_one]
  exact Complex.conj_ofReal _

/-- `⟪r|s⟩ = cos θ`. -/
theorem inner_unmarked_uniform (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    ⟪unmarked w, uniform⟫ = (Real.cos (theta N) : ℂ) := by
  classical
  have h := inner_conj_symm (𝕜 := ℂ) (unmarked w) uniform
  rw [← h, inner_uniform_unmarked hN w]
  exact Complex.conj_ofReal _

/-- **|s⟩ lies in the plane.** -/
theorem uniform_mem_plane (hN : (2 : ℝ) ≤ N) (w : Fin N) : uniform ∈ plane w := by
  rw [uniform_decomp hN w]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (ket_mem_plane w)) ?_
  exact Submodule.smul_mem _ _ (unmarked_mem_plane w)

/-- Pairing a plane state with |w⟩ recovers the marked coefficient. -/
theorem inner_ket_ampState (w : Fin N) (a b : ℂ) : ⟪ket w, ampState w a b⟫ = a := by
  classical
  rw [ampState, inner_add_right, inner_smul_right, inner_smul_right, inner_ket_ket,
    inner_ket_unmarked]
  simp

/-- Pairing a plane state with |r⟩ recovers the unmarked coefficient. -/
theorem inner_unmarked_ampState (hN : (2 : ℝ) ≤ N) (w : Fin N) (a b : ℂ) :
    ⟪unmarked w, ampState w a b⟫ = b := by
  classical
  rw [ampState, inner_add_right, inner_smul_right, inner_smul_right, inner_unmarked_ket,
    inner_self_eq_norm_sq_to_K, norm_unmarked hN]
  simp

/-- The coefficients of a state in the plane are unique. -/
theorem ampState_inj (hN : (2 : ℝ) ≤ N) (w : Fin N) {a b a' b' : ℂ}
    (h : ampState w a b = ampState w a' b') : a = a' ∧ b = b' := by
  classical
  constructor
  · rw [← inner_ket_ampState w a b, ← inner_ket_ampState w a' b', h]
  · rw [← inner_unmarked_ampState hN w a b, ← inner_unmarked_ampState hN w a' b', h]

theorem ampState_congr (w : Fin N) {a b a' b' : ℂ} (ha : a = a') (hb : b = b') :
    ampState w a b = ampState w a' b' := by
  rw [ha, hb]

/-- The plane is exactly the set of states `ampState w a b`. -/
theorem mem_plane_iff (w : Fin N) (ψ : HilbertSpace N) :
    ψ ∈ plane w ↔ ∃ a b : ℂ, ψ = ampState w a b := by
  classical
  constructor
  · intro hψ
    rw [plane] at hψ
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hψ
    exact ⟨a, b, hab.symm⟩
  · rintro ⟨a, b, rfl⟩
    rw [ampState]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (ket_mem_plane w))
      (Submodule.smul_mem _ _ (unmarked_mem_plane w))

end Plane

section Operators

/-- The phase oracle on the full space: flip the sign of the marked amplitude. -/
def oracleFull (w : Fin N) (ψ : HilbertSpace N) : HilbertSpace N :=
  WithLp.toLp 2 fun x => if x = w then - ψ x else ψ x

/-- The diffusion operator on the full space: `D = 2|s⟩⟨s| - I`. -/
def diffusionFull (ψ : HilbertSpace N) : HilbertSpace N :=
  (2 : ℂ) • (⟪uniform, ψ⟫ • uniform) - ψ

/-- One Grover iteration on the full space: oracle first, then diffusion. -/
def groverFull (w : Fin N) (ψ : HilbertSpace N) : HilbertSpace N :=
  diffusionFull (oracleFull w ψ)

@[simp] theorem oracleFull_apply (w : Fin N) (ψ : HilbertSpace N) (x : Fin N) :
    oracleFull w ψ x = (if x = w then - ψ x else ψ x) := rfl

/-- The full oracle acts on the plane by the Phase-2 oracle matrix. -/
theorem oracle_ampState (w : Fin N) (a b : ℂ) :
    oracleFull w (ampState w a b) = ampState w (- a) b := by
  classical
  ext i
  simp only [ampState, oracleFull_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    ket_apply, unmarked_apply, Pi.add_apply, Pi.smul_apply]
  by_cases hi : i = w <;> simp [hi, neg_mul, sub_eq_add_neg, mul_zero, zero_mul, add_zero,
    zero_add]

/-- `⟪s|ψ⟫` for a state of the plane. -/
theorem inner_uniform_ampState (hN : (2 : ℝ) ≤ N) (w : Fin N) (a b : ℂ) :
    ⟪uniform, ampState w a b⟫
      = (Real.sin (theta N) : ℂ) * a + (Real.cos (theta N) : ℂ) * b := by
  rw [ampState, inner_add_right, inner_smul_right, inner_smul_right]
  rw [inner_uniform_ket (by linarith : (1 : ℝ) ≤ N), inner_uniform_unmarked hN]
  ring

/-- `|s⟩` written as a plane state. -/
theorem uniform_eq_ampState (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    uniform = ampState w (Real.sin (theta N)) (Real.cos (theta N)) :=
  uniform_decomp hN w

/-- `ampState` is additive in its coefficients. -/
@[simp] theorem ampState_add (w : Fin N) (a b c d : ℂ) :
    ampState w a b + ampState w c d = ampState w (a + c) (b + d) := by
  show (a • ket w + b • unmarked w) + (c • ket w + d • unmarked w)
    = (a + c) • ket w + (b + d) • unmarked w
  rw [add_smul, add_smul]
  abel

/-- `ampState` is homogeneous in its coefficients. -/
@[simp] theorem ampState_smul (w : Fin N) (k a b : ℂ) :
    k • ampState w a b = ampState w (k * a) (k * b) := by
  show k • (a • ket w + b • unmarked w) = (k * a) • ket w + (k * b) • unmarked w
  rw [smul_add, smul_smul, smul_smul]

/-- `ampState` commutes with negation. -/
@[simp] theorem ampState_neg (w : Fin N) (a b : ℂ) :
    -ampState w a b = ampState w (-a) (-b) := by
  show -(a • ket w + b • unmarked w) = (-a) • ket w + (-b) • unmarked w
  rw [neg_add, neg_smul, neg_smul]

/-- `ampState` commutes with subtraction. -/
@[simp] theorem ampState_sub (w : Fin N) (a b c d : ℂ) :
    ampState w a b - ampState w c d = ampState w (a - c) (b - d) := by
  rw [sub_eq_add_neg, ampState_neg, ampState_add]
  simp [sub_eq_add_neg]

/-- The full diffusion operator acts on the plane by the Phase-2 diffusion matrix. -/
theorem diffusion_ampState (hN : (2 : ℝ) ≤ N) (w : Fin N) (a b : ℂ) :
    diffusionFull (ampState w a b)
      = ampState w
          (2 * (Real.sin (theta N) : ℂ) * ((Real.sin (theta N) : ℂ) * a
            + (Real.cos (theta N) : ℂ) * b) - a)
          (2 * (Real.cos (theta N) : ℂ) * ((Real.sin (theta N) : ℂ) * a
            + (Real.cos (theta N) : ℂ) * b) - b) := by
  rw [diffusionFull, inner_uniform_ampState hN w, uniform_eq_ampState hN w]
  rw [ampState_smul, ampState_smul, ampState_sub]
  refine ampState_congr w ?_ ?_ <;> ring

/-- **The full Grover iteration acts on the plane by the Phase-2 Grover matrix.**  With
`θ = θ N`,
```
(a, b) ↦ (cos 2θ · a + sin 2θ · b,  -sin 2θ · a + cos 2θ · b)
```
which is exactly the matrix `groverIter θ` verified in `Grover/Diffusion.lean`. -/
theorem grover_ampState (hN : (2 : ℝ) ≤ N) (w : Fin N) (a b : ℂ) :
    groverFull w (ampState w a b)
      = ampState w ((Real.cos (2 * theta N) : ℂ) * a + (Real.sin (2 * theta N) : ℂ) * b)
          (-(Real.sin (2 * theta N) : ℂ) * a + (Real.cos (2 * theta N) : ℂ) * b) := by
  have hc : Real.cos (2 * theta N) = 1 - 2 * Real.sin (theta N) ^ 2 := by
    have h : Real.cos (2 * theta N) = 2 * Real.cos (theta N) ^ 2 - 1 := Real.cos_two_mul _
    have h2 : Real.sin (theta N) ^ 2 + Real.cos (theta N) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    linarith
  have hs : Real.sin (2 * theta N) = 2 * Real.sin (theta N) * Real.cos (theta N) :=
    Real.sin_two_mul _
  rw [groverFull, oracle_ampState, diffusion_ampState hN w]
  refine ampState_congr w ?_ ?_
  · rw [hc, hs]
    push_cast
    ring
  · rw [hc, hs]
    push_cast
    have h2 : Complex.sin ↑(theta N) ^ 2 + Complex.cos ↑(theta N) ^ 2 = 1 :=
      Complex.sin_sq_add_cos_sq _
    linear_combination (2 * b) * h2

/-- Every plane state is a member of the plane. -/
theorem ampState_mem_plane (w : Fin N) (a b : ℂ) : ampState w a b ∈ plane w := by
  rw [ampState]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (ket_mem_plane w))
    (Submodule.smul_mem _ _ (unmarked_mem_plane w))

/-- The plane is invariant under the oracle. -/
theorem oracleFull_mem_plane (w : Fin N) (ψ : HilbertSpace N) (hψ : ψ ∈ plane w) :
    oracleFull w ψ ∈ plane w := by
  classical
  obtain ⟨a, b, hab⟩ := (mem_plane_iff w ψ).mp hψ
  rw [hab, oracle_ampState]
  exact ampState_mem_plane w _ _

/-- The plane is invariant under diffusion. -/
theorem diffusionFull_mem_plane (hN : (2 : ℝ) ≤ N) (w : Fin N) (ψ : HilbertSpace N)
    (hψ : ψ ∈ plane w) : diffusionFull ψ ∈ plane w := by
  classical
  obtain ⟨a, b, hab⟩ := (mem_plane_iff w ψ).mp hψ
  rw [hab, diffusion_ampState hN w]
  exact ampState_mem_plane w _ _

/-- The plane is invariant under the Grover iteration. -/
theorem groverFull_mem_plane (hN : (2 : ℝ) ≤ N) (w : Fin N) (ψ : HilbertSpace N)
    (hψ : ψ ∈ plane w) : groverFull w ψ ∈ plane w := by
  rw [groverFull]
  exact diffusionFull_mem_plane hN w _ (oracleFull_mem_plane w _ hψ)

end Operators

section Transfer

/-- The coordinate map that identifies the invariant plane with `ℂ²` in the basis
`(|w⟩, |r⟩)`. -/
def coord (w : Fin N) (ψ : HilbertSpace N) : Fin 2 → ℂ :=
  ![⟪ket w, ψ⟫, ⟪unmarked w, ψ⟫]

theorem coord_ampState (hN : (2 : ℝ) ≤ N) (w : Fin N) (a b : ℂ) :
    coord w (ampState w a b) = ![a, b] := by
  classical
  show ![⟪ket w, ampState w a b⟫, ⟪unmarked w, ampState w a b⟫] = ![a, b]
  rw [inner_ket_ampState, inner_unmarked_ampState hN]

/-- **The restriction of the physical Grover iteration to the invariant plane is the Phase-2
matrix** `groverIter θ` (with entries viewed in `ℂ`). -/
theorem coord_grover_of_mem_plane (hN : (2 : ℝ) ≤ N) (w : Fin N) (ψ : HilbertSpace N)
    (hψ : ψ ∈ plane w) :
    coord w (groverFull w ψ)
      = Matrix.map (groverIter (theta N)) Complex.ofReal *ᵥ coord w ψ := by
  classical
  obtain ⟨a, b, hab⟩ := (mem_plane_iff w ψ).mp hψ
  subst hab
  have h00 : (groverIter (theta N)).map Complex.ofReal 0 0 = (Real.cos (2 * theta N) : ℂ) := by
    rw [Matrix.map_apply, groverIter_eq_rot, rot_00]
  have h01 : (groverIter (theta N)).map Complex.ofReal 0 1 = (Real.sin (2 * theta N) : ℂ) := by
    rw [Matrix.map_apply, groverIter_eq_rot, rot_01]
  have h10 : (groverIter (theta N)).map Complex.ofReal 1 0 = -(Real.sin (2 * theta N) : ℂ) := by
    rw [Matrix.map_apply, groverIter_eq_rot, rot_10]
    simp
  have h11 : (groverIter (theta N)).map Complex.ofReal 1 1 = (Real.cos (2 * theta N) : ℂ) := by
    rw [Matrix.map_apply, groverIter_eq_rot, rot_11]
  rw [grover_ampState hN w]
  simp only [coord_ampState hN w]
  rw [mulVec_fin_two, h00, h01, h10, h11]
  simp

/-- The state of the physical algorithm after `k` Grover iterations. -/
def iterateFull (w : Fin N) (k : ℕ) : HilbertSpace N := (groverFull w) ^[k] uniform

/-- **Closed form of the physical state after `k` iterations** — the exact analogue of
`Grover.iterate_eq_state`, now for the genuine `N`-dimensional operators. -/
theorem iterateFull_eq (hN : (2 : ℝ) ≤ N) (w : Fin N) (k : ℕ) :
    iterateFull w k
      = ampState w (Real.sin (((2 : ℝ) * k + 1) * theta N))
          (Real.cos (((2 : ℝ) * k + 1) * theta N)) := by
  classical
  induction k with
  | zero =>
      have h₁ : ((2 : ℝ) * ((0 : ℕ) : ℝ) + 1) * theta N = theta N := by ring
      show uniform = ampState w (Real.sin (((2 : ℝ) * ((0 : ℕ) : ℝ) + 1) * theta N))
        (Real.cos (((2 : ℝ) * ((0 : ℕ) : ℝ) + 1) * theta N))
      rw [h₁]
      exact uniform_decomp hN w
  | succ k ih =>
      have ih' : (groverFull w) ^[k] uniform
          = ampState w (Real.sin (((2 : ℝ) * (k : ℝ) + 1) * theta N))
              (Real.cos (((2 : ℝ) * (k : ℝ) + 1) * theta N)) := ih
      show (groverFull w) ^[k + 1] uniform = _
      rw [Function.iterate_succ_apply', ih', grover_ampState hN w]
      have h₁ : ((2 : ℝ) * ((k + 1 : ℕ) : ℝ) + 1) * theta N
          = ((2 : ℝ) * (k : ℝ) + 1) * theta N + 2 * theta N := by push_cast; ring
      refine ampState_congr w ?_ ?_
      · rw [h₁, Real.sin_add]
        simp only [← Complex.ofReal_mul, ← Complex.ofReal_add]
        ring
      · rw [h₁, Real.cos_add]
        simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub,
          ← Complex.ofReal_neg, sub_eq_add_neg, neg_mul]
        ring

/-- The Born-rule probability of measuring the marked element `w` in the state `ψ`. -/
def probMeasure (w : Fin N) (ψ : HilbertSpace N) : ℝ := ‖ψ w‖ ^ 2

/-- **Exact success probability of the physical algorithm.** -/
theorem probMeasure_iterateFull (hN : (2 : ℝ) ≤ N) (w : Fin N) (k : ℕ) :
    probMeasure w (iterateFull w k)
      = Real.sin (((2 : ℝ) * k + 1) * theta N) ^ 2 := by
  classical
  rw [probMeasure, iterateFull_eq hN w k, ampState]
  have h₁ : ((Real.sin (((2 : ℝ) * k + 1) * theta N) : ℂ) • ket w
      + (Real.cos (((2 : ℝ) * k + 1) * theta N) : ℂ) • unmarked w).ofLp w
      = (Real.sin (((2 : ℝ) * k + 1) * theta N) : ℂ) := by
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, ket_apply, unmarked_apply,
      if_pos (Eq.refl w)]
    simp
  rw [h₁, norm_real, Real.norm_eq_abs, sq_abs]

/-- The physical measurement probability agrees with the reduced model's success probability. -/
theorem probMeasure_eq_pSuccess (hN : (2 : ℝ) ≤ N) (w : Fin N) (k : ℕ) :
    probMeasure w (iterateFull w k) = pSuccess (theta N) k := by
  rw [probMeasure_iterateFull hN w k, pSuccess_eq]

/-- Pythagoras in the plane: the squared norm of a plane state is the sum of the squared moduli
of its two coefficients. -/
theorem norm_ampState_sq (hN : (2 : ℝ) ≤ N) (w : Fin N) (a b : ℂ) :
    ‖ampState w a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  classical
  have ha : a * (starRingEnd ℂ) a = (‖a‖ : ℂ) ^ 2 := by
    show a * star a = _
    rw [mul_comm, ← inner_complex_def]
    exact inner_self_eq_norm_sq_to_K a
  have hb : b * (starRingEnd ℂ) b = (‖b‖ : ℂ) ^ 2 := by
    show b * star b = _
    rw [mul_comm, ← inner_complex_def]
    exact inner_self_eq_norm_sq_to_K b
  have h : ⟪ampState w a b, ampState w a b⟫ = (‖a‖ ^ 2 + ‖b‖ ^ 2 : ℂ) := by
    simp only [ampState, inner_add_left, inner_smul_left, inner_add_right, inner_smul_right,
      inner_ket_ket, inner_unmarked_unmarked hN, inner_ket_unmarked, inner_unmarked_ket,
      mul_one, mul_zero, zero_add, add_zero]
    rw [ha, hb]
  have h₂ : (‖ampState w a b‖ : ℂ) ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2 : ℂ) :=
    (inner_self_eq_norm_sq_to_K (ampState w a b)).symm.trans h
  exact_mod_cast h₂

/-- The physical state stays normalized. -/
theorem norm_iterateFull (hN : (2 : ℝ) ≤ N) (w : Fin N) (k : ℕ) :
    ‖iterateFull w k‖ = 1 := by
  classical
  have h₁ : ‖iterateFull w k‖ ^ 2 = 1 := by
    rw [iterateFull_eq hN w k, norm_ampState_sq hN w]
    have ha : ‖(Real.sin (((2 : ℝ) * k + 1) * theta N) : ℂ)‖ ^ 2
        = Real.sin (((2 : ℝ) * k + 1) * theta N) ^ 2 := by
      rw [norm_real, Real.norm_eq_abs, sq_abs]
    have hb : ‖(Real.cos (((2 : ℝ) * k + 1) * theta N) : ℂ)‖ ^ 2
        = Real.cos (((2 : ℝ) * k + 1) * theta N) ^ 2 := by
      rw [norm_real, Real.norm_eq_abs, sq_abs]
    rw [ha, hb, Real.sin_sq_add_cos_sq]
  nlinarith [h₁, norm_nonneg (iterateFull w k)]

/-- **End-to-end theorem.**  For every search space of size `N ≥ 2` with a single marked
element `w`, running the genuine `N`-dimensional Grover iteration `k_opt N` times measures
`w` with probability at least `1 - 1/N`, using at most `(π/4)·√N` oracle queries. -/
theorem grover_success_kOpt (hN : (2 : ℝ) ≤ N) (w : Fin N) :
    1 - 1 / N ≤ probMeasure w (iterateFull w (kOpt N)) := by
  rw [probMeasure_eq_pSuccess hN w (kOpt N)]
  exact pSuccess_kOpt N hN

/-- **End-to-end query bound.** -/
theorem grover_queries_kOpt (hN : (1 : ℝ) ≤ N) :
    (oracleQueries (kOpt N) : ℝ) ≤ π / 4 * Real.sqrt N :=
  oracleQueries_kOpt_le N hN

end Transfer

end Grover
