/-
Copyright (c) 2026 Formally Verified Algorithms contributors. All rights reserved.
Released under the MIT license. See the file "LICENSE" in the root of this distribution.

# Phase 4: the optimal iteration count and the `O(√N)` query bound

For a search space of `N` items the Grover half-angle is `θ N = arcsin (1 / √N)` and the number
of iterations we recommend is

```
k_opt N = ⌊ π / (4 θ N) ⌋
```

This file proves, for every real `N ≥ 2`:

1. `|(2 * k_opt N + 1) * θ N - π / 2| ≤ θ N` — the final state is within `θ N` of the marked
   axis;
2. `1 - 1 / N ≤ pSuccess (θ N) (k_opt N)` — the exact success probability at that iteration
   count (Boyer–Brassard–Høyer–Tapp 1996);
3. `(k_opt N : ℝ) ≤ π / 4 * √N` — the explicit oracle-query upper bound.

**Query-cost model.**  One Grover iteration is one invocation of the phase oracle (the diffusion
operator uses no oracle call), so `k` iterations cost exactly `k` oracle queries; see
`Grover.oracleQueries`.
-/
import Grover.Probability

open Matrix Real

noncomputable section

namespace Grover

section ThetaFacts

variable (N : ℝ)

theorem theta_def : theta N = arcsin (1 / sqrt N) := rfl

/-- `sin θ = 1 / √N`, the defining property of the Grover angle. -/
theorem sin_theta (hN : 1 ≤ N) : sin (theta N) = 1 / sqrt N := by
  have h₁ : (-1 : ℝ) ≤ 1 / sqrt N := by
    have : 0 ≤ 1 / sqrt N := by positivity
    linarith
  have h₂ : (1 : ℝ) / sqrt N ≤ 1 := by
    have hsqrt : (1 : ℝ) ≤ sqrt N := le_sqrt_of_sq_le (by norm_num; linarith)
    rw [div_le_one (sqrt_pos.mpr (by linarith : (0 : ℝ) < N))]
    linarith
  show sin (arcsin (1 / sqrt N)) = 1 / sqrt N
  exact sin_arcsin h₁ h₂

/-- The Grover angle is positive. -/
theorem theta_pos (hN : 0 < N) : 0 < theta N :=
  arcsin_pos.mpr (by positivity)

/-- `θ ≤ π / 4` for `N ≥ 2`: the Grover angle never exceeds `45°`. -/
theorem theta_le_pi_div_four (hN : 2 ≤ N) : theta N ≤ π / 4 := by
  have hsqrt : (1 : ℝ) ≤ sqrt N := le_sqrt_of_sq_le (by norm_num; linarith)
  have hx : (1 / sqrt N : ℝ) ∈ Set.Icc (-1) 1 := by
    constructor
    · have : 0 ≤ (1 : ℝ) / sqrt N := by positivity
      linarith
    · rw [div_le_one (sqrt_pos.mpr (by linarith : (0 : ℝ) < N))]
      linarith
  have hy : (π / 4 : ℝ) ∈ Set.Icc (-(π / 2)) (π / 2) := by
    constructor <;> linarith [pi_pos]
  refine (arcsin_le_iff_le_sin hx hy).mpr ?_
  rw [sin_pi_div_four]
  have h2 : (sqrt 2 / 2 : ℝ) = 1 / sqrt 2 := by
    have h : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
    field_simp [h.ne']
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [h2]
  refine (one_div_le_one_div (sqrt_pos.mpr (by linarith : (0 : ℝ) < N))
    (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr ?_
  exact sqrt_le_sqrt (by linarith)

/-- `θ ≤ π / 2` for every `N`. -/
theorem theta_le_pi_div_two (N : ℝ) : theta N ≤ π / 2 := arcsin_le_pi_div_two _

/-- `cos² θ = 1 - 1 / N`. -/
theorem cos_sq_theta (hN : 1 ≤ N) : cos (theta N) ^ 2 = 1 - 1 / N := by
  have h : sin (theta N) ^ 2 + cos (theta N) ^ 2 = 1 := sin_sq_add_cos_sq (theta N)
  rw [sin_theta N hN] at h
  have hsq : (1 / sqrt N) ^ 2 = 1 / N := by
    rw [div_pow, one_pow, sq_sqrt (by linarith : (0 : ℝ) ≤ N)]
  rw [hsq] at h
  linarith

/-- `cos θ = √(1 - 1/N)`, in particular `cos θ ≥ 0`. -/
theorem cos_theta_eq_sqrt (hN : 1 ≤ N) : cos (theta N) = sqrt (1 - 1 / N) := by
  have h : cos (theta N) ^ 2 = 1 - 1 / N := cos_sq_theta N hN
  have hpos : 0 ≤ cos (theta N) := by
    show 0 ≤ cos (arcsin (1 / sqrt N))
    exact cos_arcsin_nonneg _
  nlinarith [sqrt_nonneg (1 - 1 / N), sq_sqrt (show (0 : ℝ) ≤ 1 - 1 / N by
    have : 1 / N ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < N)]
      linarith
    linarith)]

/-- `1 / √N ≤ θ`: the elementary bound `sin x ≤ x` gives the needed lower bound on the angle. -/
theorem inv_sqrt_le_theta (hN : 1 ≤ N) : 1 / sqrt N ≤ theta N := by
  have hpos : 0 < theta N := theta_pos N (by linarith)
  have := sin_le hpos.le
  rw [sin_theta N hN] at this
  exact this

end ThetaFacts

section KOpt

variable (N : ℝ)

theorem kOpt_arg_nonneg (hN : 0 < N) : 0 ≤ π / (4 * theta N) :=
  div_nonneg (le_of_lt pi_pos) (mul_nonneg (by norm_num) (le_of_lt (theta_pos N hN)))

theorem kOpt_le_angle (hN : 0 < N) : (kOpt N : ℝ) ≤ π / (4 * theta N) :=
  Nat.floor_le (kOpt_arg_nonneg N hN)

theorem angle_lt_kOpt (N : ℝ) : π / (4 * theta N) < (kOpt N : ℝ) + 1 := Nat.lt_floor_add_one _

/-- **The angle approximation bound.**  After `k_opt` Grover iterations the state is within
`θ` of the marked axis, i.e. `|(2 k_opt + 1) θ - π/2| ≤ θ`. -/
theorem angle_bound (hN : 1 ≤ N) : |((2 : ℝ) * kOpt N + 1) * theta N - π / 2| ≤ theta N := by
  have hθ : 0 < theta N := theta_pos N (by linarith)
  have h₁ : (kOpt N : ℝ) ≤ π / (4 * theta N) := kOpt_le_angle N (by linarith)
  have h₂ : π / (4 * theta N) < (kOpt N : ℝ) + 1 := angle_lt_kOpt N
  have hmid : 2 * (π / (4 * theta N)) * theta N = π / 2 := by
    field_simp [hθ.ne']
    ring
  have h_upper : ((2 : ℝ) * kOpt N + 1) * theta N - π / 2 ≤ theta N := by
    have hle : (2 : ℝ) * (kOpt N : ℝ) * theta N ≤ 2 * (π / (4 * theta N)) * theta N := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 2))
        (le_of_lt hθ)
    linarith [hle, hmid]
  have h_lower : -theta N ≤ ((2 : ℝ) * kOpt N + 1) * theta N - π / 2 := by
    have hlt : (kOpt N : ℝ) > π / (4 * theta N) - 1 := by linarith [h₂]
    have hmul : (2 : ℝ) * (kOpt N : ℝ) * theta N > 2 * (π / (4 * theta N)) * theta N - 2 * theta N := by
      have := mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < 2 * theta N)
      linarith
    linarith [hmul, hmid]
  exact abs_le.mpr ⟨h_lower, h_upper⟩

/-- **Exact success probability at the recommended iteration count.**  Grover search with
`k_opt N` iterations succeeds with probability at least `1 - 1/N`. -/
theorem pSuccess_kOpt (hN : 2 ≤ N) : 1 - 1 / N ≤ pSuccess (theta N) (kOpt N) := by
  have hb := angle_bound N (by linarith : (1 : ℝ) ≤ N)
  have hc := cos_sq_theta N (by linarith : (1 : ℝ) ≤ N)
  have hθ4 : theta N ≤ π / 4 := theta_le_pi_div_four N (by linarith)
  have hcosθ : 0 ≤ cos (theta N) := by
    show 0 ≤ cos (arcsin (1 / sqrt N))
    exact cos_arcsin_nonneg _
  -- sin ((2k+1)θ) = cos ((2k+1)θ - π/2)
  have hsin : sin (((2 : ℝ) * kOpt N + 1) * theta N)
      = cos (((2 : ℝ) * kOpt N + 1) * theta N - π / 2) := by
    have hrew : ((2 : ℝ) * kOpt N + 1) * theta N
        = (((2 : ℝ) * kOpt N + 1) * theta N - π / 2) + π / 2 := by ring
    rw [hrew, sin_add, sin_pi_div_two, cos_pi_div_two]
    ring
  rw [pSuccess_eq, hsin]
  have hcos_le : cos (theta N) ≤ cos (((2 : ℝ) * kOpt N + 1) * theta N - π / 2) := by
    have h₁ : cos (((2 : ℝ) * kOpt N + 1) * theta N - π / 2)
        = cos |(((2 : ℝ) * kOpt N + 1) * theta N - π / 2)| := (cos_abs _).symm
    rw [h₁]
    refine cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) ?_
    linarith [hb]
  nlinarith [hc, hcos_le, hcosθ, cos_le_one (((2 : ℝ) * kOpt N + 1) * theta N)]

/-- **The `O(√N)` oracle-query upper bound.**  `k_opt` iterations — i.e. `k_opt` oracle calls
— suffice: `(k_opt N : ℝ) ≤ (π/4) √N`. -/
theorem kOpt_le_sqrt (hN : 1 ≤ N) : (kOpt N : ℝ) ≤ π / 4 * sqrt N := by
  have hθ : 0 < theta N := theta_pos N (by linarith)
  have h₁ : (kOpt N : ℝ) ≤ π / (4 * theta N) := kOpt_le_angle N (by linarith)
  have h₂ : π / (4 * theta N) = π / 4 * (1 / theta N) := by field_simp [hθ.ne']
  have h₃ : 1 / theta N ≤ sqrt N := by
    rw [one_div_le hθ (sqrt_pos.mpr (by linarith : (0 : ℝ) < N))]
    exact inv_sqrt_le_theta N hN
  calc (kOpt N : ℝ) ≤ π / (4 * theta N) := h₁
    _ = π / 4 * (1 / theta N) := h₂
    _ ≤ π / 4 * sqrt N := mul_le_mul_of_nonneg_left h₃ (by positivity)

/-- The query-cost model: one Grover iteration is exactly one phase-oracle invocation, so `k`
iterations cost `k` oracle queries. -/
def oracleQueries (k : ℕ) : ℕ := k

@[simp] theorem oracleQueries_zero : oracleQueries 0 = 0 := rfl
@[simp] theorem oracleQueries_succ (k : ℕ) : oracleQueries (k + 1) = oracleQueries k + 1 := rfl

/-- The number of oracle queries used by the recommended schedule is `O(√N)`: the explicit
bound above is the certificate (no asymptotic machinery is claimed beyond it). -/
theorem oracleQueries_kOpt_le (hN : 1 ≤ N) :
    (oracleQueries (kOpt N) : ℝ) ≤ π / 4 * sqrt N := by
  simpa [oracleQueries] using kOpt_le_sqrt N hN

end KOpt

section SmallN

/-- `N = 1`: the unique item is already known, no oracle call is needed. -/
theorem theta_one : theta 1 = π / 2 := by
  show arcsin (1 / sqrt 1) = π / 2
  rw [show (1 / sqrt 1 : ℝ) = 1 by norm_num, arcsin_one]

theorem kOpt_one : kOpt 1 = 0 := by
  have h : (π : ℝ) / (4 * theta 1) = 1 / 2 := by
    rw [theta_one]
    field_simp
    ring
  rw [kOpt, h, Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

/-- With a single candidate the success probability is `1` with zero queries. -/
theorem pSuccess_one : pSuccess (theta 1) (kOpt 1) = 1 := by
  rw [kOpt_one, theta_one]
  rw [pSuccess_eq]
  norm_num

end SmallN

end Grover
