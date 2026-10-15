/-
The elliptic-curve discrete logarithm: the classical recovery step of Shor's ECDLP.

Shor's algorithm for ECDLP reduces the discrete logarithm to period finding on the map
  (a, b) |-> a P + b Q      with  Q = k P,
whose period lattice contains exactly the pairs (c, d) with c + d k ≡ 0 (mod r), where r is the
order of P.  A measured pair (c, d) with d invertible modulo r therefore determines
  k ≡ -c · d⁻¹  (mod r).
That recovery step is what this module proves.  The group law itself is Mathlib's: for a
nonsingular Weierstrass curve over a field the points form an additive commutative group
(Mathlib/AlgebraicGeometry/EllipticCurve/{Affine,Projective,Jacobian}/Point.lean), so scalar
multiplication a • P above is the standard NSMul action and needs no re-implementation.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Shor.Arith

namespace Shor
namespace ECDLP

open Nat

/-- **Discrete-log recovery.**  If the measured pair (c, d) satisfies c + d·k ≡ 0 and d has a
left inverse uinv, then k is determined: k = -c · uinv. -/
theorem recovery {r : Nat} {c d k uinv : ZMod r} (hu : uinv * d = 1) (h : c + d * k = 0) :
    k = -c * uinv := by
  classical
  have hdk : d * k = -c := eq_neg_of_add_eq_zero_right h
  calc k = 1 * k := (one_mul _).symm
    _ = (uinv * d) * k := by rw [hu]
    _ = uinv * (d * k) := mul_assoc _ _ _
    _ = uinv * (-c) := by rw [hdk]
    _ = -c * uinv := mul_comm _ _

/-- Uniqueness: two secrets consistent with the same measured pair are equal. -/
theorem recovery_unique {r : Nat} {c d k₁ k₂ uinv : ZMod r} (hu : uinv * d = 1)
    (h₁ : c + d * k₁ = 0) (h₂ : c + d * k₂ = 0) : k₁ = k₂ := by
  rw [recovery hu h₁, recovery hu h₂]

/-- A concrete instance: r = 7, secret k = 5, measured (c, d) = (6, 3).  Indeed
6 + 3·5 = 21 ≡ 0 (mod 7), and 5 is an inverse of 3 modulo 7. -/
theorem measured_7 : (6 : ZMod 7) + 3 * 5 = 0 := by decide

theorem inv3_7 : (5 : ZMod 7) * 3 = 1 := by decide

/-- The recovery formula returns the secret on that instance: -6 · 3⁻¹ = 1 · 5 = 5 (mod 7). -/
theorem recovered_7 : (5 : ZMod 7) = -(6 : ZMod 7) * 5 := by decide

/-- Period finding returns the order; concretely 3 has multiplicative order 6 modulo 7. -/
theorem order_3_7 : _root_.Shor.order 3 7 = 6 := by decide

end ECDLP
end Shor
