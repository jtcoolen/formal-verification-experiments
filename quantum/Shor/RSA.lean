/-
The classical half of Shor's algorithm for RSA: the order-to-factor lemma, and verified
concrete factorizations and RSA round trips.

Nothing here is quantum: this is the post-processing a measurement outcome is fed into, proved
correct for *any* square root of one that is not ±1 - which is exactly what period finding
produces.
-/
import Shor.Arith

namespace Shor

open Nat

/-! ### From a square root of one to a factor -/

/-- **Shor's factoring step.**  If y is a square root of 1 modulo n with y not congruent to 1
and y+1 not congruent to 0, then gcd(y-1, n) is a non-trivial factor of n.

In Shor's algorithm y = a^(r/2) where r is an even order of a modulo n, so y^2 ≡ 1 always
holds; the two excluded cases are exactly the runs that yield no information. -/
theorem shor_factor {y n : Nat} (hn : 1 < n) (hy0 : 1 ≤ y) (hy1 : y ^ 2 ≡ 1 [MOD n])
    (hne1 : ¬ y ≡ 1 [MOD n]) (hne0 : ¬ y + 1 ≡ 0 [MOD n]) :
    1 < Nat.gcd (y - 1) n ∧ Nat.gcd (y - 1) n < n := by
  classical
  have hg1 : Nat.gcd (y - 1) n ∣ y - 1 := Nat.gcd_dvd_left (y - 1) n
  have hg2 : Nat.gcd (y - 1) n ∣ n := Nat.gcd_dvd_right (y - 1) n
  constructor
  · by_contra hle
    have hg : Nat.gcd (y - 1) n = 1 := by
      have : 1 ≤ Nat.gcd (y - 1) n := Nat.gcd_pos_of_pos_right _ (by omega)
      omega
    have hcop : Nat.Coprime (y - 1) n := by
      rw [Nat.coprime_iff_gcd_eq_one]
      exact hg
    have hdiv : n ∣ (y - 1) * (y + 1) := by
      have hz : (n : ℤ) ∣ (y ^ 2 : ℤ) - 1 := (Nat.modEq_iff_dvd).mp (Nat.ModEq.symm hy1)
      have hfac : ((y : ℤ) ^ 2 - 1) = (((y - 1) * (y + 1) : ℕ) : ℤ) := by
        zify [hy0]
        ring
      rw [hfac] at hz
      exact_mod_cast hz
    have hnext : n ∣ y + 1 := hcop.symm.dvd_of_dvd_mul_left hdiv
    exact hne0 ((Nat.modEq_zero_iff_dvd).mpr hnext)
  · by_contra hge
    have hgle : Nat.gcd (y - 1) n ≤ n := Nat.le_of_dvd (by omega) hg2
    have hg : Nat.gcd (y - 1) n = n := by omega
    have hdn : n ∣ y - 1 := by simpa [hg] using hg1
    have hcon : y ≡ 1 [MOD n] := by
      have h1 : y - 1 ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).mpr hdn
      have h2 : y = (y - 1) + 1 := by omega
      rw [h2]
      exact Nat.ModEq.add_right 1 h1
    exact hne1 hcon

/-- The square root of one produced by an even order: a^t with 2t = order. -/
theorem sqrt_one_of_even_order {a n t : Nat} (h : Nat.Coprime a n) (hn : 1 < n)
    (hr : order a n = 2 * t) : (a ^ t) ^ 2 ≡ 1 [MOD n] := by
  classical
  have h2 : a ^ order a n ≡ 1 [MOD n] := order_spec a n h hn
  have : a ^ order a n = (a ^ t) ^ 2 := by
    rw [hr, show 2 * t = t + t by ring, Nat.pow_add, Nat.pow_two]
  rw [this] at h2
  exact h2

/-- The order is even in the two worked examples below, and the corresponding y is a genuine
non-trivial square root of one. -/
theorem order_even_15 : order 2 15 = 2 * 2 := by decide

theorem order_even_21 : order 2 21 = 2 * 3 := by decide

/-! ### Verified concrete factorizations -/

/-- The multiplicative order of 2 modulo 15 is 4 - computed by the executable definition and
checked by the kernel. -/
theorem order_2_15 : order 2 15 = 4 := by decide

/-- So 2^(4/2) = 4 is a square root of 1 modulo 15 that is neither 1 nor -1. -/
theorem sqrt_15 : 4 ^ 2 ≡ 1 [MOD 15] := by decide

theorem sqrt_15_not_one : ¬ (4 ≡ 1 [MOD 15]) := by decide

theorem sqrt_15_not_minus_one : ¬ (4 + 1 ≡ 0 [MOD 15]) := by decide

/-- **Shor's algorithm, classically verified on 15:** the factor 3 = gcd(4-1, 15) is non-trivial,
and 15 = 3 * 5. -/
theorem factor_15 : 1 < Nat.gcd (4 - 1) 15 ∧ Nat.gcd (4 - 1) 15 < 15 ∧ 15 = 3 * 5 := by decide

/-- The same for 21, with a = 2: order 6, y = 2^3 = 8, gcd(8-1, 21) = 7. -/
theorem order_2_21 : order 2 21 = 6 := by decide

theorem sqrt_21 : 8 ^ 2 ≡ 1 [MOD 21] := by decide

theorem factor_21 : 1 < Nat.gcd (8 - 1) 21 ∧ Nat.gcd (8 - 1) 21 < 21 ∧ 21 = 3 * 7 := by decide

/-! ### RSA round trips, verified by exhaustive decision -/

/-- n = 3 * 11 = 33, phi = 20, e = 3, d = 7 (3 * 7 = 21 ≡ 1 mod 20).  Encryption and decryption
are inverse on *every* message, checked exhaustively by the kernel. -/
theorem rsa_roundtrip_33 : ∀ m ∈ Finset.range 33, modExp (modExp m 3 33) 7 33 = m := by
  decide

/-- The exponent really is a valid key pair: e * d ≡ 1 modulo phi n. -/
theorem rsa_key_33 : 3 * 7 ≡ 1 [MOD Nat.totient 33] := by decide

/-- phi (3 * 11) = 20, matching (3-1)*(11-1). -/
theorem totient_33 : Nat.totient 33 = 20 := by decide

end Shor
