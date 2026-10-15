/-
Verified number-theoretic primitives for Shor's algorithm.

Everything here is executable over Nat and proved against the standard Mathlib modular
arithmetic API.  Nothing uses floating point or fixed-width integers, so the large moduli that
break fixed-width tools are handled exactly.

* modExp a e n = a^e mod n, with its Nat.ModEq correctness;
* order: the multiplicative order of a modulo n, as the minimum of an explicit finite set,
  with order_spec (it annihilates), order_min (it is the least such exponent) and order_dvd
  (it divides every annihilating exponent) - the property Shor's post-processing depends on;
* ModEq_coprime_mul: the Chinese-remainder combination used in the RSA correctness proof.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic

namespace Shor

open Nat Finset

/-! ### Modular exponentiation -/

/-- Modular exponentiation: a^e mod n. -/
def modExp (a e n : Nat) : Nat := a ^ e % n

theorem modExp_ModEq (a e n : Nat) : modExp a e n ≡ a ^ e [MOD n] := Nat.mod_modEq (a ^ e) n

theorem modExp_congr_base {a b e n : Nat} (h : a ≡ b [MOD n]) : modExp a e n ≡ b ^ e [MOD n] :=
  (Nat.mod_modEq _ _).trans (h.pow e)

theorem modExp_lt (a e n : Nat) (hn : 0 < n) : modExp a e n < n := Nat.mod_lt _ hn

/-! ### The multiplicative order -/

/-- The candidate set for the order of a modulo n: the exponents in [1, phi n].  Fermat-Euler
guarantees it contains an annihilating exponent whenever a and n are coprime and n > 1. -/
def orderCandidates (a n : Nat) : Finset Nat :=
  (Finset.Icc 1 (Nat.totient n)).filter fun k => a ^ k ≡ 1 [MOD n]

theorem nonempty_orderCandidates (a n : Nat) (h : Nat.Coprime a n) (hn : 1 < n) :
    (orderCandidates a n).Nonempty := by
  classical
  rw [orderCandidates, Finset.filter_nonempty_iff]
  refine ⟨Nat.totient n, ?_, Nat.ModEq.pow_totient h⟩
  rw [Finset.mem_Icc]
  exact ⟨Nat.totient_pos.mpr (by omega), Nat.le_refl _⟩

/-- The multiplicative order of a modulo n: the least positive k at most phi n with
a^k ≡ 1 [MOD n].  It is defined for coprime a and n with n > 1; the value is 0 otherwise and no
property is claimed in that case. -/
def order (a n : Nat) : Nat :=
  if h : (orderCandidates a n).Nonempty then Finset.min' (orderCandidates a n) h else 0

theorem order_eq_min (a n : Nat) (h : Nat.Coprime a n) (hn : 1 < n) :
    order a n = Finset.min' (orderCandidates a n) (nonempty_orderCandidates a n h hn) := by
  classical
  simp only [order]
  rw [dif_pos (nonempty_orderCandidates a n h hn)]

theorem order_mem (a n : Nat) (h : Nat.Coprime a n) (hn : 1 < n) :
    order a n ∈ orderCandidates a n := by
  classical
  rw [order_eq_min a n h hn]
  exact Finset.min'_mem _ _

theorem order_spec (a n : Nat) (h : Nat.Coprime a n) (hn : 1 < n) : a ^ order a n ≡ 1 [MOD n] := by
  classical
  have hm := order_mem a n h hn
  rw [orderCandidates, Finset.mem_filter, Finset.mem_Icc] at hm
  exact hm.2

theorem order_pos (a n : Nat) (h : Nat.Coprime a n) (hn : 1 < n) : 0 < order a n := by
  classical
  have hm := order_mem a n h hn
  rw [orderCandidates, Finset.mem_filter, Finset.mem_Icc] at hm
  exact hm.1.1

theorem order_le_totient (a n : Nat) (h : Nat.Coprime a n) (hn : 1 < n) :
    order a n ≤ Nat.totient n := by
  classical
  have hm := order_mem a n h hn
  rw [orderCandidates, Finset.mem_filter, Finset.mem_Icc] at hm
  exact hm.1.2

/-- Minimality: any exponent in [1, phi n] that annihilates a is at least the order. -/
theorem order_min (a n k : Nat) (h : Nat.Coprime a n) (hn : 1 < n) (hk1 : 1 ≤ k)
    (hkt : k ≤ Nat.totient n) (hann : a ^ k ≡ 1 [MOD n]) : order a n ≤ k := by
  classical
  rw [order_eq_min a n h hn]
  refine Finset.min'_le (orderCandidates a n) k ?_
  rw [orderCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hk1, hkt⟩, hann⟩

/-- **The order divides every annihilating exponent.**  This is the number-theoretic core of
Shor's post-processing: a measured period is a multiple of the order. -/
theorem order_dvd (a n k : Nat) (h : Nat.Coprime a n) (hn : 1 < n) (hk : a ^ k ≡ 1 [MOD n]) :
    order a n ∣ k := by
  classical
  have ho : 0 < order a n := order_pos a n h hn
  by_contra hnd
  have hr : k % order a n < order a n := Nat.mod_lt _ ho
  have hne : k % order a n ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hlt : 1 ≤ k % order a n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hne)
  have hle : k % order a n ≤ Nat.totient n :=
    (Nat.lt_of_lt_of_le hr (order_le_totient a n h hn)).le
  have hann : a ^ (k % order a n) ≡ 1 [MOD n] := by
    have hdec : k = order a n * (k / order a n) + k % order a n := (Nat.div_add_mod k _).symm
    rw [hdec, Nat.pow_add, Nat.pow_mul] at hk
    have h1 : (a ^ order a n) ^ (k / order a n) ≡ 1 [MOD n] :=
      by simpa using (order_spec a n h hn).pow (k / order a n)
    have h2 : (a ^ order a n) ^ (k / order a n) * a ^ (k % order a n) ≡
        1 * a ^ (k % order a n) [MOD n] := Nat.ModEq.mul_right _ h1
    have h3 : 1 * a ^ (k % order a n) ≡ 1 [MOD n] := Nat.ModEq.trans (Nat.ModEq.symm h2) hk
    simpa using h3
  have hmin := order_min a n (k % order a n) h hn hlt hle hann
  omega

/-! ### Chinese remainder combination -/

/-- Congruence modulo each of two coprime moduli implies congruence modulo their product. -/
theorem ModEq_coprime_mul {x y m n : Nat} (hx : x ≡ y [MOD m]) (hy : x ≡ y [MOD n])
    (hmn : Nat.Coprime m n) : x ≡ y [MOD m * n] := by
  classical
  have hc : IsCoprime (m : ℤ) (n : ℤ) := by exact_mod_cast hmn
  have key : (m * n : ℤ) ∣ (y : ℤ) - x :=
    IsCoprime.mul_dvd hc (Nat.modEq_iff_dvd.mp hx) (Nat.modEq_iff_dvd.mp hy)
  exact (Nat.modEq_iff_dvd).mpr key

end Shor
