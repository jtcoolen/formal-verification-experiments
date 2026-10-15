/-
The order-finding unitary, as an honest matrix.

Shor's algorithm needs, for a chosen base a and modulus N, a unitary U with
U|x> = |a*x mod N>; period finding then reads the multiplicative order of a mod N off the
eigenvalues of U.  This file pins down the smallest such instance *inside the verified
language*: a = 2, N = 3, which needs two work qubits - and the resulting U is exactly the
SWAP gate.  That is not a coincidence to be waved at:

* 'modMul2_3_val' proves the permutation really is x |-> 2x mod 3 on the little-endian
  encoding of a two-qubit register;
* 'denote_swap_eq_permMat' proves, entrywise and from the independent matrix semantics, that
  the denotation of SWAP is the permutation matrix of that map;
* 'unitary_order_eq_order' proves the order of that unitary is the multiplicative order of
  2 mod 3 as characterized in Shor/Arith.lean.

Convention (documented, because it matters): the register holds ceil(log2 N) = 2 qubits, so
the state 3 = 11 is not a group element; the map fixes every state >= N.  This is the
standard choice for order finding, and it is what makes the map a permutation.
-/
import Quantum.Optimizer
import Shor.Arith

namespace Shor
namespace ModMul

open Quantum

noncomputable section

def j0 : Fin 2 := 0
def j1 : Fin 2 := 1

theorem j0_ne_j1 : ¬ (j1 = j0) := by decide

/-- The natural number a two-qubit basis state encodes, least significant bit first. -/
def val2 (x : Basis 2) : Nat := (x 0).toNat + 2 * (x 1).toNat

/-- The map x |-> 2x mod 3 on a two-qubit register, fixing the non-group state 3.  It is
literally the bit swap - that is the content of this file. -/
def modMul2_3 : Basis 2 -> Basis 2 :=
  fun x => fun i => if i = 0 then x 1 else x 0

theorem modMul2_3_zero (x : Basis 2) : modMul2_3 x 0 = x 1 := by
  simp [modMul2_3]

theorem modMul2_3_one (x : Basis 2) : modMul2_3 x 1 = x 0 := by
  simp [modMul2_3]

/-- The permutation really is multiplication by 2 modulo 3, on the group elements. -/
theorem modMul2_3_val (x : Basis 2) (hx : val2 x < 3) :
    val2 (modMul2_3 x) = (2 * val2 x) % 3 := by
  classical
  rcases h0 : x 0 with (_ | _) <;> rcases h1 : x 1 with (_ | _) <;>
    simp [val2, modMul2_3_zero, modMul2_3_one, h0, h1] at hx ⊢ <;> decide

/-- The non-group state 3 is fixed, exactly as the convention says it must be. -/
theorem modMul2_3_fixes_three (x : Basis 2) (hx : val2 x = 3) : modMul2_3 x = x := by
  classical
  rcases h0 : x 0 with (_ | _) <;> rcases h1 : x 1 with (_ | _) <;>
    simp [val2, h0, h1] at hx <;>
    funext i <;> fin_cases i <;> simp [modMul2_3_zero, modMul2_3_one, h0, h1]

/-- modMul2_3 is an involution: swapping twice is the identity, which is the matrix shadow of
2 * 2 = 1 (mod 3). -/
theorem modMul2_3_involution : modMul2_3 ∘ modMul2_3 = id := by
  funext x i
  simp only [Function.comp_apply, id_eq]
  fin_cases i <;> simp [modMul2_3_zero, modMul2_3_one]

theorem modMul2_3_fixed (x : Basis 2) : modMul2_3 (modMul2_3 x) = x := by
  have := congrFun modMul2_3_involution x
  simpa [Function.comp_apply] using this

theorem modMul2_3_bijective : Function.Bijective modMul2_3 :=
  ⟨fun a b hab => by
      have := congrArg modMul2_3 hab
      rwa [modMul2_3_fixed, modMul2_3_fixed] at this,
    fun y => ⟨modMul2_3 y, modMul2_3_fixed y⟩⟩

/-! ### Permutation matrices -/

/-- The permutation matrix of a self-map of a finite type: 1 exactly on the graph of the map.
Matrix multiplication composes the underlying maps in circuit order: the matrix of "f then g"
is permMat f * permMat g. -/
def permMat {α : Type} [Fintype α] [DecidableEq α] (f : α -> α) : Matrix α α ℂ :=
  fun x y => if f x = y then 1 else 0

/-- The matrix of the identity map is the identity matrix. -/
theorem permMat_id {α : Type} [Fintype α] [DecidableEq α] :
    permMat (id : α -> α) = 1 := by
  ext x y; simp [permMat, Matrix.one_apply]

/-- **Composition.**  permMat f * permMat g is the matrix of g after f. -/
theorem permMat_mul {α : Type} [Fintype α] [DecidableEq α] (f g : α -> α) :
    permMat f * permMat g = permMat (fun x => g (f x)) := by
  classical
  ext x y
  simp only [permMat, Matrix.mul_apply]
  have ptwise : ∀ z, (if f x = z then (1 : ℂ) else 0) * (if g z = y then 1 else 0)
      = (if z = f x then (if g z = y then (1 : ℂ) else 0) else 0) := by
    intro z
    by_cases h : z = f x
    · subst h; simp
    · have h2 : ¬ (f x = z) := fun hh => h hh.symm
      simp [h, h2]
  rw [Finset.sum_congr rfl (fun z _ => ptwise z), Finset.sum_ite_eq']
  simp

/-- An involution gives a matrix that is its own inverse. -/
theorem permMat_self_inverse {α : Type} [Fintype α] [DecidableEq α] (f : α -> α)
    (h : f ∘ f = id) : permMat f * permMat f = 1 := by
  classical
  have key : (fun x => f (f x)) = (id : α -> α) := by
    funext x; exact congrFun h x
  rw [permMat_mul, key, permMat_id]

/-- The conjugate transpose of the permutation matrix of an involution is itself: the
permutation is symmetric as a relation, which is exactly what an involution says. -/
theorem permMat_conjTranspose_self {α : Type} [Fintype α] [DecidableEq α] (f : α -> α)
    (h : f ∘ f = id) : (permMat f).conjTranspose = permMat f := by
  classical
  ext x y
  simp only [Matrix.conjTranspose_apply, permMat]
  have hyy : f (f y) = y := by
    have h1 := congrFun h y
    simpa [Function.comp_apply, id_eq] using h1
  have hxx : f (f x) = x := by
    have h1 := congrFun h x
    simpa [Function.comp_apply, id_eq] using h1
  have key : (f y = x) ↔ (f x = y) := by
    constructor
    · intro hy; exact (congrArg f hy).symm.trans hyy
    · intro hx; exact (congrArg f hx).symm.trans hxx
  by_cases h1 : f y = x
  · rw [if_pos h1, if_pos (key.mp h1)]
    simp
  · rw [if_neg h1, if_neg (fun hh => h1 (key.mpr hh))]
    simp

/-! ### SWAP *is* multiplication by 2 modulo 3 -/

theorem hne : (j0 : Fin 2) ≠ j1 := by decide

/-- **The main identification.**  The denotation of the SWAP gate on two qubits is exactly
the permutation matrix of x |-> 2x mod 3. -/
theorem denote_swap_eq_permMat :
    (denote (Circuit.gate (Gate.swap j0 j1 hne)) : Operator 2) = permMat modMul2_3 := by
  classical
  ext x y
  rw [denote_swap_action]
  have key : (agreeOff [j0, j1] x y ∧ x j0 = y j1 ∧ x j1 = y j0) ↔ modMul2_3 x = y := by
    constructor
    · rintro ⟨_, h1, h2⟩
      have e1 : x 0 = y 1 := h1
      have e2 : x 1 = y 0 := h2
      funext i; fin_cases i <;> simp [modMul2_3_zero, modMul2_3_one, e1, e2]
    · intro h
      refine ⟨by intro a ha; fin_cases a <;> simp_all [List.mem_cons, j0, j1],
        congrFun h 1, congrFun h 0⟩
  simp only [permMat, key]

/-- The order-finding unitary for a = 2, N = 3 squares to the identity. -/
theorem unitary_square_one :
    (permMat modMul2_3 : Matrix (Basis 2) (Basis 2) ℂ) * permMat modMul2_3 = 1 :=
  permMat_self_inverse modMul2_3 modMul2_3_involution

/-- It is unitary - inherited from the verified semantics of SWAP rather than re-proved. -/
theorem isUnitaryM_permMat_modMul2_3 :
    IsUnitaryM (permMat modMul2_3 : Matrix (Basis 2) (Basis 2) ℂ) := by
  classical
  have h : (permMat modMul2_3 : Matrix (Basis 2) (Basis 2) ℂ)
      = denote (Circuit.gate (Gate.swap j0 j1 hne)) := denote_swap_eq_permMat.symm
  rw [h]
  exact denoteGate_isUnitary (Gate.swap j0 j1 hne)

/-- The multiplicative order of 2 mod 3, as computed by Shor/Arith.lean. -/
theorem order_2_3 : Shor.order 2 3 = 2 := by decide

/-- **The link.**  The order-finding unitary satisfies U^r = 1 for r the multiplicative order
of a mod N.  This is the algebraic fact Shor's algorithm exploits, checked here against the
independent matrix semantics. -/
theorem unitary_order_eq_order :
    (permMat modMul2_3 : Matrix (Basis 2) (Basis 2) ℂ) ^ Shor.order 2 3 = 1 := by
  classical
  rw [order_2_3]
  have h1 : (permMat modMul2_3 : Matrix (Basis 2) (Basis 2) ℂ) ^ 2 =
      permMat modMul2_3 * permMat modMul2_3 := pow_two _
  rw [h1, unitary_square_one]

/-- And the denotation of the circuit *is* that unitary, so the SWAP circuit is a genuine
implementation of the order-finding step for N = 3. -/
theorem denote_swap_pow_order :
    (denote (Circuit.gate (Gate.swap j0 j1 hne)) : Operator 2) ^ Shor.order 2 3 = 1 := by
  classical
  rw [denote_swap_eq_permMat]
  exact unitary_order_eq_order

end
end ModMul
end Shor
