/-
Independent mathematical semantics: embedding gate matrices into the n-qubit operator space.

The meaning of a circuit is a complex matrix indexed by the computational basis
'Basis n = Fin n -> Bool' (2^n states).  This file defines the operator space, the
"agreement outside a set of qubits" machinery that embeds a k-qubit gate matrix into the
n-qubit space, and the structural facts about those embeddings that every rewrite proof in
this project is derived from:

* embed1 U i * embed1 V i = embed1 (U * V) i          (same qubit: matrix multiplication)
* embed2 W i j * embed2 W' i j = embed2 (W * W') i j  (same pair of qubits, i different from j)
* embed1 (1 : Matrix Bool Bool ℂ) i = 1              (identity gate is the identity operator)
* gates on disjoint qubits commute
* conjugate transpose commutes with embedding, hence unitarity lifts

Nothing here mentions the optimizer, e-graphs, rewrite rules or certificates: this is the
reference model those components are judged against.
-/
import Quantum.Syntax
import Quantum.Gates
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace Quantum

open Complex Classical

/-! ### The operator space -/

/-- The computational basis of an n-qubit register: one bit per qubit index. -/
abbrev Basis (n : Nat) : Type := Fin n → Bool

/-- Operators on an n-qubit register: complex matrices indexed by the computational basis.
The entry M x y is the amplitude of the output basis state x given the input basis state y. -/
abbrev Operator (n : Nat) : Type := Matrix (Basis n) (Basis n) ℂ

/-- The n-qubit operator space has dimension 2^n. -/
theorem fintype_card_Basis (n : Nat) : Fintype.card (Basis n) = 2 ^ n := by
  classical
  simp [Fintype.card_fun, Fintype.card_fin]

/-! ### Agreement outside a set of qubits -/

/-- x and y agree outside the qubit indices s. -/
def agreeOff {n : Nat} (s : List (Fin n)) (x y : Basis n) : Prop :=
  ∀ a, a ∉ s → x a = y a

/-- The bits of x at the positions listed in s. -/
def bitsAt {n : Nat} (s : List (Fin n)) (x : Basis n) : ∀ a : Fin n, a ∈ s → Bool :=
  fun a _ => x a

/-- Overwrite the bits of x at the positions of s by the values v. -/
def setBits {n : Nat} (s : List (Fin n)) (x : Basis n) (v : ∀ a : Fin n, a ∈ s → Bool) :
    Basis n :=
  fun a => if h : a ∈ s then v a h else x a

/-- The basis state equal to y on s and to x outside s. -/
def mix {n : Nat} (s : List (Fin n)) (x y : Basis n) : Basis n :=
  fun a => if a ∈ s then y a else x a

namespace AgreeOff

theorem agreeOff_swap {n} {s t : List (Fin n)} (x y : Basis n)
    (h : agreeOff (s ++ t) x y) : agreeOff (t ++ s) x y :=
  fun a ha => h a (fun hh => ha (by
    rcases List.mem_append.mp hh with hs | ht
    · exact List.mem_append.mpr (Or.inr hs)
    · exact List.mem_append.mpr (Or.inl ht)))

theorem symm {n} {s : List (Fin n)} {x y : Basis n} (h : agreeOff s x y) : agreeOff s y x :=
  fun a ha => (h a ha).symm

theorem trans' {n} {s : List (Fin n)} {x y z : Basis n} (h₁ : agreeOff s x y)
    (h₂ : agreeOff s y z) : agreeOff s x z :=
  fun a ha => (h₁ a ha).trans (h₂ a ha)

/-- Agreement composes: if x agrees with u outside s and u agrees with y outside t, then x
agrees with y outside s ++ t. -/
theorem agreeOff_append {n} {s t : List (Fin n)} {x u y : Basis n}
    (h1 : agreeOff s x u) (h2 : agreeOff t u y) : agreeOff (s ++ t) x y := by
  intro a ha
  have hs : a ∉ s := fun hh => ha (by simp [hh])
  have ht : a ∉ t := fun hh => ha (by simp [hh])
  exact (h1 a hs).trans (h2 a ht)

theorem of_not_mem_append {n} {s t : List (Fin n)} {x y : Basis n} (h : agreeOff (s ++ t) x y)
    {a : Fin n} (ha : a ∉ s) (hb : a ∉ t) : x a = y a :=
  h a (fun hh => (List.mem_append.mp hh).elim (fun hs' => absurd hs' ha)
    (fun ht' => absurd ht' hb))

theorem pair_comm {n} {i j : Fin n} {x y : Basis n} :
    agreeOff [i, j] x y ↔ agreeOff [j, i] x y := by
  classical
  refine ⟨fun h a ha => h a (fun hm => ha (by simpa [or_comm, or_assoc] using hm)),
          fun h a ha => h a (fun hm => ha (by simpa [or_comm, or_assoc] using hm))⟩

theorem setBits_out {n} (s : List (Fin n)) (x : Basis n) (v : ∀ a : Fin n, a ∈ s → Bool)
    {a : Fin n} (ha : a ∉ s) : setBits s x v a = x a := dif_neg ha

theorem setBits_in {n} (s : List (Fin n)) (x : Basis n) (v : ∀ a : Fin n, a ∈ s → Bool)
    {a : Fin n} (ha : a ∈ s) : setBits s x v a = v a ha := dif_pos ha

theorem agreeOff_setBits {n} (s : List (Fin n)) (x : Basis n)
    (v : ∀ a : Fin n, a ∈ s → Bool) : agreeOff s x (setBits s x v) :=
  fun a ha => (setBits_out s x v ha).symm

theorem bitsAt_setBits {n} (s : List (Fin n)) (x : Basis n)
    (v : ∀ a : Fin n, a ∈ s → Bool) : bitsAt s (setBits s x v) = v := by
  funext a ha
  show setBits s x v a = v a ha
  rw [setBits_in s x v ha]

theorem agreeOff_iff_setBits {n} (s : List (Fin n)) (x y : Basis n) :
    agreeOff s x y ↔ y = setBits s x (bitsAt s y) := by
  constructor
  · intro h
    funext a
    by_cases ha : a ∈ s
    · show y a = setBits s x (bitsAt s y) a
      rw [setBits_in s x (bitsAt s y) ha]
      rfl
    · rw [setBits_out s x (bitsAt s y) ha]
      exact (h a ha).symm
  · intro h
    rw [h]
    exact agreeOff_setBits s x _

theorem mix_in {n} (s : List (Fin n)) (x y : Basis n) {a : Fin n} (ha : a ∈ s) :
    mix s x y a = y a := if_pos ha

theorem mix_out {n} (s : List (Fin n)) (x y : Basis n) {a : Fin n} (ha : a ∉ s) :
    mix s x y a = x a := if_neg ha

theorem agreeOff_mix_left {n} {s : List (Fin n)} (x y : Basis n) :
    agreeOff s x (mix s x y) :=
  fun a ha => (mix_out s x y ha).symm

theorem agreeOff_mix_right {n} {s t : List (Fin n)} (x y : Basis n)
    (hxy : agreeOff (s ++ t) x y) : agreeOff t (mix s x y) y := by
  intro a ha
  by_cases hs : a ∈ s
  · exact mix_in s x y hs
  · rw [mix_out s x y hs]
    exact of_not_mem_append hxy hs ha

/-- The unique intermediate basis state when two disjoint supports are composed:
u agrees with x outside s and with y outside t. -/
theorem mix_unique {n} {s t : List (Fin n)} (hdisj : ∀ a ∈ s, ∀ b ∈ t, a ≠ b) (x y u : Basis n)
    (hxy : agreeOff (s ++ t) x y) :
    (agreeOff s x u ∧ agreeOff t u y) ↔ u = mix s x y := by
  constructor
  · intro h
    funext a
    by_cases hs : a ∈ s
    · have hat : a ∉ t := fun ht => absurd rfl (hdisj a hs a ht)
      rw [mix_in s x y hs]
      exact h.2 a hat
    · rw [mix_out s x y hs]
      exact (h.1 a hs).symm
  · intro h
    subst h
    exact ⟨agreeOff_mix_left x y, agreeOff_mix_right x y hxy⟩

end AgreeOff

/-! ### Reindexing finite sums -/

/-- Reindex a condition-guarded sum along a bijection onto the satisfied elements. -/
theorem sum_cond_bij {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α] (P : ι → Prop)
    [DecidablePred P] (ins : α → ι) (proj : ι → α) (f : ι → ℂ)
    (h1 : ∀ a, P (ins a)) (h2 : ∀ a, proj (ins a) = a)
    (h3 : ∀ i, P i → ins (proj i) = i) :
    (∑ i : ι, if P i then f i else 0) = ∑ a : α, f (ins a) := by
  classical
  have hinj : Function.Injective ins := by
    intro a b hab
    have := congrArg proj hab
    rwa [h2, h2] at this
  have hsum : (∑ i : ι, if P i then f i else 0) = ∑ i ∈ Finset.univ.filter P, f i := by
    rw [Finset.sum_filter]
  rw [hsum]
  have himg : Finset.univ.filter P = Finset.univ.image ins := by
    apply Finset.ext
    intro i
    constructor
    · intro h
      refine Finset.mem_image.mpr ⟨proj i, Finset.mem_univ _, ?_⟩
      exact h3 i (Finset.mem_filter.mp h).2
    · intro h
      rcases Finset.mem_image.mp h with ⟨a, _, he⟩
      rw [← he]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1 a⟩
  rw [himg, Finset.sum_image (fun a₁ _ a₂ _ h => hinj h)]

/-- A condition satisfied by exactly one element: the sum collapses to that element. -/
theorem sum_cond_unique {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (i₀ : ι) (h : ∀ i, (P i ↔ i = i₀)) (f : ι → ℂ) :
    (∑ i : ι, if P i then f i else 0) = f i₀ := by
  classical
  have hsum : (∑ i : ι, if P i then f i else 0) = ∑ i ∈ Finset.univ.filter P, f i := by
    rw [Finset.sum_filter]
  rw [hsum]
  have hset : Finset.univ.filter P = {i₀} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and]
    exact h i
  rw [hset, Finset.sum_singleton]

/-- Reindexing a sum along an equivalence. -/
theorem sum_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℂ) :
    (∑ b : β, f b) = ∑ a : α, f (e a) := by
  classical
  have himg : (Finset.univ : Finset β) = Finset.univ.image e := by
    ext b
    simp only [Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨fun _ => ⟨e.symm b, by simp [e.apply_symm_apply]⟩, fun _ => trivial⟩
  calc (∑ b : β, f b) = ∑ b ∈ (Finset.univ : Finset β), f b := rfl
    _ = ∑ b ∈ Finset.univ.image e, f b := by rw [himg]
    _ = ∑ a : α, f (e a) := by
      rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]

/-! ### Gate embeddings -/

/-- Embed a single-qubit gate acting on qubit i into the n-qubit operator space: the matrix
entry is the gate entry on bit i, provided every other bit is unchanged. -/
noncomputable def embed1 {n : Nat} (U : Matrix Bool Bool ℂ) (i : Fin n) : Operator n :=
  fun x y => if agreeOff [i] x y then U (x i) (y i) else 0

/-- Embed a two-qubit gate acting on the ordered pair of qubits i, j. -/
noncomputable def embed2 {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (i j : Fin n) : Operator n :=
  fun x y => if agreeOff [i, j] x y then W (x i, x j) (y i, y j) else 0

theorem embed1_apply {n : Nat} (U : Matrix Bool Bool ℂ) (i : Fin n) (x y : Basis n) :
    embed1 U i x y = if agreeOff [i] x y then U (x i) (y i) else 0 := by
  simp [embed1]

theorem embed2_apply {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n)
    (x y : Basis n) :
    embed2 W i j x y = if agreeOff [i, j] x y then W (x i, x j) (y i, y j) else 0 := by
  simp [embed2]

theorem setBits_singleton {n : Nat} (x u : Basis n) (i : Fin n) (hu : agreeOff [i] x u) :
    setBits [i] x (fun a _ => u i) = u := by
  classical
  funext a
  by_cases ha : a = i
  · show (if h : a ∈ ([i] : List (Fin n)) then (fun a' _ => u i) a h else x a) = u a
    rw [dif_pos (by simp [ha])]
    exact (congrArg u ha).symm
  · show (if h : a ∈ ([i] : List (Fin n)) then (fun a' _ => u i) a h else x a) = u a
    rw [dif_neg (by simpa using ha)]
    exact hu a (by simpa using ha)

theorem setBits_pair {n : Nat} (x u : Basis n) {i j : Fin n} (hij : i ≠ j)
    (hu : agreeOff [i, j] x u) :
    setBits [i, j] x (fun a _ => if h : a = i then u i else u j) = u := by
  classical
  have hbits : (fun a (_ : a ∈ ([i, j] : List (Fin n))) =>
      if h : a = i then u i else u j) = bitsAt [i, j] u := by
    funext a ha
    show (if h : a = i then u i else u j) = u a
    by_cases hi : a = i
    · rw [dif_pos hi]
      exact (congrArg u hi).symm
    · rw [dif_neg hi]
      have haj : a = j := by
        rcases (by simpa [List.mem_cons, List.mem_singleton] using ha) with h | h
        · exact absurd h hi
        · exact h
      exact (congrArg u haj).symm
  rw [hbits]
  exact ((AgreeOff.agreeOff_iff_setBits [i, j] x u).mp hu).symm

theorem setBits_pair_val {n : Nat} (x : Basis n) {i j : Fin n} (hij : i ≠ j) (p : Bool × Bool) :
    (setBits [i, j] x (fun a _ => if h : a = i then p.1 else p.2) i,
     setBits [i, j] x (fun a _ => if h : a = i then p.1 else p.2) j) = p := by
  classical
  have h1 : setBits [i, j] x (fun a _ => if h : a = i then p.1 else p.2) i = p.1 := by
    rw [AgreeOff.setBits_in [i, j] x _ (by simp)]
    simp
  have h2 : setBits [i, j] x (fun a _ => if h : a = i then p.1 else p.2) j = p.2 := by
    rw [AgreeOff.setBits_in [i, j] x _ (by simp)]
    show (if h : (j : Fin n) = i then p.1 else p.2) = p.2
    rw [dif_neg (fun hh => hij hh.symm)]
  rw [h1, h2]

theorem embed1_eq_of_agree {n : Nat} (U : Matrix Bool Bool ℂ) (i : Fin n) {x y : Basis n}
    (h : agreeOff [i] x y) : embed1 U i x y = U (x i) (y i) := by
  rw [embed1_apply, if_pos h]

theorem embed1_ne {n : Nat} (U : Matrix Bool Bool ℂ) (i : Fin n) {x y : Basis n}
    (h : ¬ agreeOff [i] x y) : embed1 U i x y = 0 := by
  rw [embed1_apply, if_neg h]

theorem embed2_eq_of_agree {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n)
    {x y : Basis n} (h : agreeOff [i, j] x y) :
    embed2 W i j x y = W (x i, x j) (y i, y j) := by
  rw [embed2_apply, if_pos h]

theorem embed2_ne {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n)
    {x y : Basis n} (h : ¬ agreeOff [i, j] x y) : embed2 W i j x y = 0 := by
  rw [embed2_apply, if_neg h]

/-- Composition of two gates on the same qubit is composition of their 2x2 matrices. -/
theorem embed1_mul {n : Nat} (U V : Matrix Bool Bool ℂ) (i : Fin n) :
    embed1 U i * embed1 V i = embed1 (U * V) i := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  have hsum : (∑ u : Basis n, embed1 U i x u * embed1 V i u y)
      = ∑ u : Basis n, if agreeOff [i] x u ∧ agreeOff [i] u y
          then U (x i) (u i) * V (u i) (y i) else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases h₁ : agreeOff [i] x u <;> by_cases h₂ : agreeOff [i] u y <;>
      simp [h₁, h₂, embed1_apply]
  rw [hsum]
  by_cases hxy : agreeOff [i] x y
  · have heq : ∀ u, (agreeOff [i] x u ∧ agreeOff [i] u y) ↔ agreeOff [i] x u := by
      intro u
      exact ⟨fun h => h.1, fun hu => ⟨hu, AgreeOff.trans' (AgreeOff.symm hu) hxy⟩⟩
    have hconv : ∀ u, (if agreeOff [i] x u ∧ agreeOff [i] u y
        then U (x i) (u i) * V (u i) (y i) else 0)
        = (if agreeOff [i] x u then U (x i) (u i) * V (u i) (y i) else 0) := by
      intro u
      by_cases hu : agreeOff [i] x u
      · rw [if_pos ((heq u).mpr hu), if_pos hu]
      · rw [if_neg (fun h => hu (h.1)), if_neg hu]
    rw [Finset.sum_congr rfl (fun u _ => hconv u)]
    rw [sum_cond_bij (P := fun u => agreeOff [i] x u)
        (ins := fun b => setBits [i] x (fun a _ => b)) (proj := fun u => u i)
        (f := fun u => U (x i) (u i) * V (u i) (y i))
        (fun b => AgreeOff.agreeOff_setBits [i] x (fun a _ => b))
        (fun b => by show setBits [i] x (fun a _ => b) i = b
                     rw [AgreeOff.setBits_in [i] x _ (by simp)])
        (fun u hu => setBits_singleton x u i hu)]
    rw [Finset.sum_congr rfl (fun b _ => by
      rw [AgreeOff.setBits_in [i] x (fun a _ => b) (by simp)])]
    rw [embed1_apply, if_pos hxy, sum_bool_eq, ← mul2_apply]
  · have hempty : ∀ u, ¬ (agreeOff [i] x u ∧ agreeOff [i] u y) := by
      intro u h
      exact hxy (AgreeOff.trans' h.1 h.2)
    rw [Finset.sum_eq_zero (fun u _ => if_neg (hempty u)), embed1_apply, if_neg hxy]

/-- Composition of two gates on the same ordered pair of qubits. -/
theorem embed2_mul {n : Nat} (W W' : Matrix (Bool × Bool) (Bool × Bool) ℂ) {i j : Fin n}
    (hij : i ≠ j) : embed2 W i j * embed2 W' i j = embed2 (W * W') i j := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  have hsum : (∑ u : Basis n, embed2 W i j x u * embed2 W' i j u y)
      = ∑ u : Basis n, if agreeOff [i, j] x u ∧ agreeOff [i, j] u y
          then W (x i, x j) (u i, u j) * W' (u i, u j) (y i, y j) else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases h₁ : agreeOff [i, j] x u <;> by_cases h₂ : agreeOff [i, j] u y <;>
      simp [h₁, h₂, embed2_apply]
  rw [hsum]
  by_cases hxy : agreeOff [i, j] x y
  · have heq : ∀ u, (agreeOff [i, j] x u ∧ agreeOff [i, j] u y) ↔ agreeOff [i, j] x u := by
      intro u
      exact ⟨fun h => h.1, fun hu => ⟨hu, AgreeOff.trans' (AgreeOff.symm hu) hxy⟩⟩
    have hconv : ∀ u, (if agreeOff [i, j] x u ∧ agreeOff [i, j] u y
        then W (x i, x j) (u i, u j) * W' (u i, u j) (y i, y j) else 0)
        = (if agreeOff [i, j] x u
            then W (x i, x j) (u i, u j) * W' (u i, u j) (y i, y j) else 0) := by
      intro u
      by_cases hu : agreeOff [i, j] x u
      · rw [if_pos ((heq u).mpr hu), if_pos hu]
      · rw [if_neg (fun h => hu (h.1)), if_neg hu]
    rw [Finset.sum_congr rfl (fun u _ => hconv u)]
    rw [sum_cond_bij (P := fun u => agreeOff [i, j] x u)
        (ins := fun p => setBits [i, j] x (fun a _ => if h : a = i then p.1 else p.2))
        (proj := fun u => (u i, u j))
        (f := fun u => W (x i, x j) (u i, u j) * W' (u i, u j) (y i, y j))
        (fun p => AgreeOff.agreeOff_setBits [i, j] x
          (fun a _ => if h : a = i then p.1 else p.2))
        (fun p => setBits_pair_val x hij p)
        (fun u hu => setBits_pair x u hij hu)]
    rw [Finset.sum_congr rfl (fun pq _ => by rw [setBits_pair_val x hij pq])]
    rw [sum_prod_bool_eq, ← mul4_apply]
    rw [embed2_apply, if_pos hxy]
  · have hempty : ∀ u, ¬ (agreeOff [i, j] x u ∧ agreeOff [i, j] u y) := by
      intro u h
      exact hxy (AgreeOff.trans' h.1 h.2)
    rw [Finset.sum_eq_zero (fun u _ => if_neg (hempty u)), embed2_apply, if_neg hxy]

/-- The embedding of the 2x2 identity matrix is the n-qubit identity operator. -/
theorem embed1_one {n : Nat} (i : Fin n) : embed1 (1 : Matrix Bool Bool ℂ) i = 1 := by
  classical
  ext x y
  simp only [embed1_apply, Matrix.one_apply, Pi.one_apply]
  by_cases h : agreeOff [i] x y
  · rw [if_pos h]
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hne : ¬ (x i = y i) := by
        intro hh
        apply hxy
        funext a
        by_cases ha : a = i
        · rw [ha]
          exact hh
        · exact h a (by simpa using ha)
      rw [if_neg hne, if_neg hxy]
  · rw [if_neg h]
    by_cases hxy : x = y
    · exfalso
      exact h (by subst hxy; exact fun a ha => rfl)
    · rw [if_neg hxy]

/-- The embedding of the 4x4 identity matrix is the n-qubit identity operator. -/
theorem embed2_one {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    embed2 (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j = 1 := by
  classical
  ext x y
  simp only [embed2_apply, Matrix.one_apply, Pi.one_apply]
  by_cases h : agreeOff [i, j] x y
  · rw [if_pos h]
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hne : ¬ ((x i, x j) = (y i, y j)) := by
        intro hp
        rcases Prod.mk.inj hp with ⟨hih, hjh⟩
        apply hxy
        funext a
        by_cases ha : a = i
        · rw [ha]
          exact hih
        · by_cases ha' : a = j
          · rw [ha']
            exact hjh
          · exact h a (by simp [ha, ha'])
      rw [if_neg hne, if_neg hxy]
  · rw [if_neg h]
    by_cases hxy : x = y
    · exfalso
      exact h (by subst hxy; exact fun a ha => rfl)
    · rw [if_neg hxy]

theorem embed1_conjTranspose {n : Nat} (U : Matrix Bool Bool ℂ) (i : Fin n) :
    (embed1 U i).conjTranspose = embed1 U.conjTranspose i := by
  classical
  ext x y
  simp only [Matrix.conjTranspose_apply, embed1_apply]
  by_cases hxy : agreeOff [i] x y
  · simp [hxy, AgreeOff.symm hxy]
  · have hnyx : ¬ agreeOff [i] y x := fun hh => hxy (AgreeOff.symm hh)
    simp [hxy, hnyx]

theorem embed2_conjTranspose {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (i j : Fin n) : (embed2 W i j).conjTranspose = embed2 W.conjTranspose i j := by
  classical
  ext x y
  simp only [Matrix.conjTranspose_apply, embed2_apply]
  by_cases hxy : agreeOff [i, j] x y
  · simp [hxy, AgreeOff.symm hxy]
  · have hnyx : ¬ agreeOff [i, j] y x := fun hh => hxy (AgreeOff.symm hh)
    simp [hxy, hnyx]

/-- Unitarity lifts from a gate matrix to its n-qubit embedding. -/
theorem isUnitaryM_embed1 {n : Nat} (U : Matrix Bool Bool ℂ) (hU : IsUnitaryM U) (i : Fin n) :
    IsUnitaryM (embed1 U i) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [embed1_conjTranspose, embed1_mul, hU.1, embed1_one]
  · rw [embed1_conjTranspose, embed1_mul, hU.2, embed1_one]

theorem isUnitaryM_embed2 {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hW : IsUnitaryM W) {i j : Fin n} (hij : i ≠ j) : IsUnitaryM (embed2 W i j) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [embed2_conjTranspose, embed2_mul (hij := hij), hW.1, embed2_one hij]
  · rw [embed2_conjTranspose, embed2_mul (hij := hij), hW.2, embed2_one hij]

/-! ### Gates on disjoint qubits commute -/

/-- The index type of the bits selected by a support list. -/
abbrev Idx {n : Nat} (s : List (Fin n)) : Type := ∀ a : Fin n, a ∈ s → Bool

/-- Embed a gate matrix acting on the qubits listed in s into the n-qubit operator space. -/
noncomputable def embedList {n : Nat} (s : List (Fin n))
    (U : Matrix (Idx s) (Idx s) ℂ) : Operator n :=
  fun x y => if agreeOff s x y then U (bitsAt s x) (bitsAt s y) else 0

theorem embedList_apply {n : Nat} (s : List (Fin n)) (U : Matrix (Idx s) (Idx s) ℂ)
    (x y : Basis n) :
    embedList s U x y = if agreeOff s x y then U (bitsAt s x) (bitsAt s y) else 0 := by
  simp [embedList]

theorem bitsAt_mix_l {n : Nat} (s : List (Fin n)) (x y : Basis n) :
    bitsAt s (mix s x y) = bitsAt s y := by
  funext a ha
  show mix s x y a = y a
  rw [AgreeOff.mix_in s x y ha]

theorem bitsAt_mix_r {n : Nat} {s t : List (Fin n)} (hdisj : ∀ a ∈ s, ∀ b ∈ t, a ≠ b)
    (x y : Basis n) : bitsAt t (mix s x y) = bitsAt t x := by
  funext a ha
  show mix s x y a = x a
  rw [AgreeOff.mix_out s x y (fun hh => absurd rfl (hdisj a hh a ha))]

theorem embed1_eq_embedList {n : Nat} (U : Matrix Bool Bool ℂ) (i : Fin n) :
    embed1 U i = embedList [i] (fun a b => U (a i (by simp)) (b i (by simp))) := rfl

theorem embed2_eq_embedList {n : Nat} (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n) :
    embed2 W i j =
      embedList [i, j]
        (fun a b => W (a i (by simp), a j (by simp)) (b i (by simp), b j (by simp))) := rfl

/-- The entrywise form of a product of gates whose supports are disjoint. -/
theorem embedList_mul_disjoint_apply {n : Nat} {s t : List (Fin n)}
    (hdisj : ∀ a ∈ s, ∀ b ∈ t, a ≠ b)
    (U : Matrix (Idx s) (Idx s) ℂ) (V : Matrix (Idx t) (Idx t) ℂ) (x y : Basis n) :
    (embedList s U * embedList t V) x y =
      if agreeOff (s ++ t) x y
        then U (bitsAt s x) (bitsAt s y) * V (bitsAt t x) (bitsAt t y) else 0 := by
  classical
  rw [Matrix.mul_apply]
  have hsum : (∑ u : Basis n, embedList s U x u * embedList t V u y)
      = ∑ u : Basis n, if agreeOff s x u ∧ agreeOff t u y
          then U (bitsAt s x) (bitsAt s u) * V (bitsAt t u) (bitsAt t y) else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases h₁ : agreeOff s x u <;> by_cases h₂ : agreeOff t u y <;>
      simp [h₁, h₂, embedList_apply]
  rw [hsum]
  by_cases hxy : agreeOff (s ++ t) x y
  · have huniq : ∀ u, (agreeOff s x u ∧ agreeOff t u y) ↔ u = mix s x y :=
      fun u => AgreeOff.mix_unique hdisj x y u hxy
    rw [sum_cond_unique _ _ huniq _]
    rw [bitsAt_mix_l s x y, bitsAt_mix_r hdisj x y, if_pos hxy]
  · have hempty : ∀ u, ¬ (agreeOff s x u ∧ agreeOff t u y) := by
      intro u h
      exact hxy (AgreeOff.agreeOff_append h.1 h.2)
    have hz : (∑ u : Basis n, if agreeOff s x u ∧ agreeOff t u y
        then U (bitsAt s x) (bitsAt s u) * V (bitsAt t u) (bitsAt t y) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      by_cases h : agreeOff s x u ∧ agreeOff t u y
      · exact absurd h (hempty u)
      · rw [if_neg h]
    rw [hz, if_neg hxy]

/-- Gates on disjoint sets of qubits commute. -/
theorem embedList_comm {n : Nat} {s t : List (Fin n)} (hdisj : ∀ a ∈ s, ∀ b ∈ t, a ≠ b)
    (U : Matrix (Idx s) (Idx s) ℂ) (V : Matrix (Idx t) (Idx t) ℂ) :
    embedList s U * embedList t V = embedList t V * embedList s U := by
  classical
  ext x y
  rw [embedList_mul_disjoint_apply hdisj U V,
    embedList_mul_disjoint_apply (fun a ha b hb => Ne.symm (hdisj b hb a ha)) V U]
  by_cases hxy : agreeOff (s ++ t) x y
  · rw [if_pos hxy, if_pos (AgreeOff.agreeOff_swap x y hxy)]
    ring
  · rw [if_neg hxy, if_neg (fun hh => hxy (AgreeOff.agreeOff_swap x y hh))]

/-- Scalar multiplication commutes with embedding. -/
theorem embed1_smul {n : Nat} (z : ℂ) (U : Matrix Bool Bool ℂ) (i : Fin n) :
    embed1 (z • U) i = z • embed1 U i := by
  classical
  ext x y
  by_cases h : agreeOff [i] x y <;> simp [h, embed1_apply, Pi.smul_apply, smul_zero]

theorem embed2_smul {n : Nat} (z : ℂ) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (i j : Fin n) : embed2 (z • W) i j = z • embed2 W i j := by
  classical
  ext x y
  by_cases h : agreeOff [i, j] x y <;> simp [h, embed2_apply, Pi.smul_apply, smul_zero]

theorem embed1_embed1_comm {n : Nat} {i j : Fin n} (hij : i ≠ j)
    (U V : Matrix Bool Bool ℂ) : embed1 U i * embed1 V j = embed1 V j * embed1 U i := by
  classical
  rw [embed1_eq_embedList, embed1_eq_embedList]
  exact embedList_comm (by
    intro a ha b hb
    simp only [List.mem_singleton] at ha hb
    rw [ha, hb]
    exact hij) _ _

theorem embed1_embed2_comm {n : Nat} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (U : Matrix Bool Bool ℂ) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    embed1 U i * embed2 W j k = embed2 W j k * embed1 U i := by
  classical
  simp only [embed1_eq_embedList, embed2_eq_embedList]
  refine embedList_comm ?_ _ _
  intro a ha b hb
  have ha' : a = i := by simpa using ha
  have hb' : b = j ∨ b = k := by simpa using hb
  subst ha'
  rcases hb' with rfl | rfl
  · exact hij
  · exact hik

theorem embed2_embed1_comm {n : Nat} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (U : Matrix Bool Bool ℂ) (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    embed2 W i j * embed1 U k = embed1 U k * embed2 W i j := by
  apply Eq.symm
  apply embed1_embed2_comm
  · exact Ne.symm hik
  · exact Ne.symm hjk
  · exact hij

theorem embed2_embed2_comm {n : Nat} {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l)
    (W₁ W₂ : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    embed2 W₁ i j * embed2 W₂ k l = embed2 W₂ k l * embed2 W₁ i j := by
  classical
  simp only [embed2_eq_embedList]
  refine embedList_comm ?_ _ _
  intro a ha b hb
  have ha' : a = i ∨ a = j := by simpa using ha
  have hb' : b = k ∨ b = l := by simpa using hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact hik
  · exact hil
  · exact hjk
  · exact hjl

end Quantum