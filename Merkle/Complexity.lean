import Merkle.Proof

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Concrete complexity of Merkle operations

This file defines structural hash-invocation costs and proves their **exact closed forms**.
The model follows full hashing, proof generation, and proof folding separately; it is not a
semantics or a timing model of the Lean compiler.

Lean core has no asymptotic-analysis library, so we formalise the notion we need directly:

* `Merkle.IsBigO f g` is the standard definition specialised to functions on the naturals:
  `f` is eventually bounded by a constant multiple of `g`.
* Every cost counts **hash invocations** in the mathematical specification of the operation
  (one unit per call of `MerkleHash.leaf` or `NodeAlgebra.node`). This is the cost model
  that matters for a hash-based commitment: it is implementation-independent, and it is what
  the theorems below are about. We make no claim about wall-clock time, memory, or the step
  counts of the generated code.

## Main results

* `Tree.hashCost_eq_pow` - hashing a whole depth-`n` tree costs exactly `2 ^ (n + 1) - 1`
  hashes: `2 ^ n` leaf hashes and `2 ^ n - 1` node hashes.
* `Tree.hashCost_eq_leaves` - the same number is `2 * t.leaves.length - 1`, i.e. **linear in
  the number of leaves** - the honest form of the `O(N)` rehash cost.
* `Path.cost_eq`, `Proof.cost_eq` - addressing a leaf and verifying a proof each cost exactly
  `n` steps, and `n = Nat.log2 N`, i.e. **logarithmic in the number of leaves**.
* `not_pow_isBigO_linear` - `2 ^ n` is **not** `O n`. This is the content of the claim that a
  full rehash is super-linear in depth. Folding an already available path costs `O(n)`
  hashes; generating that path from an uncached tree costs `O(2 ^ n)` hashes.
* `Proof.digestCount_eq` - an authentication path for a `2 ^ n`-leaf tree carries exactly
  `n = log2 N` sibling digests. This counts fields of this proof format, without a lower
  bound on alternative encodings.
-/

namespace Merkle

/-- **Big-O on the naturals.** `IsBigO f g` means `f` is eventually bounded by a constant
multiple of `g`.

This is the standard definition restricted to total functions `Nat → Nat`, which is all this
library needs: every cost we count is a function of the tree depth. `c` is the
multiplicative constant and `N₀` the threshold beyond which the bound holds. -/
def IsBigO (f g : Nat → Nat) : Prop := ∃ c N₀, ∀ n, N₀ ≤ n → f n ≤ c * g n

/-- Every function is big-O of itself (constant `1`). -/
theorem IsBigO.refl (f : Nat → Nat) : IsBigO f f :=
  ⟨1, 0, fun n _ => by rw [Nat.one_mul]; exact Nat.le_refl _⟩

/-- Big-O is transitive: the constants multiply. -/
theorem IsBigO.trans {f g h : Nat → Nat}
    (hf : IsBigO f g) (hg : IsBigO g h) : IsBigO f h := by
  obtain ⟨c₁, N₁, h₁⟩ := hf
  obtain ⟨c₂, N₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  calc f n ≤ c₁ * g n := h₁ n hn₁
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul_left _ (h₂ n hn₂)
    _ = (c₁ * c₂) * h n := (Nat.mul_assoc _ _ _).symm

/-- Scaling the left-hand side by a constant preserves the bound. -/
theorem IsBigO.const_mul {f g : Nat → Nat}
    (h : IsBigO f g) (k : Nat) : IsBigO (fun n => k * f n) g := by
  obtain ⟨c, N₀, bound⟩ := h
  refine ⟨k * c, N₀, fun n hn => ?_⟩
  show k * f n ≤ k * c * g n
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left k (bound n hn)
/-- Scaling the right-hand side by a *positive* constant preserves the bound. The
positivity is needed: `O` of the zero function bounds only eventually-zero functions. -/
theorem IsBigO.mul_const {f g : Nat → Nat}
    (h : IsBigO f g) {k : Nat} (hk : 0 < k)
    : IsBigO f (fun n => k * g n) := by
  obtain ⟨c, N₀, bound⟩ := h
  refine ⟨c, N₀, fun n hn => ?_⟩
  exact Nat.le_trans (bound n hn)
    (Nat.mul_le_mul_left c (Nat.le_mul_of_pos_left _ hk))
/-- Big-O is monotone in the right-hand side. -/
theorem IsBigO.mono {f g h : Nat → Nat}
    (hgf : ∀ n, g n ≤ h n) (hf : IsBigO f g) : IsBigO f h := by
  obtain ⟨c, N₀, bound⟩ := hf
  exact ⟨c, N₀, fun n hn => Nat.le_trans (bound n hn) (Nat.mul_le_mul_left c (hgf n))⟩

/-- A pointwise bound by `g` is a big-O bound. -/
theorem isBigO_of_forall {f g : Nat → Nat} (h : ∀ n, f n ≤ g n) : IsBigO f g :=
  ⟨1, 0, fun n _ => by rw [Nat.one_mul]; exact h n⟩

/-- `2 ≤ 2 ^ k` as soon as `k ≥ 1`. -/
private theorem two_le_two_pow_of_pos : ∀ k : Nat, 1 ≤ k → 2 ≤ 2 ^ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by omega)
  rw [Nat.pow_succ, Nat.mul_two]
  omega

/-- The linear term needed for the induction below. -/
private theorem lin_bound : ∀ j : Nat, 2 * j + 11 ≤ 2 ^ (j + 5) := by
  intro j
  induction j with
  | zero => decide
  | succ m ih =>
      have hb : 2 ≤ 2 ^ (m + 5) := two_le_two_pow_of_pos (m + 5) (by omega)
      have hexp : m + 1 + 5 = m + 5 + 1 := by omega
      rw [hexp, Nat.pow_succ, Nat.mul_two]
      show 2 * m + 11 + 2 ≤ 2 ^ (m + 5) + 2 ^ (m + 5)
      omega

/-- `(a+1)² = a² + 2a + 1`, stated so `omega` can finish it. -/
private theorem sq_shift : ∀ a : Nat, (a + 1) * (a + 1) = a * a + (2 * a + 1) := by
  intro a
  have h : (a + 1) * (a + 1) = a * a + a + (a + 1) := by
      rw [Nat.add_mul, Nat.mul_add]
      omega
  rw [h]
  omega

/-- `n² < 2ⁿ` for every `n ≥ 5`, via a shifted induction with no side conditions. -/
private theorem sq_lt_two_pow_shift : ∀ j : Nat, (j + 5) * (j + 5) < 2 ^ (j + 5) := by
  intro j
  induction j with
  | zero => decide
  | succ m ih =>
      have h1 := sq_shift (m + 5)
      have h2 := lin_bound m
      have hexp : m + 1 + 5 = m + 5 + 1 := by omega
      rw [hexp, Nat.pow_succ, Nat.mul_two]
      omega

private theorem sq_lt_two_pow : ∀ n : Nat, 5 ≤ n → n * n < 2 ^ n := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
  exact sq_lt_two_pow_shift j

/-- `Nat.log2 (2 ^ n) = n`, proved without classical choice. -/
private theorem log2_two_pow : ∀ n : Nat, (2 ^ n).log2 = n := by
  intro n
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hne : 2 ^ n ≠ 0 := by omega
  rw [Nat.log2_eq_iff hne]
  refine ⟨Nat.le_refl _, ?_⟩
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
  omega
/-- **`2 ^ n` eventually dominates every linear function.**

For any constant `c` and threshold `N₀` there is a depth `n ≥ N₀` with `c * n < 2 ^ n`. -/
theorem exists_forall_ge_mul_lt_two_pow :
    ∀ c N₀ : Nat, ∃ n, N₀ ≤ n ∧ c * n < 2 ^ n := by
  intro c N₀
  refine ⟨c + N₀ + 5, by omega, ?_⟩
  have hle : c ≤ c + N₀ + 5 := by omega
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hle)
    (sq_lt_two_pow _ (by omega))

/-- **`2 ^ n` is not `O n`.** No constant multiple of the depth bounds the number of leaves.

Read against `Tree.hashCost_eq_pow`: recomputing a root from scratch is genuinely
super-linear in the depth. Combined with `Path.cost_eq` and `Proof.cost_eq`, this is the
sense in which folding an available authentication path (`n` node hashes plus one leaf hash)
beats a full rehash (`2 ^ (n + 1) - 1` hashes). The cost of generating that path is separate. -/
theorem not_pow_isBigO_linear : ¬ IsBigO (fun n => 2 ^ n) (fun n => n) := by
  intro ⟨c, N₀, bound⟩
  obtain ⟨n, hn₀, hn⟩ := exists_forall_ge_mul_lt_two_pow c N₀
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hn (bound n hn₀))

/-- Consequently a full rehash is not `O n` either. -/
theorem not_hashCost_isBigO_linear :
    ¬ IsBigO (fun n => 2 ^ (n + 1) - 1) (fun n => n) := by
  intro h
  obtain ⟨c, N₀, bound⟩ := h
  obtain ⟨n, hn₀, hn⟩ := exists_forall_ge_mul_lt_two_pow (2 * c) N₀
  have h₁ : 2 ^ (n + 1) - 1 ≤ c * n := bound n hn₀
  have h₂ : 2 ^ n ≤ 2 ^ (n + 1) - 1 := by
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
      omega
  have h₃ : c * n < 2 ^ n :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right n (by omega : c ≤ 2 * c)) hn
  omega


section
variable {α β : Type}

/-- **Hash-invocation cost of a whole tree.** `Tree.hashCost t` is the number of hash
invocations `rootHash` performs on `t`: one `leaf` hash per leaf and one `node` hash per
internal node. -/
def Tree.hashCost : Tree α n → Nat
  | Tree.leaf _ => 1
  | Tree.node l r => 1 + l.hashCost + r.hashCost

/-- **Branch cost of a path.** `Path.cost p` is the number of branch decisions a lookup or
update must make to reach `p`, i.e. one per level of the tree. -/
def Path.cost : Path n → Nat
  | Path.nil => 0
  | Path.left p => 1 + p.cost
  | Path.right p => 1 + p.cost

/-- **Hash cost of a proof.** `Proof.cost h` is the number of `node` hashes that `verify h`
performs while folding an authentication path up to a root. -/
def Proof.cost : Proof β n → Nat
  | Proof.nil => 0
  | Proof.left h _ => 1 + h.cost
  | Proof.right h _ => 1 + h.cost

/-- **Number of digests carried by a proof.** `Proof.digestCount` counts the sibling digests
stored in an authentication path, which is its wire size in digest units. -/
def Proof.digestCount : Proof β n → Nat
  | Proof.nil => 0
  | Proof.left h _ => 1 + Proof.digestCount h
  | Proof.right h _ => 1 + Proof.digestCount h

/-- A depth-`n` tree has `2 ^ (n + 1) - 1` nodes in total, so a full hash costs exactly that
many invocations: `2 ^ n` leaf hashes plus `2 ^ n - 1` node hashes. -/
theorem Tree.hashCost_eq_pow : ∀ (n : Nat) (t : Tree α n),
    t.hashCost = 2 ^ (n + 1) - 1
  | 0, Tree.leaf _ => rfl
  | n + 1, Tree.node l r => by
      show 1 + l.hashCost + r.hashCost = 2 ^ (n + 1 + 1) - 1
      rw [Tree.hashCost_eq_pow n l, Tree.hashCost_eq_pow n r]
      have h : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
      rw [h]
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
      omega

/-- The same cost stated the way it should be: **linear in the number of leaves**.
`rootHash` touches every leaf exactly once and every internal node exactly once, so its cost
is `2 * |leaves| - 1`. This is the precise form of "O(N)", where `N = 2 ^ n` is the size of
the committed data rather than the depth of the tree. -/
theorem Tree.hashCost_eq_leaves : ∀ (n : Nat) (t : Tree α n),
    t.hashCost = 2 * t.leaves.length - 1 := by
  intro n
  induction n with
  | zero => intro t; cases t with | leaf a => simp [Tree.hashCost, Tree.leaves]
  | succ n ih =>
      intro t
      cases t with
      | node l r =>
          show 1 + l.hashCost + r.hashCost = 2 * (l.leaves ++ r.leaves).length - 1
          rw [ih l, ih r, List.length_append]
          have hl : 1 ≤ l.leaves.length := by
            rw [Tree.leaves_length]; exact Nat.one_le_pow _ _ (by omega)
          have hr : 1 ≤ r.leaves.length := by
            rw [Tree.leaves_length]; exact Nat.one_le_pow _ _ (by omega)
          omega

/-- A path of length `n` costs exactly `n` branch steps. -/
theorem Path.cost_eq : ∀ (n : Nat) (p : Path n), p.cost = n := by
  intro n
  induction n with
  | zero => intro p; cases p; rfl
  | succ n ih => intro p; cases p with
      | left q => show 1 + Path.cost q = n + 1; rw [ih q]; omega
      | right q => show 1 + Path.cost q = n + 1; rw [ih q]; omega

/-- Hash invocations needed to generate a proof from an uncached tree. Every sibling
subtree is rehashed by `ofTree` (or `Sig.ofTree`). -/
def Tree.proofGenerationCost : Tree α n → Path n → Nat
  | Tree.leaf _, Path.nil => 0
  | Tree.node l r, Path.left p => l.proofGenerationCost p + r.hashCost
  | Tree.node l r, Path.right p => r.proofGenerationCost p + l.hashCost

/-- Generating the old proof and folding a newly hashed leaf costs a full rehash.
The logarithmic update bound applies when the authentication path is already available. -/
theorem Tree.proofGenerationCost_add_depth :
    ∀ (n : Nat) (t : Tree α n) (p : Path n),
      t.proofGenerationCost p + n + 1 = t.hashCost := by
  intro n
  induction n with
  | zero => intro t p; cases t; cases p; rfl
  | succ n ih =>
      intro t p
      cases t with
      | node l r =>
          cases p with
          | left p =>
              have h := ih l p
              change l.proofGenerationCost p + r.hashCost + (n + 1) + 1 =
                1 + l.hashCost + r.hashCost
              omega
          | right p =>
              have h := ih r p
              change r.proofGenerationCost p + l.hashCost + (n + 1) + 1 =
                1 + l.hashCost + r.hashCost
              omega

/-- Exact proof-generation cost, excluding the new leaf and its verification fold. -/
theorem Tree.proofGenerationCost_eq (t : Tree α n) (p : Path n) :
    t.proofGenerationCost p = 2 ^ (n + 1) - 1 - (n + 1) := by
  have h := Tree.proofGenerationCost_add_depth n t p
  rw [Tree.hashCost_eq_pow] at h
  omega

/-- A depth-`n` path is addressed by exactly `n` direction bits. -/
theorem Path.length_toBits : ∀ (n : Nat) (p : Path n), (Path.toBits p).length = n := by
  intro n
  induction n with
  | zero => intro p; cases p; rfl
  | succ n ih => intro p; cases p with
      | left q => exact congrArg Nat.succ (ih q)
      | right q => exact congrArg Nat.succ (ih q)

/-- The branch cost is the number of direction bits, i.e. the length of the bit vector that
addresses the leaf. -/
theorem Path.cost_eq_length_toBits : ∀ (n : Nat) (p : Path n),
    p.cost = (Path.toBits p).length := by
  intro n p
  rw [Path.cost_eq n p, Path.length_toBits n p]

/-- Verifying a proof costs exactly `n` node hashes - one per level, plus the single hash of
the claimed leaf value that the caller supplies. -/
theorem Proof.cost_eq : ∀ (n : Nat) (h : Proof β n), h.cost = n := by
  intro n
  induction n with
  | zero => intro h; cases h; rfl
  | succ n ih => intro h; cases h with
      | left h _ => show 1 + Proof.cost h = n + 1; rw [ih h]; omega
      | right h _ => show 1 + Proof.cost h = n + 1; rw [ih h]; omega

/-- **Exact size of this proof format.** A depth-`n` authentication path carries exactly
`n` sibling digests. This theorem counts fields of `Proof`; it makes no optimality claim about
compressed proofs or alternative certificate formats. -/
theorem Proof.digestCount_eq : ∀ (n : Nat) (h : Proof β n), h.digestCount = n := by
  intro n
  induction n with
  | zero => intro h; cases h; rfl
  | succ n ih => intro h; cases h with
      | left h _ => show 1 + Proof.digestCount h = n + 1; rw [ih h]; omega
      | right h _ => show 1 + Proof.digestCount h = n + 1; rw [ih h]; omega

/-- Equivalently, in terms of the number of leaves: a proof for a tree with `N = 2 ^ n`
leaves has size `log2 N`. -/
theorem Proof.digestCount_eq_log2 : ∀ (n : Nat) (h : Proof β n),
    h.digestCount = Nat.log2 (2 ^ n) := by
  intro n h
  rw [log2_two_pow, Proof.digestCount_eq n h]

/-- **Full rehash is O(N) in the number of leaves**, equivalently `O(2 ^ n)` in the depth. -/
theorem isBigO_hashCost_pow : IsBigO (fun n => 2 ^ (n + 1) - 1) (fun n => 2 ^ n) := by
  refine ⟨2, 0, fun n _ => ?_⟩
  show 2 ^ (n + 1) - 1 ≤ 2 * 2 ^ n
  rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [Nat.pow_succ, Nat.mul_two]]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- **Depth is Theta(log N)**, first direction. -/
theorem isBigO_log2_pow : IsBigO (fun n => n) (fun n => Nat.log2 (2 ^ n)) :=
  isBigO_of_forall (fun n => by rw [log2_two_pow]; exact Nat.le_refl _)

/-- **Depth is Theta(log N)**, converse direction. -/
theorem isBigO_pow_log2 : IsBigO (fun n => Nat.log2 (2 ^ n)) (fun n => n) :=
  isBigO_of_forall (fun n => by rw [log2_two_pow]; exact Nat.le_refl _)

/-- A lookup costs `p.cost = n` steps, so it is logarithmic in the number of leaves: the
number of nodes a lookup can visit is bounded by the depth. -/
theorem Path.cost_le_log2 : ∀ (n : Nat) (p : Path n),
    p.cost ≤ Nat.log2 (2 ^ n) := by
  intro n p
  rw [log2_two_pow, Path.cost_eq n p]
  exact Nat.le_refl _

/-- **Verification is logarithmic**: folding a proof of a `2 ^ n`-leaf tree costs `n`
hashes, i.e. `log2 N`. -/
theorem Proof.cost_isBigO_log : ∀ (n : Nat) (h : Proof β n),
    IsBigO (fun _ => h.cost) (fun _ => Nat.log2 (2 ^ n)) := by
  intro n h
  refine isBigO_of_forall (f := fun _ => h.cost) (g := fun _ => Nat.log2 (2 ^ n)) ?_
  intro m
  rw [log2_two_pow, Proof.cost_eq n h]
  exact Nat.le_refl _

/-- **Logarithmic is dominated by linear**, so every O(log N) operation is also O(N) - the
trivial but often-quoted direction. -/
theorem Nat.le_two_pow : ∀ n : Nat, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [Nat.pow_succ, Nat.mul_two]
      omega

/-- **Logarithmic is dominated by linear**, so every O(log N) operation is also O(N) - the
trivial but often-quoted direction. -/
theorem isBigO_linear_pow : IsBigO (fun n => n) (fun n => 2 ^ n) :=
  isBigO_of_forall (fun n => Nat.le_two_pow n)

end

end Merkle
