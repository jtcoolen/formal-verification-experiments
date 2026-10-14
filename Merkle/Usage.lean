import Merkle.Free

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
# Using the Merkle library: worked application examples

`Merkle/Basic.lean` and `Merkle/Proof.lean` state *what* a Merkle tree guarantees. This file
shows *how it gets used*: every declaration is something a real application would write, paired
with the theorem that application actually needs. Everything is pure Lean core - no Mathlib -
and every example is kernel-checked (`rfl`, `decide`, or a proved theorem), never prose.

## Main results

* **Vectors as trees.** `ofLeaves` builds a `Tree α n` from a flat list of exactly `2 ^ n`
  entries; `leaves_ofLeaves` and `ofLeaves_leaves` are the two round trips, and `get_ofLeaves`
  identifies the entry a path reads out. The right index is `leafIndex`, the left-to-right
  position - *not* `Path.toNat`, which numbers paths root-bit-first and so is a bit reversal of
  the leaf order. `pathOfIndex` / `leafIndex_pathOfIndex` give the inverse direction.
* **Sparse trees.** `fill` is the all-default subtree and `fillHash` its digest, computed with
  `n` uses of `node` instead of `2 ^ n` uses of `leaf` (`rootHash_fill`, `get_fill`,
  `leaves_fill`, `fill_eq_ofLeaves`).
* **Commitments.** `commit` hashes a vector and `commit_inj` says equal commits force equal
  vectors - the binding property a ledger or transparency log needs.
* **Batch updates.** `updateAll` folds a list of `(path, value)` writes. `get_updateAll_notMem`
  says untouched leaves are untouched, `get_updateAll_last` says the last write wins, and
  `rootHash_updateAll` says the batched root equals folding `verify` over the individual
  incremental updates.
* **Transparency log.** `history_binding` (equal heads agree at every position),
  `extension_changes_root` / `extension_preserves_root` (exactly the writes that change an entry
  move the head), and `forged_inclusion_rejected`.
* **Set certificates.** `Claim` bundles `(path, value, proof)`; `multi_inclusion` turns a list
  of verified, well-formed claims into pointwise agreement with the tree, `honestClaims` builds
  a certificate that always verifies, and `allVerifyB` is the decidable test a client runs.
* **Concrete scenarios** over `Dig Nat`, `Dig String` and `Dig (Fin 256)`: a four-account
  balance ledger with an honest transfer and a rejected forgery, a sixteen-entry log with a
  checked and a tampered inclusion proof, and a key-value store whose lookups are independent.
-/

namespace Merkle.Usage

open Merkle.Free

/-! ### Reading and writing vectors as trees -/

/-- A list of length `2 ^ 0 = 1` cannot have two or more elements, and cannot be empty. These
two facts are the side conditions of `ofLeaves` at depth zero. Phrased as rewrites rather than
`simp` calls so that no decidability of propositional equality - and hence no classical choice -
is dragged into the proofs below. -/
theorem length_cons_pow_zero_false {α : Type} (a b : α) (u : List α) :
    ¬ ((a :: b :: u).length = 2 ^ 0) := by
  intro h
  rw [List.length_cons, List.length_cons, Nat.pow_zero] at h
  omega

theorem length_nil_pow_zero_false {α : Type} : ¬ (([] : List α).length = 2 ^ 0) := by
  intro h
  rw [List.length_nil, Nat.pow_zero] at h
  omega
/-- The left-to-right position of the leaf addressed by a path.

`Path.toNat` numbers paths with the *root* branch as the most significant bit, which is the
reverse of the order in which `Tree.leaves` lists them. `leafIndex` is the index that matches
`leaves`: taking the right branch at depth `m + 1` skips the whole left subtree, i.e. `2 ^ m`
leaves. -/
def leafIndex : (n : Nat) → Path n → Nat
  | 0, _ => 0
  | m + 1, Path.left p => leafIndex m p
  | m + 1, Path.right p => 2 ^ m + leafIndex m p

/-- A path never addresses a position beyond the end of the vector. -/
theorem leafIndex_lt : ∀ (n : Nat) (p : Path n), leafIndex n p < 2 ^ n := by
  intro n
  induction n with
  | zero => intro p; cases p; simp [leafIndex]
  | succ n ih =>
      intro p
      cases p with
      | left p =>
          have h := ih p
          have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          show leafIndex n p < 2 ^ (n + 1)
          omega
      | right p =>
          have h := ih p
          have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          show 2 ^ n + leafIndex n p < 2 ^ (n + 1)
          omega

/-- Build the depth-`n` tree whose leaves, left to right, are the entries of `l`.

The length hypothesis is an argument of the function, so a wrongly sized vector cannot be turned
into a tree at all: `l.length = 2 ^ n` is exactly the precondition a caller must discharge. -/
def ofLeaves : (n : Nat) → (l : List α) → l.length = 2 ^ n → Tree α n
  | 0, [a], _ => Tree.leaf a
  | 0, [], h => absurd h (by simp)
  | n + 1, l, h =>
      Tree.node (ofLeaves n (l.take (2 ^ n)) (by rw [List.length_take, h]; omega))
        (ofLeaves n (l.drop (2 ^ n)) (by rw [List.length_drop, h]; omega))

/-- Round trip one way: the leaves of a tree built from `l` are `l`. -/
theorem leaves_ofLeaves : ∀ (n : Nat) (l : List α) (h : l.length = 2 ^ n),
    (ofLeaves n l h).leaves = l := by
  intro n
  induction n with
  | zero =>
      intro l h
      cases l with
      | nil => exact absurd h length_nil_pow_zero_false
      | cons a t =>
          cases t with
          | nil => rfl
          | cons b u => exact absurd h (length_cons_pow_zero_false a b u)
  | succ n ih =>
      intro l h
      show (ofLeaves n (l.take (2 ^ n)) _).leaves ++ (ofLeaves n (l.drop (2 ^ n)) _).leaves = l
      rw [ih, ih]
      exact List.take_append_drop _ _

/-- A tree is determined by its leaf vector: the `leaves` analogue of `Tree.get_injective`. -/
theorem leaves_injective : ∀ (n : Nat) (t₁ t₂ : Tree α n), t₁.leaves = t₂.leaves → t₁ = t₂ := by
  intro n
  induction n with
  | zero =>
      intro t₁ t₂ h
      cases t₁ with
      | leaf a =>
          cases t₂ with
          | leaf b =>
              have : a = b := (List.cons.inj h).1
              subst this
              rfl
  | succ n ih =>
      intro t₁ t₂ h
      cases t₁ with
      | node l₁ r₁ =>
          cases t₂ with
          | node l₂ r₂ =>
              have e1 : l₁.leaves ++ r₁.leaves = l₂.leaves ++ r₂.leaves := h
              have lel₁ : 2 ^ n ≤ l₁.leaves.length := by
                have hh := Tree.leaves_length n l₁
                omega
              have lel₂ : 2 ^ n ≤ l₂.leaves.length := by
                have hh := Tree.leaves_length n l₂
                omega
              have hle₁ : l₁.leaves.length ≤ 2 ^ n := by
                have hh := Tree.leaves_length n l₁
                omega
              have hle₂ : l₂.leaves.length ≤ 2 ^ n := by
                have hh := Tree.leaves_length n l₂
                omega
              have hl : l₁.leaves = l₂.leaves := by
                have key := congrArg (List.take (2 ^ n)) e1
                rw [List.take_append_of_le_length (i := 2 ^ n) lel₁,
                    List.take_append_of_le_length (i := 2 ^ n) lel₂] at key
                rw [List.take_of_length_le hle₁, List.take_of_length_le hle₂] at key
                exact key
              have hr : r₁.leaves = r₂.leaves := by
                have key := congrArg (List.drop (2 ^ n)) e1
                rw [List.drop_append_of_le_length (i := 2 ^ n) lel₁,
                    List.drop_append_of_le_length (i := 2 ^ n) lel₂] at key
                rw [List.drop_of_length_le hle₁, List.drop_of_length_le hle₂] at key
                rw [List.nil_append, List.nil_append] at key
                exact key
              rw [ih l₁ l₂ hl, ih r₁ r₂ hr]

/-- Round trip the other way: converting a tree to a vector and back is the identity. -/
theorem ofLeaves_leaves : ∀ (n : Nat) (t : Tree α n),
    ofLeaves n t.leaves (Tree.leaves_length n t) = t := by
  intro n t
  refine leaves_injective n (ofLeaves n t.leaves (Tree.leaves_length n t)) t ?_
  exact leaves_ofLeaves n t.leaves (Tree.leaves_length n t)

/-- `ofLeaves` is a function of the vector: equal lists give equal trees, whatever the proofs. -/
theorem ofLeaves_eq {n : Nat} {l₁ l₂ : List α} (h₁ : l₁.length = 2 ^ n) (h₂ : l₂.length = 2 ^ n)
    (heq : l₁ = l₂) : ofLeaves n l₁ h₁ = ofLeaves n l₂ h₂ := by
  subst heq
  rfl

/-- `getD` at an in-bounds index ignores the fallback. -/
theorem getD_eq_get {α : Type} (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l.getD i d = l.get ⟨i, h⟩ := by
  induction l generalizing i with
  | nil => cases h
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have h' : i < t.length := by
            rw [List.length_cons] at h
            omega
          exact ih i h'

/-- Reading a tree built from `l` at `p` returns the `leafIndex n p`-th entry of `l`. -/
theorem get_ofLeaves : ∀ (n : Nat) (l : List α) (h : l.length = 2 ^ n) (p : Path n) (d : α),
    (ofLeaves n l h).get p = l.getD (leafIndex n p) d := by
  intro n
  induction n with
  | zero =>
      intro l h p d
      cases l with
      | nil => exact absurd h length_nil_pow_zero_false
      | cons a t =>
          cases t with
          | nil =>
              cases p with
              | nil => rfl
          | cons b u => exact absurd h (length_cons_pow_zero_false a b u)
  | succ n ih =>
      intro l h p d
      cases p with
      | left p =>
          show (ofLeaves n (l.take (2 ^ n)) _).get p = l.getD (leafIndex n p) d
          rw [ih]
          have hk : leafIndex n p < 2 ^ n := leafIndex_lt n p
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt hk]
      | right p =>
          show (ofLeaves n (l.drop (2 ^ n)) _).get p = l.getD (2 ^ n + leafIndex n p) d
          rw [ih, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The index-bounded form: the read is a genuine in-bounds `List.get`. -/
theorem get_ofLeaves_get : ∀ (n : Nat) (l : List α) (h : l.length = 2 ^ n) (p : Path n),
    (ofLeaves n l h).get p =
      l.get ⟨leafIndex n p, by rw [h]; exact leafIndex_lt n p⟩ := by
  intro n l h p
  have hb : leafIndex n p < l.length := by rw [h]; exact leafIndex_lt n p
  rw [get_ofLeaves (d := l.get ⟨leafIndex n p, hb⟩)]
  exact getD_eq_get l (leafIndex n p) hb _

/-- The path addressing the `i`-th leaf of a depth-`n` tree: the inverse of `leafIndex`. -/
def pathOfIndex : (i : Nat) → (n : Nat) → i < 2 ^ n → Path n
  | _, 0, _ => Path.nil
  | i, n + 1, h =>
      if hi : i < 2 ^ n then Path.left (pathOfIndex i n hi)
      else Path.right (pathOfIndex (i - 2 ^ n) n (by omega))

/-- `pathOfIndex` really addresses position `i`. -/
theorem leafIndex_pathOfIndex : ∀ (i : Nat) (n : Nat) (h : i < 2 ^ n),
    leafIndex n (pathOfIndex i n h) = i := by
  intro i n
  induction n generalizing i with
  | zero =>
      intro h
      have : i = 0 := by omega
      subst this
      rfl
  | succ n ih =>
      intro h
      unfold pathOfIndex
      split
      · rename_i hi
        exact ih i hi
      · rename_i hi
        show 2 ^ n + leafIndex n (pathOfIndex (i - 2 ^ n) n _) = i
        rw [ih]
        omega

/-- Kernel check: building a depth-two tree from a flat vector gives the expected tree. -/
example : ofLeaves 2 [0, 1, 2, 3] rfl =
    Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)) := rfl

/-- Kernel check: `Path.toNat` and `leafIndex` disagree exactly by the bit reversal, and it is
`leafIndex` that matches the leaf order. -/
example : (Path.left (Path.right Path.nil)).toNat = 2 ∧
    leafIndex 2 (Path.left (Path.right Path.nil)) = 1 := ⟨rfl, rfl⟩

example : (ofLeaves 2 [0, 1, 2, 3] rfl).get (Path.left (Path.right Path.nil)) = 1 := rfl

/-! ### Sparse trees: the all-default subtree -/

/-- The depth-`n` tree every one of whose `2 ^ n` leaves holds `a`. -/
def fill : (n : Nat) → α → Tree α n
  | 0, a => Tree.leaf a
  | n + 1, a => Tree.node (fill n a) (fill n a)

/-- The root digest of `fill`, computed *without* building the tree: `n` uses of `node` on one
repeated digest, instead of `2 ^ n` uses of `leaf` plus `2 ^ n - 1` uses of `node`.

This is the whole reason sparse Merkle trees are cheap. A tree with a million default leaves is
committed to by about twenty hashes, and an inclusion proof inside it is checked by combining
`fillHash` values for the untouched sibling subtrees rather than materialising them. -/
def fillHash {α β : Type} [m : MerkleHash α β] : (n : Nat) → α → β
  | 0, a => m.leaf a
  | n + 1, a => m.node (fillHash (m := m) n a) (fillHash (m := m) n a)

/-- Every leaf of `fill` is the default value, whatever path you ask for. -/
theorem get_fill : ∀ (n : Nat) (a : α) (p : Path n), (fill n a).get p = a := by
  intro n
  induction n with
  | zero => intro a p; cases p; rfl
  | succ n ih =>
      intro a p
      cases p with
      | left p => exact ih a p
      | right p => exact ih a p

/-- The cheap digest really is the root digest of the expensive tree. -/
theorem rootHash_fill : ∀ (n : Nat) (a : α) [m : MerkleHash α β],
    rootHash (m := m) (fill n a) = fillHash (m := m) n a := by
  intro n
  induction n with
  | zero => intro a m; rfl
  | succ n ih =>
      intro a m
      show m.node (rootHash (m := m) (fill n a)) (rootHash (m := m) (fill n a)) =
        m.node (fillHash (m := m) n a) (fillHash (m := m) n a)
      rw [ih (m := m)]

/-- The leaf vector of `fill` is a replicated list. -/
theorem leaves_fill : ∀ (n : Nat) (a : α), (fill n a).leaves = List.replicate (2 ^ n) a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
      intro a
      show (fill n a).leaves ++ (fill n a).leaves = List.replicate (2 ^ (n + 1)) a
      rw [ih, List.replicate_append_replicate]
      have h : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_two]
      exact congrArg (fun k => List.replicate k a) h

/-- The two ways of spelling a sparse tree agree. -/
theorem fill_eq_ofLeaves : ∀ (n : Nat) (a : α) (h : (List.replicate (2 ^ n) a).length = 2 ^ n),
    ofLeaves n (List.replicate (2 ^ n) a) h = fill n a := by
  intro n a h
  have key : (ofLeaves n (List.replicate (2 ^ n) a) h).leaves = (fill n a).leaves := by
    rw [leaves_ofLeaves, leaves_fill]
  exact leaves_injective n (ofLeaves n (List.replicate (2 ^ n) a) h) (fill n a) key

/-- Kernel check: the sparse digest at depth three is three doublings of one leaf digest. -/
example : fillHash (α := Nat) (β := Dig Nat) 3 7 =
    Dig.node (Dig.node (Dig.node (Dig.leaf 7) (Dig.leaf 7)) (Dig.node (Dig.leaf 7) (Dig.leaf 7)))
      (Dig.node (Dig.node (Dig.leaf 7) (Dig.leaf 7)) (Dig.node (Dig.leaf 7) (Dig.leaf 7))) := rfl

/-- The sparse digest of a depth-four tree, discharged by the theorem rather than by hand. -/
example : rootHash (α := Nat) (β := Dig Nat) (fill 4 0) =
    fillHash (α := Nat) (β := Dig Nat) 4 0 := rootHash_fill 4 0

/-! ### Committing to a vector -/

/-- The Merkle commitment to a vector of exactly `2 ^ n` entries. -/
def commit {α β : Type} [m : MerkleHash α β] : (n : Nat) → (l : List α) → l.length = 2 ^ n → β :=
  fun n l h => rootHash (m := m) (ofLeaves n l h)

/-- **Binding.** Two vectors with the same commitment are the same vector.

This is what makes a published root worth quoting as evidence: nobody can point at a root and
later talk their way into a different vector. -/
theorem commit_inj {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (l₁ l₂ : List α) (h₁ : l₁.length = 2 ^ n) (h₂ : l₂.length = 2 ^ n),
      commit (m := m) n l₁ h₁ = commit (m := m) n l₂ h₂ → l₁ = l₂ := by
  intro n l₁ l₂ h₁ h₂ h
  rw [← leaves_ofLeaves n l₁ h₁, ← leaves_ofLeaves n l₂ h₂]
  exact congrArg Tree.leaves
    (rootHash_injective (m := m) (ofLeaves n l₁ h₁) (ofLeaves n l₂ h₂) h)

/-- Kernel check: committing to `[0, 1, 2, 3]` at depth two is exactly the expected `Dig` term. -/
example : commit (α := Nat) (β := Dig Nat) 2 [0, 1, 2, 3] rfl =
    Dig.node (Dig.node (Dig.leaf 0) (Dig.leaf 1)) (Dig.node (Dig.leaf 2) (Dig.leaf 3)) := rfl

/-- Kernel check: two different vectors of the same size get different commitments. -/
example : commit (α := Nat) (β := Dig Nat) 2 [0, 1, 2, 3] rfl ≠
    commit (α := Nat) (β := Dig Nat) 2 [0, 1, 2, 4] rfl := by decide

/-! ### Batch updates -/

/-- Apply a batch of writes, left to right, so a later write to the same path wins. -/
def updateAll : Tree α n → List (Path n × α) → Tree α n :=
  fun t l => l.foldl (fun acc pa => acc.update pa.1 pa.2) t

/-- The paths touched by a batch. -/
def touched : List (Path n × α) → List (Path n) := List.map Prod.fst

/-- An empty batch changes nothing. -/
theorem get_updateAll_nil : ∀ (n : Nat) (t : Tree α n) (p : Path n),
    (updateAll t []).get p = t.get p := fun _ _ _ => rfl

/-- **Untouched leaves are unchanged.** If `p` is not one of the paths the batch writes to, the
batched tree still reads `t.get p` there. -/
theorem get_updateAll_notMem : ∀ {n : Nat} (t : Tree α n) (l : List (Path n × α)) (p : Path n),
    p ∉ touched l → (updateAll t l).get p = t.get p := by
  intro n t l p h
  induction l generalizing t with
  | nil => rfl
  | cons x xs ih =>
      rw [touched, List.map_cons, List.mem_cons] at h
      show (updateAll (t.update x.1 x.2) xs).get p = t.get p
      rw [ih (t.update x.1 x.2) (fun hh => h (Or.inr hh)),
        Tree.get_update_other (a := x.2) (p := x.1) (q := p) t (fun hh => h (Or.inl hh.symm))]

/-- **The last write wins.** Appending `(p, a)` as the final entry of the batch puts `a` at `p`. -/
theorem get_updateAll_last : ∀ {n : Nat} (t : Tree α n) (l : List (Path n × α)) (p : Path n)
    (a : α), (updateAll t (l ++ [(p, a)])).get p = a := by
  intro n t l p a
  induction l generalizing t with
  | nil => exact Tree.get_update_same a n t p
  | cons x xs ih =>
      show (updateAll (t.update x.1 x.2) (xs ++ [(p, a)])).get p = a
      exact ih (t.update x.1 x.2)

/-- The same fact phrased with `List.getLast?`, for callers that only know the batch is nonempty. -/
theorem get_updateAll_getLast : ∀ {n : Nat} (t : Tree α n) (l : List (Path n × α)) (p : Path n)
    (a : α), l.getLast? = some (p, a) → (updateAll t l).get p = a := by
  intro n t l p a h
  induction l generalizing t with
  | nil => exact absurd h (by simp [List.getLast?])
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx : x = (p, a) := Option.some.inj h
          subst hx
          exact Tree.get_update_same a n t p
      | cons y ys =>
          rw [List.getLast?_cons_cons] at h
          show (updateAll (t.update x.1 x.2) (y :: ys)).get p = a
          exact ih (t.update x.1 x.2) h

/-- One step of the incremental batched root recomputation: carry the tree and its current root,
and update the root from the *pre-update* authentication path. -/
def updateStep {α β : Type} [m : MerkleHash α β] :
    (Tree α n × β) → Path n × α → Tree α n × β :=
  fun acc pa => (acc.1.update pa.1 pa.2, verify (ofTree (β := β) acc.1 pa.1) (m.leaf pa.2))

/-- **Batch update correctness.** The root of the batched tree equals folding `verify` over the
individual updates: `O(|l| * n)` hashes instead of `O(|l| * 2 ^ n)`, and this theorem says the
shortcut agrees with hashing the whole result. -/
theorem rootHash_updateAll {α β : Type} [m : MerkleHash α β] :
    ∀ {n : Nat} (t : Tree α n) (l : List (Path n × α)),
      rootHash (m := m) (updateAll t l) =
        (l.foldl (updateStep (m := m)) (t, rootHash (m := m) t)).2 := by
  intro n t l
  induction l generalizing t with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | mk p a =>
          show rootHash (updateAll (t.update p a) xs) =
            (List.foldl (updateStep (m := m))
              (t.update p a, verify (ofTree t p) (m.leaf a)) xs).2
          rw [ih, rootHash_update (α := α) (β := β) (m := m) n t p a]

/-! ### A transparency log / append-only ledger -/

/-- A log of `2 ^ n` entries is just a `Tree α n`: the position is the path. -/
abbrev Log (α : Type) (n : Nat) := Tree α n

/-- The published head of a log: the Merkle root of its entries. -/
def logRoot {α β : Type} [m : MerkleHash α β] : Log α n → β := rootHash (m := m)

/-- The entry of a log at position `p`. -/
def logEntry : Log α n → Path n → α := fun t p => t.get p

/-- **History binding.** Two logs with the same head agree at every position.

This is what makes a published root worth quoting: a server that shows you one entry cannot
quietly be showing you the entries of a different log. -/
theorem history_binding {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t₁ t₂ : Log α n), logRoot (m := m) t₁ = logRoot (m := m) t₂ →
      ∀ (p : Path n), logEntry t₁ p = logEntry t₂ p := by
  intro n t₁ t₂ h p
  exact rootHash_injective (m := m) t₁ t₂ h ▸ rfl

/-- **Appending changes the head.** Writing a value at `p` that is not already there moves the
root, so a log cannot be edited in place without its head noticing. -/
theorem extension_changes_root {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Log α n) (p : Path n) (a : α), logEntry t p ≠ a →
      logRoot (m := m) (t.update p a) ≠ logRoot (m := m) t := by
  intro n t p a hne heq
  exact hne (rootHash_injective (m := m) (t.update p a) t heq ▸ Tree.get_update_same a n t p)

/-- **Re-storing an old value leaves the head alone.** The complement of the previous theorem:
the only writes that do not move the root are the ones that change nothing. -/
theorem extension_preserves_root {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Log α n) (p : Path n),
      logRoot (m := m) (t.update p (logEntry t p)) = logRoot (m := m) t :=
  fun n t p => rootHash_update_get (α := α) (β := β) (m := m) n t p

/-- **No forged inclusion.** If the log does not hold `a` at `p`, then the honest authentication
path for `p` refuses to verify `a` against the published head. -/
theorem forged_inclusion_rejected {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Log α n) (p : Path n) (a : α), logEntry t p ≠ a →
      verify (ofTree (β := β) t p) (m.leaf a) ≠ logRoot (m := m) t := by
  intro n t p a hne
  exact no_forgery (α := α) (β := β) (m := m) n t p a hne (ofTree t p)
    (Proof.pathOf_ofTree n t p)

/-- Every position of a log is reachable by some path, so "the entries agree" can be checked
position by position. -/
theorem log_entries_cover : ∀ (n : Nat) (p : Path n), p ∈ Path.allPaths n :=
  fun n p => Path.allPaths_complete n p

/-! ### Multi-inclusion: a set certificate -/

/-- One item of a set certificate: a claimed position, a claimed value, and the authentication
path offered as evidence. -/
structure Claim (α β : Type) (n : Nat) where
  /-- The position being claimed. -/
  path : Path n
  /-- The value claimed to live there. -/
  value : α
  /-- The authentication path offered as evidence. -/
  proof : Proof β n

/-- A claim checks out against `root` when folding its proof up from its value reaches `root`. -/
def verifiesAt {α β : Type} [m : MerkleHash α β] (root : β) (c : Claim α β n) : Prop :=
  verify c.proof (m.leaf c.value) = root

/-- Every claim in the certificate checks out against `root`. -/
def allVerify {α β : Type} [m : MerkleHash α β] (root : β) (cs : List (Claim α β n)) : Prop :=
  ∀ c ∈ cs, verifiesAt (m := m) root c

/-- A proof is *for the position it claims to be for*. Without this a proof could be re-used at
a different leaf, which is exactly the substitution attack a set certificate must rule out. -/
def wellFormed {α β : Type} (c : Claim α β n) : Prop := Proof.pathOf c.proof = c.path

/-- **Multi-inclusion soundness.** A certificate whose every claim verifies against one root,
and whose every proof selects the position it claims, implies the tree agrees with every
claimed value. -/
theorem multi_inclusion {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (cs : List (Claim α β n)),
      allVerify (m := m) (rootHash t) cs →
        (∀ c ∈ cs, wellFormed c) → ∀ c ∈ cs, t.get c.path = c.value := by
  intro n t cs h hw c hc
  have hs : t.get (Proof.pathOf c.proof) = c.value := verify_sound n t c.proof c.value (h c hc)
  have hwc : Proof.pathOf c.proof = c.path := hw c hc
  rw [hwc] at hs
  exact hs

/-- The honest certificate for a set of positions of `t`. -/
def honestClaims {α β : Type} [m : MerkleHash α β] (t : Tree α n) (ps : List (Path n)) :
    List (Claim α β n) :=
  ps.map (fun p => { path := p, value := t.get p, proof := ofTree t p })

/-- An honest certificate always verifies. -/
theorem honestClaims_allVerify {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (ps : List (Path n)),
      allVerify (m := m) (rootHash t) (honestClaims (m := m) t ps) := by
  intro n t ps c hc
  show verifiesAt (m := m) (rootHash t) c
  have key : c ∈ List.map (fun p => Claim.mk p (t.get p) (ofTree t p)) ps := hc
  rw [List.mem_map] at key
  obtain ⟨p, _, rfl⟩ := key
  exact verify_complete n t p

/-- An honest certificate is well formed. -/
theorem honestClaims_wellFormed {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (ps : List (Path n)) (c : Claim α β n),
      c ∈ honestClaims (m := m) t ps → wellFormed c := by
  intro n t ps c hc
  have key : c ∈ List.map (fun p => Claim.mk p (t.get p) (ofTree t p)) ps := hc
  rw [List.mem_map] at key
  obtain ⟨p, _, rfl⟩ := key
  exact Proof.pathOf_ofTree n t p

/-- Hence an honest certificate really does pin the tree down at every claimed position. -/
theorem honestClaims_correct {α β : Type} [m : MerkleHash α β] :
    ∀ (n : Nat) (t : Tree α n) (ps : List (Path n)) (c : Claim α β n),
      c ∈ honestClaims (m := m) t ps → t.get c.path = c.value :=
  fun n t ps c hc =>
    multi_inclusion n t (honestClaims (m := m) t ps)
      (honestClaims_allVerify n t ps) (honestClaims_wellFormed n t ps) c hc

/-- The boolean test a client would actually run: every claim in `cs` folds up to `root`. -/
def allVerifyB {α β : Type} [DecidableEq β] [m : MerkleHash α β] (root : β)
    (cs : List (Claim α β n)) : Bool :=
  cs.all (fun c => decide (verify c.proof (m.leaf c.value) = root))

/-- The boolean test agrees with the `Prop` it implements, so a client that runs it learns
something true. -/
theorem allVerifyB_eq {α β : Type} [DecidableEq β] [m : MerkleHash α β] (root : β)
    (cs : List (Claim α β n)) :
    allVerifyB (m := m) root cs = true ↔ allVerify (m := m) root cs := by
  show (cs.all (fun c => decide (verify c.proof (m.leaf c.value) = root)) = true) ↔
    ∀ c ∈ cs, verify c.proof (m.leaf c.value) = root
  rw [List.all_eq_true]
  refine ⟨fun h c hc => of_decide_eq_true (h c hc), fun h c hc => decide_eq_true (h c hc)⟩

/-! ### Concrete scenarios -/

/-- A four-account balance ledger. -/
def balances : Tree Nat 2 := ofLeaves 2 [100, 250, 0, 75] (by simp)

/-- Account 1, the second leaf: left at the root, right below it. -/
def acct1 : Path 2 := Path.left (Path.right Path.nil)

/-- Account 2, the third leaf: right at the root, left below it. -/
def acct2 : Path 2 := Path.right (Path.left Path.nil)

/-- The ledger really holds the balances we wrote down. -/
example : balances.leaves = [100, 250, 0, 75] := rfl

/-- **A transfer updates the root exactly as `verify` predicts.** Account 1 goes from 250 to
300, and the incremental recomputation from the old authentication path equals the full rehash. -/
example : rootHash (α := Nat) (β := Dig Nat) (balances.update acct1 300) =
    verify (β := Dig Nat) (ofTree (β := Dig Nat) balances acct1) (Dig.leaf 300) := rfl

/-- The transferred ledger has the new balance at `acct1`... -/
example : (balances.update acct1 300).get acct1 = 300 := rfl

/-- ...and nobody else's balance moved. -/
example : (balances.update acct1 300).get acct2 = 0 := by
  rw [Tree.get_update_other (a := 300) (t := balances) (p := acct1) (q := acct2) (by decide)]
  rfl

/-- **A forged balance does not verify.** Claiming account 1 holds 999 is rejected by the
kernel, not merely by argument. -/
example : verify (β := Dig Nat) (ofTree (β := Dig Nat) balances acct1) (Dig.leaf 999) ≠
    rootHash (α := Nat) (β := Dig Nat) balances := by decide

/-- The honest whole-ledger certificate verifies, checked by the kernel. -/
example : allVerifyB (α := Nat) (β := Dig Nat) (rootHash balances)
    (honestClaims balances (Path.allPaths 2)) = true := by decide

/-- ... and the `Prop` behind it holds, by the proved theorem. -/
example : allVerify (α := Nat) (β := Dig Nat) (rootHash balances)
    (honestClaims balances (Path.allPaths 2)) := honestClaims_allVerify 2 balances _

/-- A certificate with one forged entry is rejected by the kernel. -/
example : allVerifyB (α := Nat) (β := Dig Nat) (rootHash balances)
    ((honestClaims balances [acct1]).map (fun c => { c with value := 999 })) = false := by decide

/-- A batch transfer over two accounts, with the batched root computed by the kernel. -/
example : rootHash (α := Nat) (β := Dig Nat) (updateAll balances [(acct1, 200), (acct2, 50)]) =
    Dig.node (Dig.node (Dig.leaf 100) (Dig.leaf 200)) (Dig.node (Dig.leaf 50) (Dig.leaf 75)) := rfl

/-- The batch left the untouched accounts alone. -/
example : (updateAll balances [(acct1, 200), (acct2, 50)]).get
    (Path.left (Path.left Path.nil)) = 100 := by
  rw [get_updateAll_notMem (t := balances) (l := [(acct1, 200), (acct2, 50)])
    (Path.left (Path.left Path.nil)) (by decide)]
  rfl

/-- A sixteen-entry append-only log. -/
def log16 : Tree Nat 4 :=
  ofLeaves 4 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] (by simp)

/-- Entry 11 of the log, addressed by position rather than by bits. -/
def pos11 : Path 4 := pathOfIndex 11 4 (by decide)

/-- Indexing by position agrees with the leaf vector. -/
example : log16.get pos11 = 11 := rfl

/-- **A real inclusion proof verifies**, computed by the kernel at depth four. -/
example : verify (β := Dig Nat) (ofTree (β := Dig Nat) log16 pos11) (Dig.leaf 11) =
    rootHash (α := Nat) (β := Dig Nat) log16 := by decide

/-- **A tampered one does not.** The same proof with the value changed to 12 is rejected. -/
example : verify (β := Dig Nat) (ofTree (β := Dig Nat) log16 pos11) (Dig.leaf 12) ≠
    rootHash (α := Nat) (β := Dig Nat) log16 := by decide

/-- Appending a replacement for entry 11 moves the head of the log. -/
example : rootHash (α := Nat) (β := Dig Nat) (log16.update pos11 111) ≠
    rootHash (α := Nat) (β := Dig Nat) log16 := by decide

/-- The whole sixteen-entry log certificate verifies, by the kernel. -/
example : allVerifyB (α := Nat) (β := Dig Nat) (rootHash log16)
    (honestClaims log16 (Path.allPaths 4)) = true := by decide

/-- A key-value store: keys are paths, values are leaves. -/
def kv : Tree String 2 := ofLeaves 2 ["alice", "bob", "carol", "dave"] (by simp)

/-- **Two writes at distinct keys are independent.** Overwriting `carol` leaves `bob` readable,
and the write at `acct1` is visible there - the formal reason a batch of writes cannot corrupt
its neighbours. -/
example : (kv.update acct1 "eve").get acct1 = "eve" ∧
    (kv.update acct1 "eve").get acct2 = "carol" := by
  refine ⟨Tree.get_update_same "eve" 2 kv acct1, ?_⟩
  rw [Tree.get_update_other (a := "eve") (t := kv) (p := acct1) (q := acct2) (by decide)]
  rfl

/-- The same store read back through the vector API. -/
example : kv.leaves = ["alice", "bob", "carol", "dave"] := rfl

/-- Committing the store and reading it back recovers the vector, by `commit_inj`. -/
theorem commit_recovery (l : List String) (h : l.length = 2 ^ 2) :
    commit (α := String) (β := Dig String) 2 l h =
      commit (α := String) (β := Dig String) 2 ["alice", "bob", "carol", "dave"] (by simp) →
    l = ["alice", "bob", "carol", "dave"] := by
  intro hh
  have hs : (["alice", "bob", "carol", "dave"] : List String).length = 2 ^ 2 := by simp
  exact commit_inj 2 l ["alice", "bob", "carol", "dave"] h hs hh

/-! ### The same theorems at three different leaf types -/

/-- Balances: `α = Nat`. -/
theorem commit_binding_nat (l₁ l₂ : List Nat) (h₁ : l₁.length = 2 ^ 2) (h₂ : l₂.length = 2 ^ 2)
    (h : commit (α := Nat) (β := Dig Nat) 2 l₁ h₁ = commit (α := Nat) (β := Dig Nat) 2 l₂ h₂) :
    l₁ = l₂ := commit_inj 2 l₁ l₂ h₁ h₂ h

/-- Names: `α = String`. -/
theorem commit_binding_string (l₁ l₂ : List String) (h₁ : l₁.length = 2 ^ 2)
    (h₂ : l₂.length = 2 ^ 2)
    (h : commit (α := String) (β := Dig String) 2 l₁ h₁ =
      commit (α := String) (β := Dig String) 2 l₂ h₂) : l₁ = l₂ :=
  commit_inj 2 l₁ l₂ h₁ h₂ h

/-- Bytes: `α = Fin 256`. -/
theorem commit_binding_byte (l₁ l₂ : List (Fin 256)) (h₁ : l₁.length = 2 ^ 2)
    (h₂ : l₂.length = 2 ^ 2)
    (h : commit (α := Fin 256) (β := Dig (Fin 256)) 2 l₁ h₁ =
      commit (α := Fin 256) (β := Dig (Fin 256)) 2 l₂ h₂) : l₁ = l₂ :=
  commit_inj 2 l₁ l₂ h₁ h₂ h

/-- Sparse digests at each instantiation: `Nat`, `String`, and a byte. -/
example : rootHash (α := Nat) (β := Dig Nat) (fill 3 7) =
    Dig.node (Dig.node (Dig.node (Dig.leaf 7) (Dig.leaf 7)) (Dig.node (Dig.leaf 7) (Dig.leaf 7)))
      (Dig.node (Dig.node (Dig.leaf 7) (Dig.leaf 7)) (Dig.node (Dig.leaf 7) (Dig.leaf 7))) := rfl

example : rootHash (α := String) (β := Dig String) (fill 1 "x") =
    Dig.node (Dig.leaf "x") (Dig.leaf "x") := rfl

example : rootHash (α := Fin 256) (β := Dig (Fin 256)) (fill 1 255) =
    Dig.node (Dig.leaf 255) (Dig.leaf 255) := rfl

/-- Byte trees read back through the vector API, at depth two. -/
example : (ofLeaves 2 ([0, 1, 254, 255] : List (Fin 256)) (by simp)).get
    (Path.right (Path.left Path.nil)) = 254 := rfl

/-- No forgery, instantiated at bytes: writing a fresh byte moves the root. -/
example : rootHash (α := Fin 256) (β := Dig (Fin 256))
    ((fill 2 (255 : Fin 256)).update (Path.left (Path.left Path.nil)) (0 : Fin 256)) ≠
    rootHash (α := Fin 256) (β := Dig (Fin 256)) (fill 2 (255 : Fin 256)) := by
  refine extension_changes_root (α := Fin 256) (β := Dig (Fin 256)) 2 (fill 2 255)
    (Path.left (Path.left Path.nil)) 0 ?_
  show (fill 2 (255 : Fin 256)).get (Path.left (Path.left Path.nil)) ≠ 0
  rw [get_fill]
  decide

end Merkle.Usage
