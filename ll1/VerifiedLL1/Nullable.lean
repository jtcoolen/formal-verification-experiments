/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Fixpoint
import VerifiedLL1.Derivation

/-!
# Phase 4.1 — NULLABLE

## Specification

`G.Nullable A` is defined as `Derives G [var A] []`: `A` derives the empty word.  This
is a Phase 1 notion; nothing here mentions any algorithm.

## Computation

The classical rules are

    A -> (epsilon)        A -> X1 ... Xk   each Xi nullable
    -------------- null   --------------------------------- null
      Nullable A                        Nullable A

and NULLABLE is their least fixed point.  The executable transformer `nullableP G`
encodes both rules in one step: `A` is added when *some* production of `A` has a
right-hand side whose every symbol is already known nullable (a terminal never is,
and an empty right-hand side passes the test vacuously — which is exactly how the
epsilon rule is represented).  The iteration runs `|N|` times over the finite
enumeration of `N`, and `Fixpoint.iterP_stable` supplies termination.

## Results

* `nullable_sound`    - every fact the iteration produces is a real derivation of ε
  (**soundness**);
* `nullable_complete` - every real derivation of ε is found (**completeness**);
* `nullable_iff`      - the two coincide, so the computation decides the specification;
* `nullableSet`       - the same answer as an explicit finite list;
* `nullable_eps_tree` - the ε-behaviour in parse-tree terms: `A` is computed nullable
  exactly when there is a valid parse tree rooted at `A` with empty yield.
-/

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

/-- **Specification.** `G.Nullable A`: the nonterminal `A` derives the empty word. -/
def Grammar.Nullable (G : Grammar T N) (A : N) : Prop := Derives G [Sym.var A] []

/-- A symbol is nullable if it is a nullable nonterminal; a terminal never is. -/
def symNull [BEq N] (S : N → Bool) : Sym T N → Bool
  | Sym.var B => S B
  | Sym.tok _ => false

/-- One step of the NULLABLE computation: `A` is added when some production of `A`
has a right-hand side all of whose symbols are already known nullable. -/
def nullableTest [BEq N] (G : Grammar T N) (S : N → Bool) (A : N) : Bool :=
  G.productions.any fun p => p.1 == A && p.2.all (fun s => symNull S s)

/-- The monotone transformer whose least fixed point is NULLABLE. -/
def nullableP [BEq N] (G : Grammar T N) : (N → Bool) → N → Bool := nullableTest G

theorem nullableP_mono [BEq N] (G : Grammar T N) : Fixpoint.PMono (nullableP G) := by
  intro f g hfg A h
  unfold nullableP nullableTest at *
  obtain ⟨p, hp, hand⟩ := List.any_eq_true.mp h
  obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
  refine List.any_eq_true.mpr ⟨p, hp, Fixpoint.and_eq_true_iff.mpr ⟨h1, ?_⟩⟩
  rw [List.all_eq_true] at h2 ⊢
  intro s hs
  cases s with
  | tok t => exact absurd (h2 (Sym.tok t) hs) (by simp [symNull])
  | var B => exact hfg B (h2 (Sym.var B) hs)

/-- The iteration runs once per element of the enumeration of `N`. -/
def Grammar.nullableRounds (_G : Grammar T N) [FiniteEnum N] : Nat :=
  (FiniteEnum.elems (α := N)).length

theorem elems_complete [FiniteEnum N] : ∀ (x : N), x ∈ FiniteEnum.elems :=
  FiniteEnum.complete

/-- The computed NULLABLE set, as an explicit finite list. -/
def Grammar.nullableSet [DecidableEq N] (G : Grammar T N) [FiniteEnum N] : List N :=
  (FiniteEnum.elems (α := N)).filter (Fixpoint.iterP (nullableP G) (G.nullableRounds))

/-- The computed NULLABLE membership test. -/
def Grammar.nullable [BEq N] (G : Grammar T N) [FiniteEnum N] (A : N) : Bool :=
  Fixpoint.iterP (nullableP G) (G.nullableRounds) A

theorem derives_nil_of_symbols : ∀ (rhs : List (Sym T N)),
    (∀ s ∈ rhs, Derives G [s] []) → Derives G rhs [] := by
  intro rhs hall
  induction rhs with
  | nil => exact derives_refl []
  | cons s rest ih =>
      refine derives_append (hall s (List.Mem.head _))
        (ih (fun x hx => hall x (List.Mem.tail _ hx)))

/-- **Soundness of the computation.**  Whatever the iteration produces at any stage is
a genuine derivation of the empty word. -/
theorem nullable_sound [BEq N] [LawfulBEq N] (G : Grammar T N) :
    ∀ (k : Nat) (A : N), Fixpoint.iterP (nullableP G) k A = true → G.Nullable A := by
  intro k
  induction k with
  | zero => intro A h; exact absurd h (by simp [Fixpoint.iterP])
  | succ k ih =>
      intro A h
      unfold nullableP nullableTest at h
      rw [Fixpoint.iterP_succ] at h
      obtain ⟨p, hp, hand⟩ := List.any_eq_true.mp h
      obtain ⟨h1, h2⟩ := Fixpoint.and_eq_true_iff.mp hand
      have hA : p.1 = A := eq_of_beq h1
      have hprod : (A, p.2) ∈ G.productions := hA ▸ hp
      have hnull : Derives G p.2 [] :=
        derives_nil_of_symbols p.2 (fun s hs => by
          have hs' := (List.all_eq_true.mp h2) s hs
          cases s with
          | tok t => exact absurd hs' (by simp [symNull])
          | var B => exact ih B hs')
      exact derives_trans (derives_production A p.2 hprod) hnull

/-- **Completeness of the computation.**  Nullability is preserved *backwards* along a
derivation when the limit set is used: if the end of a derivation has only nullable
symbols, so does its beginning. -/
theorem nullable_backward [BEq N] [LawfulBEq N] (G : Grammar T N) [FiniteEnum N] :
    ∀ (xs ys : List (Sym T N)), Derives G xs ys →
      (∀ s ∈ ys, symNull (G.nullable) s = true) → ∀ s ∈ xs, symNull (G.nullable) s = true := by
  intro xs ys h
  induction h with
  | refl => intro hall s hs; exact hall s hs
  | @tail mid fin hrec hstep ih =>
      intro hall
      have hmid : ∀ s ∈ mid, symNull (G.nullable) s = true := by
        obtain ⟨B, rhs, pre, post, hp, h1, h2⟩ := derives1_decompose hstep
        subst h1; subst h2
        intro s hs
        rw [List.mem_append] at hs
        rcases hs with hpre | hright
        · refine hall _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hpre))))
        · rcases (List.mem_cons.mp hright) with hB | hpost
          · -- `s` is the rewritten variable `B`: closure of the limit makes `B` nullable
            subst hB
            have hclosed : G.nullable B ↔
                nullableP G (Fixpoint.iterP (nullableP G) (G.nullableRounds)) B = true := by
              simpa [Grammar.nullable, Grammar.nullableRounds] using
                Fixpoint.iterP_closed (FiniteEnum.elems (α := N)) (nullableP G)
                  (nullableP_mono G) elems_complete B
            refine hclosed.mpr ?_
            unfold nullableP nullableTest
            refine List.any_eq_true.mpr ⟨(B, rhs), hp,
              Fixpoint.and_eq_true_iff.mpr ⟨by simp, ?_⟩⟩
            rw [List.all_eq_true]
            intro x hx
            refine hall x (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
          · refine hall _ (List.mem_append.mpr (Or.inr hpost))
      exact ih hmid
/-- **Completeness.**  Every genuinely nullable nonterminal is computed. -/
theorem nullable_complete [BEq N] [LawfulBEq N] (G : Grammar T N) [FiniteEnum N]
    (A : N) (h : G.Nullable A) : G.nullable A = true := by
  have key := nullable_backward G [Sym.var A] [] h (by simp) (Sym.var A) (List.Mem.head _)
  simpa [symNull] using key

/-- **The characterisation.**  The computation decides the specification. -/
theorem nullable_iff [BEq N] [LawfulBEq N] (G : Grammar T N) [FiniteEnum N] (A : N) :
    G.nullable A = true ↔ G.Nullable A :=
  ⟨fun h => nullable_sound G (G.nullableRounds) A h, fun h => nullable_complete G A h⟩

/-- Membership in the computed list is the same statement. -/
theorem nullableSet_iff [DecidableEq N] [LawfulBEq N] (G : Grammar T N) [FiniteEnum N]
    (A : N) : A ∈ G.nullableSet ↔ G.Nullable A := by
  unfold Grammar.nullableSet
  rw [List.mem_filter]
  constructor
  · intro ⟨_, h⟩; exact (nullable_iff G A).mp h
  · intro h; exact ⟨FiniteEnum.complete A, (nullable_iff G A).mpr h⟩

/-- **Correct ε-behaviour.**  The computed set is exactly the set of nonterminals that
root a valid parse tree with empty yield. -/
theorem nullable_eps_tree [BEq N] [LawfulBEq N] (G : Grammar T N) [FiniteEnum N]
    (A : N) : G.nullable A = true ↔
      ∃ ts, Valid G (Tree.node A ts) ∧ Tree.yield (Tree.node A ts) = [] := by
  rw [nullable_iff]
  exact Iff.symm tree_iff_derives

end VerifiedLL1
