/-
Circuit contexts and contextual replacement.

A context is a circuit with one hole; filling the hole with a circuit yields a circuit.
Contexts are built only from sequential composition, which is exactly the class of contexts
for which congruence modulo global phase is valid (see Quantum/ControlPhase.lean for why
controlled-subcircuit formation is deliberately absent).
-/
import Quantum.Equivalence

namespace Quantum

/-- A one-hole context over n-qubit circuits, built from sequential composition. -/
inductive Ctx (n : Nat) : Type where
  | hole : Ctx n
  | seqL : Circuit n -> Ctx n -> Ctx n
  | seqR : Ctx n -> Circuit n -> Ctx n
deriving DecidableEq

namespace Ctx

/-- Fill the hole. -/
def fill : Ctx n -> Circuit n -> Circuit n
  | hole, c => c
  | seqL d k, c => Circuit.seq d (fill k c)
  | seqR k d, c => Circuit.seq (fill k c) d

/-- The context 'seq p1 (seq p2 (... (seq hole ...)))' for a right-nested prefix. -/
def ofSuffix : List (Circuit n) -> Ctx n
  | [] => Ctx.hole
  | d :: ds => Ctx.seqL d (ofSuffix ds)

theorem fill_ofSuffix (pre : List (Circuit n)) (c : Circuit n) :
    fill (ofSuffix pre) c = List.foldr Circuit.seq c pre := by
  induction pre with
  | nil => rfl
  | cons d t ih => simp [ofSuffix, fill, List.foldr, ih]

/-- Composition of contexts: 'comp k₁ k₂' fills k₁'s hole with k₂. -/
def comp : Ctx n -> Ctx n -> Ctx n
  | hole, k₂ => k₂
  | seqL d k₁, k₂ => seqL d (comp k₁ k₂)
  | seqR k₁ d, k₂ => seqR (comp k₁ k₂) d

theorem fill_comp (k₁ k₂ : Ctx n) (c : Circuit n) :
    fill (comp k₁ k₂) c = fill k₁ (fill k₂ c) := by
  induction k₁ with
  | hole => rfl
  | seqL d k ih =>
    show fill (Ctx.seqL d (comp k k₂)) c = fill (Ctx.seqL d k) (fill k₂ c)
    simp [fill, ih]
  | seqR k d ih =>
    show fill (Ctx.seqR (comp k k₂) d) c = fill (Ctx.seqR k d) (fill k₂ c)
    simp [fill, ih]

/-- Contextual replacement preserves equivalence modulo global phase. -/
theorem congr (k : Ctx n) {a b : Circuit n} (h : PhaseEquivalent a b) :
    PhaseEquivalent (fill k a) (fill k b) := by
  induction k with
  | hole => exact h
  | seqL d k ih => exact PhaseEquivalent.pre ih
  | seqR k d ih => exact PhaseEquivalent.post ih

/-- Contextual replacement preserves exact semantic equality. -/
theorem congrEq (k : Ctx n) {a b : Circuit n} (h : EqExact a b) :
    EqExact (fill k a) (fill k b) := by
  induction k with
  | hole => exact h
  | seqL d k ih => exact EqExact.pre ih
  | seqR k d ih => exact EqExact.post ih

end Ctx

end Quantum
