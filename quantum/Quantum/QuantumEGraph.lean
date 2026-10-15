/-
OptiSat adapter: quantum circuits as an OptiSat (LambdaSat) equality-saturation domain.

OptiSat is a domain-agnostic, formally verified equality-saturation engine (vendored
unmodified in LambdaSat/, pinned toolchain Lean 4.26.0).  It is parameterized by three
typeclasses:

* NodeOps Op           -- the e-node structure (children, mapChildren, replaceChildren)
* NodeSemantics Op Val -- the semantic interpretation of e-nodes in a domain Val
* Extractable Op Expr  -- reconstruction of a concrete expression from e-nodes

This file instantiates them for quantum circuits:

* Op = QOp n: identity, a primitive gate, or the composition of two e-classes
* Val = PhaseOp n: the n-qubit operator space MODULO GLOBAL PHASE (a setoid quotient).
  Equality in this domain is exactly "differs by a scalar of unit modulus", the equivalence
  relation the whole project must preserve.
* Expr = Circuit n

Nothing here refers to saturation or extraction: the quotient semantics is defined directly
from the matrix semantics of Quantum/Semantics.lean.
-/
import Quantum.Certificates
import Quantum.Cost
import LambdaSat

namespace Quantum
namespace EG

open LambdaSat UnionFind

/-! ### E-nodes -/

/-- The e-nodes of the quantum circuit language: identity, a primitive gate, or the
sequential composition of two e-classes. -/
inductive QOp (n : Nat) : Type where
  | one : QOp n
  | gate : Gate n -> QOp n
  | seq : EClassId -> EClassId -> QOp n
deriving Repr, Inhabited, DecidableEq

instance {n : Nat} : BEq (QOp n) := ⟨fun a b => a = b⟩

instance {n : Nat} : LawfulBEq (QOp n) where
  eq_of_beq {a b} h := by simpa [BEq.beq] using h
  rfl {a} := by simp [BEq.beq]

instance {n : Nat} : Hashable (QOp n) where
  hash
    | .one => 7
    | .gate g => mixHash 11 (g.qubits.foldl (fun acc i => mixHash acc (hash (i : Nat))) 7)
    | .seq a b => mixHash 13 (mixHash (hash a) (hash b))

instance {n : Nat} : LawfulHashable (QOp n) where
  hash_eq a b h := by
    have hab : a = b := eq_of_beq h
    subst hab
    rfl

/-- Raw structural operations on e-nodes, defined before the instance so that the
instance laws can reuse them. -/
def childrenQ : QOp n -> List EClassId
  | .one => []
  | .gate _ => []
  | .seq a b => [a, b]

def mapChildrenQ : (EClassId -> EClassId) -> QOp n -> QOp n
  | f, .one => .one
  | f, .gate g => .gate g
  | f, .seq a b => .seq (f a) (f b)

def replaceChildrenQ : QOp n -> List EClassId -> QOp n
  | .seq _ _, [a, b] => .seq a b
  | op, _ => op

/-- The two NodeOps laws relating replaceChildren to children and to the skeleton. -/
theorem replaceChildren_laws (op : QOp n) (ids : List EClassId)
    (hlen : ids.length = (childrenQ op).length) :
    childrenQ (replaceChildrenQ op ids) = ids /\
      mapChildrenQ (fun _ => (0 : EClassId)) (replaceChildrenQ op ids) =
        mapChildrenQ (fun _ => (0 : EClassId)) op := by
  cases op with
  | one =>
    rw [childrenQ] at hlen
    cases ids with
    | nil => simp [childrenQ, replaceChildrenQ, mapChildrenQ]
    | cons x rest => simp at hlen
  | gate g =>
    rw [childrenQ] at hlen
    cases ids with
    | nil => simp [childrenQ, replaceChildrenQ, mapChildrenQ]
    | cons x rest => simp at hlen
  | seq a b =>
    rw [childrenQ] at hlen
    cases ids with
    | nil => simp at hlen
    | cons x rest =>
      cases rest with
      | nil => simp at hlen
      | cons y rest2 =>
        cases rest2 with
        | nil => simp [childrenQ, replaceChildrenQ, mapChildrenQ]
        | cons z rest3 => simp at hlen

/-- The two NodeOps laws relating mapChildren to children. -/
theorem mapChildren_laws (f : EClassId -> EClassId) (op : QOp n) :
    childrenQ (mapChildrenQ f op) = (childrenQ op).map f /\
      mapChildrenQ id op = op := by
  cases op <;> simp [childrenQ, mapChildrenQ]

instance {n : Nat} : NodeOps (QOp n) where
  children := childrenQ
  mapChildren := mapChildrenQ
  replaceChildren := replaceChildrenQ
  localCost op :=
    match op with
    | .one => 0
    | .gate _ => 1
    | .seq _ _ => 0
  mapChildren_children := by
    intro f op
    exact (mapChildren_laws f op).1
  mapChildren_id := by
    intro op
    exact (mapChildren_laws id op).2
  replaceChildren_children := by
    intro op ids hlen
    exact (replaceChildren_laws op ids hlen).1
  replaceChildren_sameShape := by
    intro op ids hlen
    exact (replaceChildren_laws op ids hlen).2

/-! ### The semantic domain: operators modulo global phase -/

/-- Two operators are equivalent when they differ by a scalar of unit modulus. -/
def OpPhase (n : Nat) (M N : Operator n) : Prop :=
  ∃ z : ℂ, IsUnitPhase z ∧ M = z • N

theorem opPhase_refl {n : Nat} (M : Operator n) : OpPhase n M M :=
  ⟨1, isUnitPhase_one, by rw [one_smul]⟩

theorem opPhase_symm {n : Nat} {M N : Operator n} (h : OpPhase n M N) : OpPhase n N M := by
  classical
  obtain ⟨z, hz, he⟩ := h
  refine ⟨z⁻¹, isUnitPhase_inv hz, ?_⟩
  rw [he, smul_smul]
  have hz0 : z ≠ 0 := by
    intro hh
    rw [hh] at hz
    norm_num [IsUnitPhase, Complex.normSq] at hz
  rw [inv_mul_cancel₀ hz0, one_smul]

theorem opPhase_trans {n : Nat} {M N P : Operator n} (h1 : OpPhase n M N)
    (h2 : OpPhase n N P) : OpPhase n M P := by
  obtain ⟨z, hz, he1⟩ := h1
  obtain ⟨w, hw, he2⟩ := h2
  refine ⟨z * w, isUnitPhase_mul hz hw, ?_⟩
  rw [he1, he2, smul_smul]

/-- The setoid of n-qubit operators modulo global phase. -/
def phaseSetoidOp (n : Nat) : Setoid (Operator n) where
  r := OpPhase n
  iseqv := ⟨@opPhase_refl n, @opPhase_symm n, @opPhase_trans n⟩

/-- The n-qubit operator space modulo global phase. -/
def PhaseOp (n : Nat) : Type := Quotient (phaseSetoidOp n)

/-- The equivalence class of an operator. -/
def pquot {n : Nat} (M : Operator n) : PhaseOp n := Quotient.mk (phaseSetoidOp n) M

theorem pquot_eq {n : Nat} {M N : Operator n} : pquot M = pquot N ↔ OpPhase n M N := by
  classical
  show Quotient.mk (phaseSetoidOp n) M = Quotient.mk (phaseSetoidOp n) N ↔ OpPhase n M N
  exact Quotient.eq

theorem pquot_eq_of_phase {n : Nat} {M N : Operator n} (h : OpPhase n M N) : pquot M = pquot N :=
  Quotient.eq.mpr h

instance {n : Nat} : Inhabited (PhaseOp n) := ⟨pquot 1⟩

/-- Multiplication on the phase quotient.  It is well defined because scaling each factor by
a unit phase scales the product by the product of those phases. -/
noncomputable instance {n : Nat} : Mul (PhaseOp n) where
  mul := Quotient.lift₂ (fun M N => pquot (M * N)) (by
    intro M N M' N' hM hN
    show pquot (M * N) = pquot (M' * N')
    obtain ⟨z, hz, heM⟩ := hM
    obtain ⟨w, hw, heN⟩ := hN
    rw [heM, heN]
    apply pquot_eq_of_phase
    refine ⟨z * w, isUnitPhase_mul hz hw, ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_smul])

theorem pquot_mul {n : Nat} (M N : Operator n) : pquot (M * N) = pquot M * pquot N := rfl

theorem pquot_phase {n : Nat} {a b : Circuit n} (h : PhaseEquivalent a b) :
    pquot (denote a) = pquot (denote b) :=
  pquot_eq_of_phase h

/-! ### The algebraic laws of the phase quotient -/

theorem pquot_mul_one {n : Nat} (M : Operator n) :
    pquot M * pquot (1 : Operator n) = pquot M := by
  show pquot (M * 1) = pquot M
  rw [Matrix.mul_one]

theorem pquot_one_mul {n : Nat} (M : Operator n) :
    pquot (1 : Operator n) * pquot M = pquot M := by
  show pquot (1 * M) = pquot M
  rw [Matrix.one_mul]

theorem pquot_mul_assoc {n : Nat} (M N P : Operator n) :
    (pquot M * pquot N) * pquot P = pquot M * (pquot N * pquot P) := by
  show pquot ((M * N) * P) = pquot (M * (N * P))
  rw [Matrix.mul_assoc]

/-- Multiplication of phase classes is associative: every phase class is the image of an
operator, so this reduces to associativity of matrix multiplication. -/
theorem pquot_op_mul_assoc {n : Nat} (x y z : PhaseOp n) :
    (x * y) * z = x * (y * z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro M N P
  show pquot ((M * N) * P) = pquot (M * (N * P))
  rw [Matrix.mul_assoc]

theorem pquot_op_mul_one {n : Nat} (x : PhaseOp n) : x * pquot (1 : Operator n) = x := by
  refine Quotient.inductionOn x ?_
  intro M
  show pquot (M * 1) = pquot M
  rw [Matrix.mul_one]

theorem pquot_op_one_mul {n : Nat} (x : PhaseOp n) : pquot (1 : Operator n) * x = x := by
  refine Quotient.inductionOn x ?_
  intro M
  show pquot (1 * M) = pquot M
  rw [Matrix.one_mul]

/-! ### NodeSemantics -/

/-- The semantic interpretation of a quantum e-node in the phase quotient. -/
noncomputable def evalOpQ {n : Nat} : QOp n -> (Nat -> PhaseOp n) -> (EClassId -> PhaseOp n) ->
    PhaseOp n
  | .one, _, _ => pquot (1 : Operator n)
  | .gate g, _, _ => pquot (denoteGate g)
  | .seq a b, _, v => v b * v a

noncomputable instance {n : Nat} : NodeSemantics (QOp n) (PhaseOp n) where
  evalOp := evalOpQ
  evalOp_ext := by
    intro op env v v' h
    cases op with
    | one => rfl
    | gate _ => rfl
    | seq a b =>
      have ha : a ∈ NodeOps.children (QOp.seq (n := n) a b) := List.Mem.head _
      have hb : b ∈ NodeOps.children (QOp.seq (n := n) a b) :=
        List.Mem.tail _ (List.Mem.head _)
      show v b * v a = v' b * v' a
      rw [h a ha, h b hb]
  evalOp_mapChildren := by
    intro f op env v
    cases op <;> rfl
  evalOp_skeleton := by
    intro op₁ op₂ env v₁ v₂ hskel hc
    have h1 : mapChildrenQ (fun _ => (0 : EClassId)) op₁ =
        mapChildrenQ (fun _ => (0 : EClassId)) op₂ := hskel
    cases op₁ with
    | one =>
      cases op₂ with
      | one => rfl
      | gate g => exact absurd h1 (by simp [mapChildrenQ])
      | seq a b => exact absurd h1 (by simp [mapChildrenQ])
    | gate g =>
      cases op₂ with
      | one => exact absurd h1 (by simp [mapChildrenQ])
      | gate g' =>
        have hg : g = g' := by simpa [mapChildrenQ] using h1
        subst hg
        rfl
      | seq a b => exact absurd h1 (by simp [mapChildrenQ])
    | seq a b =>
      cases op₂ with
      | one => exact absurd h1 (by simp [mapChildrenQ])
      | gate g => exact absurd h1 (by simp [mapChildrenQ])
      | seq c d =>
        simp only [evalOpQ]
        have hk1 : (0 : Nat) < (NodeOps.children (QOp.seq (n := n) a b)).length := by
          show (0 : Nat) < ([a, b] : List EClassId).length
          simp
        have hk2 : (0 : Nat) < (NodeOps.children (QOp.seq (n := n) c d)).length := by
          show (0 : Nat) < ([c, d] : List EClassId).length
          simp
        have hk3 : (1 : Nat) < (NodeOps.children (QOp.seq (n := n) a b)).length := by
          show (1 : Nat) < ([a, b] : List EClassId).length
          simp
        have hk4 : (1 : Nat) < (NodeOps.children (QOp.seq (n := n) c d)).length := by
          show (1 : Nat) < ([c, d] : List EClassId).length
          simp
        have h2 : v₁ a = v₂ c := by
          have := hc 0 hk1 hk2
          simpa using this
        have h3 : v₁ b = v₂ d := by
          have := hc 1 hk3 hk4
          simpa using this
        rw [← h2, ← h3]

/-! The three computation rules of the quantum node semantics, as definitional simp lemmas.
They hold by `rfl` because the `NodeSemantics` instance above uses `evalOpQ` directly. -/

@[simp] theorem evalOpQ_one {n : Nat} (env : Nat -> PhaseOp n) (v : EClassId -> PhaseOp n) :
    @NodeSemantics.evalOp (QOp n) (PhaseOp n) _ _ QOp.one env v = pquot (1 : Operator n) := rfl

@[simp] theorem evalOpQ_gate {n : Nat} (g : Gate n) (env : Nat -> PhaseOp n)
    (v : EClassId -> PhaseOp n) :
    @NodeSemantics.evalOp (QOp n) (PhaseOp n) _ _ (QOp.gate g) env v = pquot (denoteGate g) := rfl

@[simp] theorem evalOpQ_seq {n : Nat} (a b : EClassId) (env : Nat -> PhaseOp n)
    (v : EClassId -> PhaseOp n) :
    @NodeSemantics.evalOp (QOp n) (PhaseOp n) _ _ (QOp.seq a b) env v = v b * v a := rfl

/-! ### Extraction -/

instance {n : Nat} : Extractable (QOp n) (Circuit n) where
  reconstruct op childExprs :=
    match op, childExprs with
    | .one, [] => some Circuit.one
    | .gate g, [] => some (Circuit.gate g)
    | .seq _ _, [a, b] => some (Circuit.seq a b)
    | _, _ => none

noncomputable instance {n : Nat} : EvalExpr (Circuit n) (PhaseOp n) where
  evalExpr c _ := pquot (denote c)

theorem extractableSound_qop (n : Nat) :
    LambdaSat.ExtractableSound (QOp n) (Circuit n) (PhaseOp n) := by
  classical
  intro op childExprs expr env v hrec hlen hchild
  cases op with
  | one =>
    cases childExprs with
    | nil =>
      have hrec' : (some Circuit.one : Option (Circuit n)) = some expr := hrec
      have hexpr : expr = Circuit.one := (Option.some.inj hrec').symm
      subst hexpr
      show pquot (denote Circuit.one) = pquot (1 : Operator n)
      simp only [denote_one]
    | cons x rest =>
      exfalso
      simp [NodeOps.children, childrenQ] at hlen
  | gate g =>
    cases childExprs with
    | nil =>
      have hrec' : (some (Circuit.gate g) : Option (Circuit n)) = some expr := hrec
      have hexpr : expr = Circuit.gate g := (Option.some.inj hrec').symm
      subst hexpr
      show pquot (denote (Circuit.gate g)) = pquot (denoteGate g)
      simp only [denote_gate]
    | cons x rest =>
      exfalso
      simp [NodeOps.children, childrenQ] at hlen
  | seq a b =>
    cases childExprs with
    | nil =>
      exfalso
      simp [NodeOps.children, childrenQ] at hlen
    | cons x rest =>
      cases rest with
      | nil =>
        exfalso
        simp [NodeOps.children, childrenQ] at hlen
      | cons y rest2 =>
        cases rest2 with
        | nil =>
          have hrec' : (some (Circuit.seq x y) : Option (Circuit n)) = some expr := hrec
          have hexpr : expr = Circuit.seq x y := (Option.some.inj hrec').symm
          subst hexpr
          have hk0 : (0 : Nat) < (NodeOps.children (QOp.seq (n := n) a b)).length := by
            show (0 : Nat) < ([a, b] : List EClassId).length
            simp
          have hk1 : (1 : Nat) < (NodeOps.children (QOp.seq (n := n) a b)).length := by
            show (1 : Nat) < ([a, b] : List EClassId).length
            simp
          have hx : pquot (denote x) = v a := by
            simpa using hchild 0 (by simp) hk0
          have hy : pquot (denote y) = v b := by
            simpa using hchild 1 (by simp) hk1
          show pquot (denote (Circuit.seq x y)) = v b * v a
          rw [denote_seq, pquot_mul, hy, hx]
        | cons z rest3 =>
          exfalso
          simp [NodeOps.children, childrenQ] at hlen

/-! ### Inserting circuits into an e-graph -/

/-- Insert a circuit into an e-graph, returning the e-class of the whole circuit. -/
def addCircuit {n : Nat} : Circuit n -> EGraph (QOp n) -> EClassId × EGraph (QOp n)
  | Circuit.one, g => g.add ⟨QOp.one⟩
  | Circuit.gate k, g => g.add ⟨QOp.gate k⟩
  | Circuit.seq a b, g =>
    let (ia, g₁) := addCircuit a g
    let (ib, g₂) := addCircuit b g₁
    g₂.add ⟨QOp.seq ia ib⟩

/-- The e-graph built from a circuit. -/
def ofCircuit {n : Nat} (c : Circuit n) : EClassId × EGraph (QOp n) :=
  addCircuit c (EGraph.empty : EGraph (QOp n))

end EG
end Quantum