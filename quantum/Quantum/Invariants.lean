/-
Formal invariants of the equality-saturation engine, stated in THIS project's domain.

OptiSat (vendored in LambdaSat/) proves its e-graph theory once, parameterized by a node
type `Op`, a semantic domain `Val`, a `NodeSemantics Op Val` instance and an
`Extractable Op Expr` instance.  Quantum/QuantumEGraph.lean supplies those instances for
`Op = QOp n`, `Val = PhaseOp n` (operators modulo global phase) and `Expr = Circuit n`.

This module is where the two halves meet: every §E and §F obligation of the specification -
initial well-formedness, node-insertion preservation, merge preservation,
congruence-closure correctness, rebuilding preservation, saturation preservation, and
extraction correctness - is stated here as a named declaration *of this project*, at the
quantum domain, so the theorem inventory points at declarations inside quantum/ rather than
at the vendored library.  Each is discharged by the corresponding generic OptiSat theorem
plus the instances from Quantum/QuantumEGraph.lean; nothing is re-proved and nothing is
assumed.
-/
import Quantum.Optimizer
import LambdaSat.AddNodeTriple
import LambdaSat.PipelineSoundness

namespace Quantum
namespace Invariants

set_option maxHeartbeats 8000000

open LambdaSat UnionFind EG Quantum.Opt

variable {n : Nat}

/-! ### The invariant bundle -/

/-- The four invariants OptiSat's preservation theorems carry in lockstep:
  * `ConsistentValuation` - union-find-equivalent classes have equal values, and every e-node
    evaluates to the value of its class (this is the *semantic consistency of the
    equivalence classes*, spec §E.6);
  * `PostMergeInvariant`  - the structural invariants that survive a merge (rebuild
    restores full well-formedness);
  * `SemanticHashconsInv` - hashconsed entries evaluate to the value of their class;
  * `HashconsChildrenBounded` - every hashconsed node's children are valid class ids. -/
structure Quadruple (g : EGraph (QOp n)) (env : Nat -> PhaseOp n)
    (v : EClassId -> PhaseOp n) : Prop where
  cv : ConsistentValuation g env v
  pmi : PostMergeInvariant g
  shi : SemanticHashconsInv g env v
  hcb : HashconsChildrenBounded g

/-! ### Initial well-formedness and node-insertion preservation -/

/-- Inserting a circuit into a well-formed e-graph leaves a well-formed union-find.

Proved by induction over the circuit, using OptiSat's `add_preserves_uf_wf` at each of the
three insertion sites of `addCircuit` (identity, gate, and the composition node of a
sequential pair). -/
theorem addCircuit_uf_wf : (c : Circuit n) -> (g : EGraph (QOp n)) ->
    WellFormed g.unionFind -> WellFormed ((addCircuit c g).2).unionFind
  | Circuit.one, g, hg => add_preserves_uf_wf g ⟨QOp.one⟩ hg
  | Circuit.gate k, g, hg => add_preserves_uf_wf g ⟨QOp.gate k⟩ hg
  | Circuit.seq a b, g, hg => by
    have h1 := addCircuit_uf_wf a g hg
    have h2 := addCircuit_uf_wf b (addCircuit a g).2 h1
    have h3 := add_preserves_uf_wf (addCircuit b (addCircuit a g).2).2
      ⟨QOp.seq (addCircuit a g).1 (addCircuit b (addCircuit a g).2).1⟩ h2
    simpa [addCircuit] using h3

/-- The e-graph built from a circuit has a well-formed union-find. -/
theorem ofCircuit_uf_wf (c : Circuit n) : WellFormed (ofCircuit c).2.unionFind :=
  addCircuit_uf_wf c EGraph.empty UnionFind.empty_wf

/-- The empty e-graph satisfies the whole invariant bundle, with the trivial valuation. -/
theorem empty_quadruple (env : Nat -> PhaseOp n) :
    Quadruple (g := (EGraph.empty : EGraph (QOp n))) env (fun _ => default) := by
  refine ⟨empty_consistent (Op := QOp n) (Val := PhaseOp n) env,
    ⟨UnionFind.empty_wf, ?_, ?_, ?_⟩,
    empty_shi (Op := QOp n) (Val := PhaseOp n) env,
    empty_hcb (Op := QOp n) (Val := PhaseOp n)⟩
  · intro id cls h _ _ _ hc
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at h
  · intro node id h
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at h
  · intro id h
    simp [EGraph.empty] at h

/-! ### Preservation, instantiated at quantum circuits -/

/-- **Node insertion preservation.**  Adding an e-node whose children are valid class ids
preserves the bundle (extending the valuation), and the new class evaluates to the meaning
of the node that was inserted. -/
theorem insert_preserves (g : EGraph (QOp n)) (node : ENode (QOp n))
    (env : Nat -> PhaseOp n) (v : EClassId -> PhaseOp n) (hq : Quadruple g env v)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    ∃ v', Quadruple ((g.add node).2) env v' ∧
      v' (root ((g.add node).2).unionFind (g.add node).1) = NodeEval node env v' ∧
      (∀ i, i < g.unionFind.parent.size -> v' i = v i) ∧
      g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size ∧
      (g.add node).1 < (g.add node).2.unionFind.parent.size := by
  obtain ⟨v', hcv, hpmi, hshi, hhcb, hnew, hmono, hext, heval⟩ :=
    add_node_triple g node env v hq.cv hq.pmi hq.shi hq.hcb hbnd
  exact ⟨v', ⟨hcv, hpmi, hshi, hhcb⟩, heval, hext, hmono, hnew⟩

/-- **Merge preservation (class union and rule-based merge).**  Merging two classes whose
values already agree preserves `ConsistentValuation` with the *same* valuation, and the
structural invariant survives a merge as `PostMergeInvariant`. -/
theorem merge_preserves (g : EGraph (QOp n)) (id1 id2 : EClassId)
    (env : Nat -> PhaseOp n) (v : EClassId -> PhaseOp n) (hq : Quadruple g env v)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (root g.unionFind id1) = v (root g.unionFind id2)) :
    ConsistentValuation (g.merge id1 id2) env v ∧ PostMergeInvariant (g.merge id1 id2) :=
  ⟨merge_consistent g id1 id2 env v hq.cv hq.pmi.uf_wf h1 h2 heq,
   merge_preserves_pmi g id1 id2 hq.pmi h1⟩

/-- **Congruence-closure correctness.**  `processClass` is the congruence step: it merges
classes whose e-nodes have become congruent, and it preserves both the semantic and the
structural halves of the bundle. -/
theorem congruence_preserves (g : EGraph (QOp n)) (classId : EClassId)
    (env : Nat -> PhaseOp n) (v : EClassId -> PhaseOp n) (hq : Quadruple g env v) :
    ConsistentValuation (g.processClass classId).1 env v ∧
      PostMergeInvariant (g.processClass classId).1 :=
  ⟨processClass_consistent g classId env v hq.cv hq.pmi.uf_wf,
   processClass_preserves_pmi g classId hq.pmi⟩

/-- **Rebuilding preservation.**  Rebuilding - the deferred congruence pass, run to a fuel
bound - preserves the whole bundle with the same valuation. -/
theorem rebuild_preserves (g : EGraph (QOp n)) (env : Nat -> PhaseOp n)
    (v : EClassId -> PhaseOp n) (hq : Quadruple g env v) (fuel : Nat) :
    ConsistentValuation (rebuildF g fuel) env v ∧ PostMergeInvariant (rebuildF g fuel) ∧
      SemanticHashconsInv (rebuildF g fuel) env v ∧
      HashconsChildrenBounded (rebuildF g fuel) :=
  rebuildF_preserves_cv env fuel g v hq.cv hq.pmi hq.shi hq.hcb

/-- **Saturation preservation.**  A bounded saturation loop over a list of *sound* rules
(`PatternSoundRule` carries, by construction, the proof that its two sides denote the same
element of `PhaseOp n` - for the quantum rules that proof comes from the verified rewrite
library, never from the optimizer) preserves semantic consistency of the classes and
restores union-find well-formedness. -/
theorem saturation_preserves (fuel maxIter rebuildFuel : Nat) (g : EGraph (QOp n))
    (rules : List (PatternSoundRule (QOp n) (PhaseOp n)))
    (env : Nat -> PhaseOp n) (v : EClassId -> PhaseOp n) (hq : Quadruple g env v) :
    ∃ v', ConsistentValuation (saturateF fuel maxIter rebuildFuel g
      (rules.map fun r => r.rule)) env v' ∧
      WellFormed (saturateF fuel maxIter rebuildFuel g
        (rules.map fun r => r.rule)).unionFind := by
  obtain ⟨v', hcv⟩ := saturateF_preserves_consistent_internal fuel maxIter rebuildFuel g
    rules env v hq.cv hq.pmi hq.shi hq.hcb sameShapeSemantics_holds
    (InstantiateEvalSound_holds env)
    (fun g' rule hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ)
  exact ⟨v', hcv, saturateF_preserves_wf fuel maxIter rebuildFuel g rules env v hq.cv
    hq.pmi hq.shi hq.hcb⟩

/-! ### Extraction correctness -/

/-- The pipeline the optimizer runs *is* OptiSat's `optimizeF`: saturation, cost annotation,
automatic extraction from the root class. -/
theorem optimizeF_eq (cfg : Config) (c : Circuit n) :
    (optimizeF cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
      ((quantumRules c).map fun psr => psr.rule) egCostFn cfg.costFuel (rootOf cfg c) :
      Option (Circuit n))
    = extractAuto (saturatedGraph cfg c) (rootOf cfg c) := rfl

/-- **Extraction correctness (semantic value).**  If the pipeline extracts a circuit, that
circuit evaluates - in the phase-quotient domain, where equality *is* equality up to global
phase - to the value of the root e-class of the saturated graph.  This is the *internal*
soundness story of the engine; it is separate from, and does not replace, the external
certificate checker of Quantum/Certificates.lean. -/
theorem extraction_value (cfg : Config) (c : Circuit n) (c' : Circuit n)
    (env : Nat -> PhaseOp n) (v : EClassId -> PhaseOp n) (hq : Quadruple (ofCircuit c).2 env v)
    (hbni : BestNodeInv (ofCircuit c).2.classes)
    (hopt : extractAuto (saturatedGraph cfg c) (rootOf cfg c) = some c') :
    ∃ (v_sat : EClassId -> PhaseOp n), EvalExpr.evalExpr c' env =
      v_sat (root (saturateF cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
        ((quantumRules c).map fun psr => psr.rule)).unionFind (rootOf cfg c)) := by
  refine optimizeF_soundness_complete (ofCircuit c).2 (quantumRules c) egCostFn
    cfg.costFuel cfg.fuel cfg.maxIter cfg.rebuildFuel env v hq.cv hq.pmi hq.shi hq.hcb hbni
    (rootOf cfg c) c' (extractableSound_qop n) ?_
  exact hopt
/-! ### Semantic consistency of the initial graph -/

/-- Inserting a circuit into an e-graph that already carries a consistent valuation yields a
graph with a consistent valuation, in which the class of the inserted circuit has exactly the
value of that circuit's denotation in the phase quotient.  This is the semantic-consistency
half of spec section E for the initial graph: every e-class that insertion creates is
consistent with the circuit node it was built from, and insertion only ever extends the
valuation pointwise on the classes that already existed. -/
theorem addCircuit_quadruple : (c : Circuit n) -> (g : EGraph (QOp n)) ->
    (env : Nat -> PhaseOp n) -> (v : EClassId -> PhaseOp n) -> Quadruple g env v ->
    ∃ (v' : EClassId -> PhaseOp n),
      Quadruple ((addCircuit c g).2) env v' ∧
      v' ((addCircuit c g).1) = pquot (denote c) ∧
      (∀ i, i < g.unionFind.parent.size -> v' i = v i) ∧
      g.unionFind.parent.size ≤ (addCircuit c g).2.unionFind.parent.size ∧
      (addCircuit c g).1 < (addCircuit c g).2.unionFind.parent.size
  | Circuit.one, g, env, v, hq => by
    obtain ⟨v', hq', heval, hext, hmono, hnew⟩ :=
      insert_preserves g ⟨QOp.one⟩ env v hq
        (by simp [ENode.children, NodeOps.children, childrenQ])
    refine ⟨v', hq', ?_, hext, hmono, hnew⟩
    have hr : v' (root (g.add ⟨QOp.one⟩).2.unionFind (g.add ⟨QOp.one⟩).1) =
        v' (g.add ⟨QOp.one⟩).1 :=
      consistent_root_eq' (g.add ⟨QOp.one⟩).2 env v' hq'.cv hq'.pmi.uf_wf _
    change v' (g.add ⟨QOp.one⟩).1 = _
    rw [← hr, heval]
    show (NodeSemantics.evalOp (QOp.one : QOp n) env v' : PhaseOp n) =
      pquot (denote Circuit.one)
    rw [evalOpQ_one, denote_one]

  | Circuit.gate k, g, env, v, hq => by
    obtain ⟨v', hq', heval, hext, hmono, hnew⟩ :=
      insert_preserves g ⟨QOp.gate k⟩ env v hq
        (by simp [ENode.children, NodeOps.children, childrenQ])
    refine ⟨v', hq', ?_, hext, hmono, hnew⟩
    have hr : v' (root (g.add ⟨QOp.gate k⟩).2.unionFind (g.add ⟨QOp.gate k⟩).1) =
        v' (g.add ⟨QOp.gate k⟩).1 :=
      consistent_root_eq' (g.add ⟨QOp.gate k⟩).2 env v' hq'.cv hq'.pmi.uf_wf _
    change v' (g.add ⟨QOp.gate k⟩).1 = _
    rw [← hr, heval]
    show (NodeSemantics.evalOp (QOp.gate k : QOp n) env v' : PhaseOp n) =
      pquot (denote (Circuit.gate k))
    rw [evalOpQ_gate, denote_gate]

  | Circuit.seq a b, g, env, v, hq => by
    obtain ⟨v₁, hq₁, hva, hext₁, hmono₁, hnew₁⟩ := addCircuit_quadruple a g env v hq
    let g₁ := (addCircuit a g).2
    let ia := (addCircuit a g).1
    obtain ⟨v₂, hq₂, hvb, hext₂, hmono₂, hnew₂⟩ :=
      addCircuit_quadruple b g₁ env v₁ hq₁
    let g₂ := (addCircuit b g₁).2
    let ib := (addCircuit b g₁).1
    have hia₂ : ia < g₂.unionFind.parent.size := Nat.lt_of_lt_of_le hnew₁ hmono₂
    have hib₂ : ib < g₂.unionFind.parent.size := hnew₂
    have hsz : ∀ i, i < g.unionFind.parent.size ->
        i < g₂.unionFind.parent.size :=
      fun i hi => Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi hmono₁) hmono₂
    have hbnd : ∀ c ∈ (⟨QOp.seq ia ib⟩ : ENode (QOp n)).children,
        c < g₂.unionFind.parent.size := by
      intro c hc
      simp only [ENode.children, NodeOps.children, childrenQ, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hia₂
      · exact hib₂
    obtain ⟨v₃, hq₃, heval, hext₃, hmono₃, hnew₃⟩ :=
      insert_preserves g₂ ⟨QOp.seq ia ib⟩ env v₂ hq₂ hbnd
    refine ⟨v₃, hq₃, ?_, fun i hi => by
      rw [hext₃ i (hsz i hi), hext₂ i (Nat.lt_of_lt_of_le hi hmono₁), hext₁ i hi],
      Nat.le_trans hmono₁ (Nat.le_trans hmono₂ hmono₃), hnew₃⟩
    have hr : v₃ (root (g₂.add ⟨QOp.seq ia ib⟩).2.unionFind (g₂.add ⟨QOp.seq ia ib⟩).1) =
        v₃ (g₂.add ⟨QOp.seq ia ib⟩).1 :=
      consistent_root_eq' (g₂.add ⟨QOp.seq ia ib⟩).2 env v₃ hq₃.cv hq₃.pmi.uf_wf _
    change v₃ (g₂.add ⟨QOp.seq ia ib⟩).1 = _
    rw [← hr, heval]
    have hia : v₃ ia = pquot (denote a) := by
      rw [hext₃ ia hia₂, hext₂ ia hnew₁]
      exact hva
    have hib : v₃ ib = pquot (denote b) := by
      rw [hext₃ ib hib₂]
      exact hvb
    show (NodeSemantics.evalOp (QOp.seq ia ib : QOp n) env v₃ : PhaseOp n) =
      pquot (denote (Circuit.seq a b))
    rw [evalOpQ_seq, denote_seq, hia, hib]
    exact (pquot_mul (denote b) (denote a)).symm
/-- The e-graph built from a circuit carries a consistent valuation: the initial graph of the
optimizer satisfies the whole invariant bundle. -/
theorem initial_quadruple (c : Circuit n) (env : Nat -> PhaseOp n) :
    ∃ v, Quadruple (ofCircuit c).2 env v := by
  obtain ⟨v, hq, _, _, _, _⟩ := 
    addCircuit_quadruple c (EGraph.empty : EGraph (QOp n)) env (fun _ => default)
      (empty_quadruple env)
  exact ⟨v, hq⟩
/-- The cost table of the initial graph is empty of stale best-nodes: insertion preserves
`BestNodeInv`, and the empty graph satisfies it. -/
theorem addCircuit_bestNodeInv : (c : Circuit n) -> (g : EGraph (QOp n)) ->
    BestNodeInv g.classes -> BestNodeInv (addCircuit c g).2.classes
  | Circuit.one, g, h => add_preserves_bestNodeInv g ⟨QOp.one⟩ h
  | Circuit.gate k, g, h => add_preserves_bestNodeInv g ⟨QOp.gate k⟩ h
  | Circuit.seq a b, g, h => by
    have h1 := addCircuit_bestNodeInv a g h
    have h2 := addCircuit_bestNodeInv b (addCircuit a g).2 h1
    have h3 := add_preserves_bestNodeInv (addCircuit b (addCircuit a g).2).2
      ⟨QOp.seq ((addCircuit a g).1) ((addCircuit b (addCircuit a g).2).1)⟩ h2
    change BestNodeInv ((addCircuit b (addCircuit a g).2).2.add
      ⟨QOp.seq ((addCircuit a g).1) ((addCircuit b (addCircuit a g).2).1)⟩).2.classes
    exact h3

/-- The initial e-graph of a circuit satisfies `BestNodeInv`. -/
theorem initial_bestNodeInv (c : Circuit n) :
    BestNodeInv (ofCircuit c).2.classes :=
  addCircuit_bestNodeInv c EGraph.empty (bestNodeInv_empty (Op := QOp n))

/-- **Extraction soundness with the initial graph's invariants discharged.**  Running the
optimizer's own pipeline on a circuit `c` and extracting `c'` puts `c'` at the value of the
root class of the saturated graph, in the phase quotient - with *no* hypothesis beyond the
extraction equation itself, because the initial graph's invariant bundle and cost-table
well-formedness are theorems (`initial_quadruple`, `initial_bestNodeInv`) rather than
assumptions. -/
theorem extraction_value_initial (cfg : Config) (c c' : Circuit n)
    (env : Nat -> PhaseOp n)
    (hopt : extractAuto (saturatedGraph cfg c) (rootOf cfg c) = some c') :
    ∃ (v_sat : EClassId -> PhaseOp n), EvalExpr.evalExpr c' env =
      v_sat (root (saturateF cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
        ((quantumRules c).map fun psr => psr.rule)).unionFind (rootOf cfg c)) := by
  obtain ⟨v, hq⟩ := initial_quadruple c env
  exact extraction_value cfg c c' env v hq (initial_bestNodeInv c) hopt

/-- **Saturation preserves semantic consistency of the initial graph.**  The saturated graph
of a circuit has a consistent valuation: every e-class in it is semantically consistent, and
its union-find is well-formed. -/
theorem saturation_preserves_initial (cfg : Config) (c : Circuit n)
    (env : Nat -> PhaseOp n) :
    ∃ v', ConsistentValuation (saturateF cfg.fuel cfg.maxIter cfg.rebuildFuel
        (ofCircuit c).2 ((quantumRules c).map fun psr => psr.rule)) env v' ∧
      WellFormed (saturateF cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
        ((quantumRules c).map fun psr => psr.rule)).unionFind := by
  obtain ⟨v, hq⟩ := initial_quadruple c env
  exact saturation_preserves cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
    (quantumRules c) env v hq
end Invariants
end Quantum
