/-
Turning the verified rewrite library into OptiSat rewrite rules, and bounded
certificate-producing search over them.

OptiSat patterns cannot bind qubit indices or angles: a pattern is a fixed e-node skeleton
with e-class holes.  So each schematic rule of Quantum/Rewrites.lean is *instantiated* over
the finite set of qubit indices of the register and the finite set of exact angles occurring
in the input circuit.  This is a bounded, documented form of rule instantiation: the search
space is finite and every rule instance that is generated carries its own proof of
soundness, inherited from the schematic rule.
-/
import Quantum.QuantumEGraph

namespace Quantum
namespace Opt

open LambdaSat UnionFind EG

/-! ### Finite instantiation data -/

/-- All qubit indices of an n-qubit register. -/
def allFin : (n : Nat) -> List (Fin n)
  | 0 => []
  | Nat.succ m => (allFin m).map Fin.succ ++ [⟨0, Nat.succ_pos m⟩]

/-- The angles occurring in a circuit. -/
def anglesOf : Circuit n -> List Angle
  | Circuit.one => []
  | Circuit.gate (Gate.rz _ a) => [a]
  | Circuit.gate (Gate.rx _ a) => [a]
  | Circuit.gate (Gate.ry _ a) => [a]
  | Circuit.gate (Gate.crz _ _ _ a) => [a]
  | Circuit.gate _ => []
  | Circuit.seq a b => anglesOf a ++ anglesOf b

/-- The gates occurring in a circuit. -/
def gatesOf : Circuit n -> List (Gate n)
  | Circuit.one => []
  | Circuit.gate g => [g]
  | Circuit.seq a b => gatesOf a ++ gatesOf b

/-- Candidate argument lists for rule instantiation.

Qubit indices range over the whole register (finite: `Fin n`); angles range over the angles
that occur in the circuit together with `0`; gate pairs range over the gates that occur.
Circuit arguments are *not* the full cartesian product of subcircuits — that would be cubic —
but the pairs and triples that actually appear as sequential nodes of the circuit.  This is
complete for the current circuit: an instance of a structural rule can only fire at a
position whose shape is already present, so its arguments are exactly the children of such a
node. -/
def candidateArgs (c : Circuit n) : List (List (Arg n)) :=
  let qs := (allFin n).map fun i => [Arg.q i]
  let qqs := do
    let i <- allFin n
    let j <- allFin n
    pure [Arg.q i, Arg.q j]
  let angs := anglesOf c ++ [0]
  let qaa := do
    let i <- allFin n
    let s <- angs
    let t <- angs
    pure [Arg.q i, Arg.a s, Arg.a t]
  let qjaa := do
    let i <- allFin n
    let j <- allFin n
    let s <- angs
    let t <- angs
    pure [Arg.q i, Arg.q j, Arg.a s, Arg.a t]
  let ggs := do
    let g₁ <- gatesOf c
    let g₂ <- gatesOf c
    pure [Arg.g g₁, Arg.g g₂]
  let subs := c.subcircuits
  let cs := subs.map fun d => [Arg.c d]
  let ccs := subs.filterMap fun d =>
    match d with
    | Circuit.seq a b => some [Arg.c a, Arg.c b]
    | _ => none
  let cccs := subs.filterMap fun d =>
    match d with
    | Circuit.seq (Circuit.seq a b) e => some [Arg.c a, Arg.c b, Arg.c e]
    | Circuit.seq a (Circuit.seq b e) => some [Arg.c a, Arg.c b, Arg.c e]
    | _ => none
  qs ++ qqs ++ qaa ++ qjaa ++ ggs ++ cs ++ ccs ++ cccs

/-- The schematic rules of the library are handled *schematically* by the e-graph (pattern
variables for subcircuits, see `structRules`), so their ground instances are dropped from the
instantiated set. -/
def instantiatedRules (n : Nat) : List (Rule n) :=
  (rules n).filter fun r => !(["assoc", "idL", "idR"] : List String).contains r.id

/-! ### Patterns from circuits -/

/-- A pattern matching the identity e-node. -/
def pOne : Pattern (QOp n) := .node QOp.one []

/-- A pattern matching the e-node of a primitive gate. -/
def pGate (g : Gate n) : Pattern (QOp n) := .node (QOp.gate g) []

/-- A pattern matching the composition of two e-classes.  The skeleton uses two distinct
placeholder ids so that the pattern satisfies AllDistinctChildren. -/
def pSeq (p q : Pattern (QOp n)) : Pattern (QOp n) := .node (QOp.seq 0 1) [p, q]

/-- Translate a circuit into a ground pattern. -/
def patOf : Circuit n -> Pattern (QOp n)
  | Circuit.one => pOne
  | Circuit.gate g => pGate g
  | Circuit.seq a b => pSeq (patOf a) (patOf b)

/-! ### Pattern evaluation -/

/-- A ground pattern has no pattern variables, so its evaluation is its node's semantics
with the children's values substituted positionally. -/
theorem eval_patOf {n : Nat} (c : Circuit n) (env : Nat -> PhaseOp n)
    (sigma : PatVarId -> PhaseOp n) :
    Pattern.eval (patOf c) env sigma = pquot (denote c) := by
  classical
  induction c with
  | one =>
      show Pattern.eval (Pattern.node QOp.one []) env sigma = pquot (denote Circuit.one)
      unfold Pattern.eval
      simp only [NodeOps.children, childrenQ, denote_one]
      rfl
  | gate g =>
      show Pattern.eval (Pattern.node (QOp.gate g) []) env sigma =
        pquot (denote (Circuit.gate g))
      unfold Pattern.eval
      simp only [NodeOps.children, childrenQ, denote_gate]
      rfl
  | seq a b iha ihb =>
      show Pattern.eval (Pattern.node (QOp.seq 0 1) [patOf a, patOf b]) env sigma =
        pquot (denote (Circuit.seq a b))
      unfold Pattern.eval
      simp only [NodeOps.children, childrenQ, evalOpQ, List.map_cons, List.map_nil, List.zip,
        List.lookup_cons, List.lookup_nil, denote_seq, iha, ihb]
      rfl

theorem allDistinct_patOf {n : Nat} (c : Circuit n) : AllDistinctChildren (patOf c) := by
  classical
  induction c with
  | one =>
      show AllDistinctChildren (Pattern.node QOp.one [])
      simp [AllDistinctChildren, NodeOps.children, childrenQ]
  | gate g =>
      show AllDistinctChildren (Pattern.node (QOp.gate g) [])
      simp [AllDistinctChildren, NodeOps.children, childrenQ]
  | seq a b iha ihb =>
      show AllDistinctChildren (Pattern.node (QOp.seq 0 1) [patOf a, patOf b])
      simp [AllDistinctChildren, NodeOps.children, childrenQ, iha, ihb]

/-! ### OptiSat rules generated from the verified rewrite library -/

/-- The OptiSat rewrite rule generated from a rule instantiation. -/
def toRewriteRule {n : Nat} (r : Rule n) (args : List (Arg n)) : RewriteRule (QOp n) := {
  name := r.id
  lhs := patOf (r.lhs args)
  rhs := patOf (r.rhs args) }

/-- The generated rule is sound in the phase quotient, hence a PatternSoundRule. -/
def toPatternSoundRule {n : Nat} (r : Rule n) (args : List (Arg n))
    (hs : r.side args = true) : PatternSoundRule (QOp n) (PhaseOp n) where
  rule := toRewriteRule r args
  soundness := by
    intro env σ
    show Pattern.eval (patOf (r.lhs args)) env σ = Pattern.eval (patOf (r.rhs args)) env σ
    rw [eval_patOf, eval_patOf]
    exact pquot_phase (r.sound args hs)
  lhs_wf := allDistinct_patOf _
  rhs_wf := allDistinct_patOf _

/-- The same instantiation in the *reverse* orientation: rhs → lhs.  A rule that preserves
or raises the cost is often what unlocks a later reduction, so both orientations are fed to
the saturation loop whenever either side can occur. -/
def toPatternSoundRuleFlip {n : Nat} (r : Rule n) (args : List (Arg n))
    (hs : r.side args = true) : PatternSoundRule (QOp n) (PhaseOp n) where
  rule := { name := r.id, lhs := patOf (r.rhs args), rhs := patOf (r.lhs args) }
  soundness := by
    intro env σ
    show Pattern.eval (patOf (r.rhs args)) env σ = Pattern.eval (patOf (r.lhs args)) env σ
    rw [eval_patOf, eval_patOf]
    exact pquot_phase ((r.sound args hs).symm)
  lhs_wf := allDistinct_patOf _
  rhs_wf := allDistinct_patOf _

/-! ### Schematic structural rules for the e-graph -/

/-- A pattern variable standing for an arbitrary subcircuit.  Unlike the gate rules, the
structural rules do not mention qubit indices or angles, so they can be handed to OptiSat
*schematically* instead of being instantiated over subcircuits of the input. -/
def pVar (i : Nat) : Pattern (QOp n) := .patVar i

/-- Sequential composition of two patterns.  The skeleton `QOp.seq 0 1` carries two distinct
placeholder child ids, which is what `AllDistinctChildren` requires. -/
def pSeqP (p q : Pattern (QOp n)) : Pattern (QOp n) := .node (QOp.seq 0 1) [p, q]

theorem eval_pVar {n : Nat} (i : Nat) (env : Nat -> PhaseOp n) (σ : Nat -> PhaseOp n) :
    Pattern.eval (pVar (n := n) i) env σ = σ i := by
  simp [pVar, Pattern.eval]

theorem eval_pOne {n : Nat} (env : Nat -> PhaseOp n) (σ : Nat -> PhaseOp n) :
    Pattern.eval (pOne (n := n)) env σ = pquot (1 : Operator n) := by
  classical
  simp [pOne, Pattern.eval, NodeOps.children, childrenQ]

theorem eval_pSeqP {n : Nat} (p q : Pattern (QOp n)) (env : Nat -> PhaseOp n)
    (σ : Nat -> PhaseOp n) :
    Pattern.eval (pSeqP (n := n) p q) env σ = Pattern.eval q env σ * Pattern.eval p env σ := by
  classical
  simp [pSeqP, Pattern.eval, NodeOps.children, childrenQ, List.zip, List.lookup]

theorem wf_pVar {n : Nat} (i : Nat) : AllDistinctChildren (pVar (n := n) i) := by
  classical
  simp [pVar, AllDistinctChildren]

theorem wf_pOne {n : Nat} : AllDistinctChildren (pOne (n := n)) := by
  classical
  simp [pOne, AllDistinctChildren, NodeOps.children, childrenQ]

theorem wf_pSeqP {n : Nat} (p q : Pattern (QOp n))
    (hp : AllDistinctChildren p) (hq : AllDistinctChildren q) :
    AllDistinctChildren (pSeqP (n := n) p q) := by
  classical
  simp only [pSeqP, AllDistinctChildren, NodeOps.children, childrenQ]
  refine ⟨by simp, by simp, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hq

/-- Reverse a sound rule: the reversed rule is sound because the semantic equality is
symmetric. -/
def psrFlip {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op] {Val : Type}
    [NodeSemantics Op Val] [Inhabited Val]
    (psr : PatternSoundRule Op Val) : PatternSoundRule Op Val :=
  { rule := { name := psr.rule.name, lhs := psr.rule.rhs, rhs := psr.rule.lhs },
    soundness := fun env σ => (psr.soundness env σ).symm
    lhs_wf := psr.rhs_wf
    rhs_wf := psr.lhs_wf }

/-- Associativity of sequential composition, as a schematic OptiSat pattern pair. -/
def assocPattern (n : Nat) : RewriteRule (QOp n) :=
  { name := "assoc"
    lhs := pSeqP (n := n) (pSeqP (n := n) (pVar 0) (pVar 1)) (pVar 2)
    rhs := pSeqP (n := n) (pVar 0) (pSeqP (n := n) (pVar 1) (pVar 2)) }

/-- Left identity of `Circuit.one`, as a schematic OptiSat pattern pair. -/
def idLPattern (n : Nat) : RewriteRule (QOp n) :=
  { name := "idL"
    lhs := pSeqP (n := n) (pOne (n := n)) (pVar 0)
    rhs := pVar (n := n) 0 }

/-- Right identity of `Circuit.one`, as a schematic OptiSat pattern pair. -/
def idRPattern (n : Nat) : RewriteRule (QOp n) :=
  { name := "idR"
    lhs := pSeqP (n := n) (pVar 0) (pOne (n := n))
    rhs := pVar (n := n) 0 }

/-- Associativity of sequential composition, as a schematic OptiSat rule. -/
def structAssoc (n : Nat) : PatternSoundRule (QOp n) (PhaseOp n) where
  rule := assocPattern n
  soundness := by
    intro env σ
    show Pattern.eval (assocPattern (n := n)).lhs env σ =
      Pattern.eval (assocPattern (n := n)).rhs env σ
    rw [show (assocPattern (n := n)).lhs = pSeqP (n := n) (pSeqP (n := n) (pVar 0) (pVar 1))
        (pVar 2) from rfl,
      show (assocPattern (n := n)).rhs = pSeqP (n := n) (pVar 0)
        (pSeqP (n := n) (pVar 1) (pVar 2)) from rfl]
    repeat rw [eval_pSeqP]
    repeat rw [eval_pVar]
    exact (pquot_op_mul_assoc _ _ _).symm
  lhs_wf := wf_pSeqP _ _ (wf_pSeqP _ _ (wf_pVar 0) (wf_pVar 1)) (wf_pVar 2)
  rhs_wf := wf_pSeqP _ _ (wf_pVar 0) (wf_pSeqP _ _ (wf_pVar 1) (wf_pVar 2))

/-- Left identity of `Circuit.one`, as a schematic OptiSat rule. -/
def structIdL (n : Nat) : PatternSoundRule (QOp n) (PhaseOp n) where
  rule := idLPattern n
  soundness := by
    intro env σ
    show Pattern.eval (idLPattern (n := n)).lhs env σ = Pattern.eval (idLPattern (n := n)).rhs env σ
    rw [show (idLPattern (n := n)).lhs = pSeqP (n := n) (pOne (n := n)) (pVar 0) from rfl,
      show (idLPattern (n := n)).rhs = pVar (n := n) 0 from rfl,
      eval_pSeqP, eval_pOne, eval_pVar]
    exact pquot_op_mul_one _
  lhs_wf := wf_pSeqP _ _ wf_pOne (wf_pVar 0)
  rhs_wf := wf_pVar 0

/-- Right identity of `Circuit.one`, as a schematic OptiSat rule. -/
def structIdR (n : Nat) : PatternSoundRule (QOp n) (PhaseOp n) where
  rule := idRPattern n
  soundness := by
    intro env σ
    show Pattern.eval (idRPattern (n := n)).lhs env σ = Pattern.eval (idRPattern (n := n)).rhs env σ
    rw [show (idRPattern (n := n)).lhs = pSeqP (n := n) (pVar 0) (pOne (n := n)) from rfl,
      show (idRPattern (n := n)).rhs = pVar (n := n) 0 from rfl,
      eval_pSeqP, eval_pOne, eval_pVar]
    exact pquot_op_one_mul _
  lhs_wf := wf_pSeqP _ _ (wf_pVar 0) wf_pOne
  rhs_wf := wf_pVar 0

/-- The structural rules in both orientations.  Re-associating is cost-neutral but is what
exposes adjacent gate pairs to the cancelling rules, which is exactly the non-greedy behaviour
equality saturation is for. -/
def structRules (n : Nat) : List (PatternSoundRule (QOp n) (PhaseOp n)) :=
  let a := structAssoc n
  let l := structIdL n
  let r := structIdR n
  [a, psrFlip a, l, psrFlip l, r, psrFlip r]

/-- All sound rule instances whose left-hand side *or* right-hand side occurs as a
subcircuit of the input, in both orientations, as OptiSat rules, together with the schematic
structural rules.  Restricting the gate rules to occurring subcircuits keeps the generated
rule set finite and small; it is a documented bound on the search space, not a change in
semantics: every rule instance is still proved sound individually, and every step of the
resulting derivation is re-checked independently. -/
def quantumRules {n : Nat} (c : Circuit n) : List (PatternSoundRule (QOp n) (PhaseOp n)) :=
  let subs := c.subcircuits
  ((instantiatedRules n).flatMap fun r =>
    (candidateArgs c).flatMap fun args =>
      if hs : r.side args = true then
        let occursL := subs.any fun d => d == r.lhs args
        let occursR := subs.any fun d => d == r.rhs args
        (if occursL then [toPatternSoundRule r args hs] else []) ++
          (if occursR then [toPatternSoundRuleFlip r args hs] else [])
      else []) ++ structRules n

/-! ### One-step rewrites and certificate synthesis -/

/-- All hole positions of a circuit, given an outer context. -/
def allContextsFrom : Circuit n -> Ctx n -> List (Ctx n)
  | Circuit.one, k => [k]
  | Circuit.gate _, k => [k]
  | Circuit.seq a b, k =>
    k :: allContextsFrom a (Ctx.seqR k b) ++ allContextsFrom b (Ctx.seqL a k)

/-- The cost used by the e-graph: one per primitive gate, zero for identity and composition.
This is the gateCount component of Quantum.Cost. -/
def egCostFn {n : Nat} : ENode (QOp n) -> Nat
  | ⟨QOp.one⟩ => 0
  | ⟨QOp.gate _⟩ => 1
  | ⟨QOp.seq _ _⟩ => 0

/-- Every single-step rewrite of a circuit, paired with the step that performs it.
Only rule instances whose arguments occur in the circuit are considered, so this is finite
and effectively computable. -/
def oneStepCandidates (c : Circuit n) : List (Step n × Circuit n) :=
  (rules n).flatMap fun r =>
    (candidateArgs c).flatMap fun args =>
      if hs : r.side args = true then
        ([false, true]).flatMap fun bw =>
          (allContextsFrom c Ctx.hole).flatMap fun ctx =>
            let lhs := if bw then r.rhs args else r.lhs args
            let rhs := if bw then r.lhs args else r.rhs args
            if decide (Ctx.fill ctx lhs = c) then
              [({ ruleId := r.id, args := args, ctx := ctx, backward := bw },
                Ctx.fill ctx rhs)]
            else []
      else []

/-- The one-step rewrites of a circuit, filtered by the independent checker's own step
application function: a pair `(s, c')` is in the list only if `applyStep c s = some c'`,
i.e. only if the very function that validates certificates accepts the step.  The search
therefore cannot propose a step its own checker would reject, and no property of the
enumeration above is trusted. -/
def oneStepRewrites (c : Circuit n) : List (Step n × Circuit n) :=
  (oneStepCandidates c).filter fun p => decide (applyStep c p.1 = some p.2)

/-- Every pair produced by the search really is an application of its step, as judged by the
independent checker's `applyStep`. -/
theorem oneStepRewrites_apply {n : Nat} {c : Circuit n} {p : Step n × Circuit n}
    (h : p ∈ oneStepRewrites c) : applyStep c p.1 = some p.2 :=
  of_decide_eq_true ((List.mem_filter.mp h).2)

/-- Every step produced by the search preserves the semantics up to global phase. -/
theorem oneStepRewrites_sound {n : Nat} {c c' : Circuit n} {s : Step n}
    (h : (s, c') ∈ oneStepRewrites c) : PhaseEquivalent c c' :=
  applyStep_sound s (oneStepRewrites_apply h)

/-! ### The greedy baseline -/

/-- The first one-step rewrite of `c` that strictly decreases the gate count, if any. -/
def greedyStep? (c : Circuit n) : Option (Step n × Circuit n) :=
  ((oneStepRewrites c).filter fun p =>
      decide ((Cost.of p.2).gateCount < (Cost.of c).gateCount)).head?

/-- The greedy baseline: repeatedly apply the first one-step rewrite that *strictly decreases*
the gate count, and stop when no such step exists.  It never applies a cost-neutral or
cost-increasing step, so it cannot re-associate a circuit or commute two anticommuting gates
into a cancelling position.  This is a restriction of the search space, not a different
semantics: every step it takes is a checked certificate step, and `greedy_phaseEquivalent`
proves the baseline sound.  The fuel bounds the number of steps; the definition is structural
in the fuel, so the baseline terminates on every input. -/
def greedy : (fuel : Nat) -> Circuit n -> Circuit n
  | 0, c => c
  | fuel + 1, c =>
      match greedyStep? c with
      | none => c
      | some (_, c') => greedy fuel c'

@[simp] theorem greedy_zero (c : Circuit n) : greedy 0 c = c := rfl

theorem greedy_succ (fuel : Nat) (c : Circuit n) :
    greedy (fuel + 1) c = match greedyStep? c with
      | none => c
      | some (_, c') => greedy fuel c' := rfl

theorem greedy_none (fuel : Nat) (c : Circuit n) (h : greedyStep? c = none) :
    greedy (fuel + 1) c = c := by
  show (match greedyStep? c with | none => c | some (_, x) => greedy fuel x) = c
  rw [h]

theorem greedy_some (fuel : Nat) (c c' : Circuit n) (s : Step n)
    (h : greedyStep? c = some (s, c')) : greedy (fuel + 1) c = greedy fuel c' := by
  show (match greedyStep? c with | none => c | some (_, x) => greedy fuel x) = greedy fuel c'
  rw [h]

set_option maxHeartbeats 4000000 in
/-- The greedy baseline is sound: its result is phase-equivalent to its input.  Every step it
takes is a step the independent checker accepts, so the baseline is a *sound* strategy — it is
merely weaker than equality saturation, which is what Example F demonstrates. -/
theorem greedy_phaseEquivalent : (fuel : Nat) -> (c : Circuit n) ->
    PhaseEquivalent (greedy fuel c) c
  | 0, c => PhaseEquivalent.refl c
  | fuel + 1, c => by
      set_option maxHeartbeats 4000000 in
      classical
      rcases h : greedyStep? c with _ | ⟨⟨s, c'⟩⟩
      · rw [greedy_none fuel c h]
        exact PhaseEquivalent.refl c
      · rw [greedy_some fuel c c' s h]
        refine PhaseEquivalent.trans (greedy_phaseEquivalent fuel c') ?_
        have hmem : (s, c') ∈ oneStepRewrites c := by
          have hsub : (s, c') ∈ (oneStepRewrites c).filter fun p =>
              decide ((Cost.of p.2).gateCount < (Cost.of c).gateCount) := by
            unfold greedyStep? at h
            obtain ⟨rest, hrest⟩ := (List.head?_eq_some_iff).mp h
            exact hrest ▸ List.Mem.head _
          exact (List.mem_filter.mp hsub).1
        exact (applyStep_sound s (oneStepRewrites_apply (n := n) (c := c) (p := (s, c'))
          hmem)).symm

/-! ### Certificate synthesis by bounded search -/

/-- Is the result circuit of one rewrite no more expensive than that of another? -/
def stepLe {n : Nat} (p q : Step n × Circuit n) : Bool :=
  decide ((Cost.of p.2).gateCount ≤ (Cost.of q.2).gateCount)

/-- Insert one rewrite into an already sorted list.  Written with an accumulator so that the
function is structurally recursive (no `partial` anywhere in this project). -/
def insertStep {n : Nat} (x : Step n × Circuit n) (acc : List (Step n × Circuit n)) :
    List (Step n × Circuit n) -> List (Step n × Circuit n)
  | [] => acc.reverse ++ [x]
  | y :: ys => if stepLe x y then acc.reverse ++ (x :: y :: ys) else insertStep x (y :: acc) ys

/-- Stable insertion sort of rewrites by the gate count of their result: cost-decreasing
steps are explored before cost-neutral ones, and those before cost-increasing ones. -/
def sortByCost {n : Nat} : List (Step n × Circuit n) -> List (Step n × Circuit n) :=
  List.foldl (fun acc x => insertStep x [] acc) []

/-- The unseen successors of `c`, cheapest first, each paired with the derivation that
reaches it. -/
def deriveSuccessors {n : Nat} (c : Circuit n) (path : Certificate n) (seen : List (Circuit n)) :
    List (Circuit n × Certificate n) :=
  let nexts := (oneStepRewrites c).filter fun p => !((c :: seen).any fun d => d == p.2)
  (sortByCost nexts).map fun (s, c') => (c', path ++ [s])

/-- Breadth-first search for a derivation from `c` to `target`, bounded by a maximum number
of rewrite steps and by a global node budget, with a visited set so that the search space is
finite and no circuit is expanded twice.  Termination is structural in the budget.

The result is a certificate; it is *always* re-verified by the independent checker before the
optimizer returns it, so nothing here is trusted for correctness. -/
def findDerivation {n : Nat} (maxSteps : Nat) (target : Circuit n) :
    (fuel : Nat) -> List (Circuit n × Certificate n) -> List (Circuit n) ->
    Option (Certificate n)
  | 0, _, _ => none
  | fuel + 1, queue, seen =>
    match queue with
    | [] => none
    | (c, path) :: rest =>
      if decide (c = target) then some path
      else if decide (path.length ≥ maxSteps) then findDerivation maxSteps target fuel rest seen
      else findDerivation maxSteps target fuel (rest ++ deriveSuccessors c path seen) (c :: seen)

/-- Optimizer configuration: explicit resource bounds on every loop. -/
structure Config where
  /-- fuel for e-matching and instantiation inside one saturation round -/
  fuel : Nat := 300
  /-- maximum number of saturation rounds -/
  maxIter : Nat := 6
  /-- fuel for congruence rebuilding in one round -/
  rebuildFuel : Nat := 300
  /-- iterations of the cost fixpoint computation -/
  costFuel : Nat := 60
  /-- maximum length of a synthesized derivation -/
  maxSteps : Nat := 8
  /-- maximum number of circuits explored by the derivation search -/
  searchBudget : Nat := 4000
  /-- the lexicographic cost policy used for reporting -/
  costConfig : CostConfig := CostConfig.default
deriving Repr, Inhabited

/-- The default configuration. -/
def Config.default : Config := {}

/-- The final gate of the optimizer: a candidate result is returned only if the independent
checker accepts its certificate; otherwise the input circuit is returned together with the
empty (reflexive) certificate, which the checker always accepts.  This is the fail-closed
contract required of the public API. -/
def finish (c : Circuit n) (c' : Circuit n) (cert : Certificate n) :
    Circuit n × Certificate n :=
  if decide (checkCertificate c c' cert) then (c', cert) else (c, [])

/-- The e-class of the whole input circuit. -/
def rootOf (cfg : Config) (c : Circuit n) : EClassId := (ofCircuit c).1

/-- The e-graph built from `c`, saturated and cost-annotated under `cfg`. -/
def saturatedGraph (cfg : Config) (c : Circuit n) : EGraph (QOp n) :=
  computeCostsF (saturateF cfg.fuel cfg.maxIter cfg.rebuildFuel (ofCircuit c).2
    ((quantumRules c).map fun psr => psr.rule)) egCostFn cfg.costFuel

/-- The optimizer body, in a form whose branches can be reasoned about directly. -/
def optimizeFrom (cfg : Config) (c : Circuit n) : Option (Circuit n × Certificate n) :=
  match extractAuto (saturatedGraph cfg c) (rootOf cfg c) with
  | none => some (finish c c [])
  | some c' =>
      match findDerivation cfg.maxSteps c' cfg.searchBudget [(c, [])] [] with
      | some cert => some (finish c c' cert)
      | none => some (finish c c [])

/-- Run the equality-saturation engine on a circuit and return the extracted circuit together
with a certificate that the independent checker accepts.

If no better circuit can be certified, the input circuit is returned together with the empty
(reflexive) certificate, which the checker accepts.  The optimizer never returns a circuit
whose certificate has not been checked: see `Opt.optimize_sound`. -/
def optimize (cfg : Config) (c : Circuit n) : Option (Circuit n × Certificate n) :=
  optimizeFrom cfg c

theorem optimize_eq (cfg : Config) (c : Circuit n) : optimize cfg c = optimizeFrom cfg c := rfl

end Opt
end Quantum
