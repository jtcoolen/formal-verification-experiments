/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Compress
import ProtSat.Benchmarks

/-!
# ProtSat: refinement R1 - the pruned event enumerator

## Why this module exists

`ProtSat.Reference.Explore.candidates` offers, at *every* configuration, `Ev.idle` and a deduction
for *every* message of the universe (`Explore.lean:149`), and `ProtSat.Reference.stepOf` *accepts*
a deduction of a message the attacker already knows: `oneStepBool`'s first disjunct is
`decide (t in C.kn)` (`Certificate.lean:122`), and the step is `publish C t`, which appends a
second copy of `t` (`Reference.lean:121`, `Reference.lean:210`). So the enumeration spends most of
its nodes on executions that either do nothing at all or duplicate a message already held, and the
duplicates make the resulting configurations *literally different*, so nothing merges them.

The measured cost, from the profiling run that motivated this module and re-measured here:

* `Contract.Gates.secureQ` at its own bound (three events): 258 nodes unpruned, **3 nodes pruned**.
* The same query at the bound `Compress` *derives* from the model - sixteen events - is still
  **3 nodes** pruned (`Gates.secureQ_derived_nodeCount`), and the kernel decides
  `attackFoundP (Compress.derived Compress.secureQ) = false` in 0.06 s
  (`Gates.secureQ_derived_attackFoundP_false`). The unpruned search cannot reach sixteen events at
  all: it is already at 258 nodes after three.
* `Benchmarks.NSL2c` at `rounds := 0`: 3,808,070 nodes at five events unpruned, 2,738 pruned; at
  the exhaustion bound `exB0` the pruned search is 115 nodes and the kernel decides it in 4.4 s -
  against the 174 s that `ProtSat.Benchmarks` costs as a module today.

## What this module does

`candidatesP` deletes exactly the two kinds of event that cannot matter - `Ev.idle`, and `Ev.ded t`
when `t` is already in `C.kn`, the same test the deduction step itself uses as its first disjunct -
and the whole explorer is mirrored over it: `extendP`, `frontierP`, `allNodesP`,
`explorerAttackP`, `attackFoundP`. The mirrors are structurally identical to
`ProtSat.Reference.Explore`, so the pruned search is a *refinement* in the sense the roadmap asks
for:

`@
Prune.explorerAttack_equiv  : explorerAttack  P B = explorerAttackP P B
Prune.attackFound_equiv     : attackFound     q   = attackFoundP     q
@`

The easy direction is that a pruned attack is an attack: `candidatesP` is a sublist of
`candidates`. The hard direction is that every attack has a pruned witness, and that is where
`ProtSat.Compress` pays off - with one new induction. `Compress.dropRedundant` deletes idle
events and deductions whose message is already in the *accumulator*, which is the initial knowledge
plus the deductions kept so far: a message an honest `send` published is known but not in the
accumulator, so the compressed
trace of `Compress` can still contain a deduction that `candidatesP` prunes, and its output is not
in general enumerated by `frontierP`. `runs_prune` is the same deletion restated against the
*enumerator* and against the configuration's own knowledge: a run can be replayed by `frontierP`,
up to the extensional equality `Compress.CfgEq` of the configurations it visits - it has to be up to
`CfgEq`, because a redundant deduction really does change the configuration by appending a copy, so
the pruned run reaches a *different* configuration than the original one did. `violates_congr` and
`goalViolation_congr` then move the verdict across, reusing `Compress.leaks_congr`,
`Compress.inBounds_congr`, `Compress.agrees_renumber` and `Compress.agreesInj_renumber` rather than
re-proving them, and `Compress.compress_secrecy`, `compress_agreement` and `compress_agreementInj`
supply the length bound that makes the pruned search at the derived bound exhaustive.

Because the two searches answer the same question and the pruned one is small, the derived bound
stops being a reduction and becomes a decision: `allLengthsSafe_of_attackFoundP_false` turns a
single `decide` on the pruned search at the derived bound into `Compress.allLengthsSafe` - safety
for executions of *every* length inside the query's own universe. `secureQ_allLengthsSafe` is that
decision, made by the kernel, on the contract's own secure gate model.

## What this module does not do

It does not make NS separable from NSL at the interesting bound. The pruning removes the two kinds
of step that provably cannot matter; it does not merge two different executions that reach the same
knowledge, and the surviving branching factor is still exponential in the number of events.
Extrapolating the measured 2.3x growth per event on the NSL model, thirteen events is about
6 * 10 ^ 4 seconds of kernel time, so the sixteen-event bound this module reaches on `secureQ` is
specific to a model whose universe is small and whose honest role is short.

It does not canonicalise the knowledge representation: `Cfg.kn` is still a list with duplicates,
and what is proved here is an equivalence between two *enumerations*, not that a configuration has
a normal form. And it does not prune anything the semantics can observe: `Ev.recv` of a message the
session already holds is still offered, because `stepOf` stores it again and a later `check` reads
the store.
-/

namespace ProtSat.Prune

open ProtSat Term Protocol Bounded
open ProtSat.Reference
open ProtSat.Reference.Explore
open ProtSat.Reference.Contract
open ProtSat.Compress

/-! ### The pruned candidate list -/

/-- **The pruned events worth trying at a configuration**: the explorer's candidates with
`Ev.idle` and every deduction of an already-known message removed. The "already known" test is
`t in C.kn`, exactly the first disjunct of `oneStepBool` that the deduction case of `stepOf`
tests; any other test would make the enumeration below unsound in one direction and incomplete in
the other. -/
def candidatesP (P : Protocol) (B : Bounds) (C : Reference.Cfg) : List Reference.Ev :=
  (candidates P B C).filter fun e => match e with
  | Reference.Ev.idle => false
  | Reference.Ev.ded t => ! (t ∈ C.kn)
  | _ => true

/-- Every event the pruned enumerator offers is an event the explorer offers. -/
theorem candidatesP_subset_candidates {P : Protocol} {B : Bounds} {C : Reference.Cfg}
    {e : Reference.Ev} (h : e ∈ candidatesP P B C) : e ∈ candidates P B C :=
  (List.mem_filter.mp h).1

/-- **The filter removes nothing else.** An event the explorer offers that is not `Ev.idle` and not
a deduction of a message the configuration already knows is offered by the pruned enumerator. -/
theorem candidatesP_of_candidates {P : Protocol} {B : Bounds} {C : Reference.Cfg}
    {e : Reference.Ev} (hc : e ∈ candidates P B C) (hi : e ≠ Reference.Ev.idle)
    (hd : ∀ t, e = Reference.Ev.ded t → t ∉ C.kn) : e ∈ candidatesP P B C := by
  classical
  rw [candidatesP, List.mem_filter]
  refine ⟨hc, ?_⟩
  cases e with
  | idle => exact absurd rfl hi
  | ded t =>
      by_cases h : t ∈ C.kn
      · exact absurd h (hd t rfl)
      · simp [h]
  | recv _ _ => trivial
  | generate _ _ => trivial
  | act _ => trivial

/-- **The pruned enumerator still offers every bounded step that matters.** -/
theorem candidatesP_of_rel {P : Protocol} {B : Bounds} {C C' : Reference.Cfg}
    {e : Reference.Ev} (hstep : Reference.Rel P C e C') (hb : inBounds P B C)
    (hb' : inBounds P B C')
    (hi : e ≠ Reference.Ev.idle) (hd : ∀ t, e = Reference.Ev.ded t → t ∉ C.kn) :
    e ∈ candidatesP P B C :=
  candidatesP_of_candidates (candidates_complete hstep hb hb') hi hd

/-! ### The explorer, mirrored over the pruned candidates -/

/-- The one-step extension of a node over `candidatesP`. Compare `Explore.extend`: the only
difference is the candidate list. -/
def extendP (P : Protocol) (B : Bounds) (x : Node) : List Node :=
  (candidatesP P B x.cfg).flatMap fun e =>
    match stepB P B x.cfg e with
    | none => []
    | some C' => [{ cfg := C', tr := x.tr ++ [e], Cs := x.Cs ++ [C'] }]

/-- Membership in `extendP` is exactly a bounded step by a pruned candidate. -/
theorem mem_extendP_iff {P : Protocol} {B : Bounds} {x y : Node} :
    y ∈ extendP P B x <->
      ∃ e C', e ∈ candidatesP P B x.cfg ∧ stepB P B x.cfg e = some C' ∧
        y.cfg = C' ∧ y.tr = x.tr ++ [e] ∧ y.Cs = x.Cs ++ [C'] := by
  unfold extendP
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hw⟩
    rcases hstep : stepB P B x.cfg e with _ | C'
    · simp [hstep] at hw
    · rw [hstep] at hw
      rw [List.mem_singleton] at hw
      cases hw
      exact ⟨e, C', he, hstep, rfl, rfl, rfl⟩
  · rintro ⟨e, C', he, hstep, h1, h2, h3⟩
    refine ⟨e, he, ?_⟩
    rw [hstep, List.mem_singleton]
    cases y
    simp_all

/-- Every pruned extension is an extension. -/
theorem extendP_subset_extend (P : Protocol) (B : Bounds) (x : Node) :
    ∀ y ∈ extendP P B x, y ∈ extend P B x := by
  intro y hy
  rw [mem_extendP_iff] at hy
  obtain ⟨e, C', he, hstep, h1, h2, h3⟩ := hy
  rw [mem_extend_iff]
  exact ⟨e, C', candidatesP_subset_candidates he, hstep, h1, h2, h3⟩

/-- **The pruned frontier**: nodes reachable in exactly `k` pruned bounded steps. -/
def frontierP : (P : Protocol) -> (B : Bounds) -> Nat -> Node -> List Node
  | _, _, 0, x => [x]
  | P, B, k + 1, x => (extendP P B x).flatMap (frontierP P B k)

@[simp] theorem frontierP_zero (P : Protocol) (B : Bounds) (x : Node) :
    frontierP P B 0 x = [x] := rfl

/-- Extending a pruned frontier member is a pruned frontier member one step out. -/
theorem mem_frontierP_extend {P : Protocol} {B : Bounds} {k : Nat} {x y z : Node}
    (hy : y ∈ extendP P B x) (hz : z ∈ frontierP P B k y) : z ∈ frontierP P B (k + 1) x :=
  List.mem_flatMap.mpr ⟨y, hy, hz⟩

/-- Every pruned frontier node is on the explorer's frontier. -/
theorem frontierP_subset_frontier {P : Protocol} {B : Bounds} {k : Nat} {x y : Node}
    (h : y ∈ frontierP P B k x) : y ∈ frontier P B k x := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
      rw [frontierP, List.mem_flatMap] at h
      obtain ⟨z, hz, hy⟩ := h
      exact mem_frontier_extend (extendP_subset_extend P B x z hz) (ih hy)

/-- All nodes reachable in at most `n` pruned bounded steps from the initial node. -/
def allNodesP (P : Protocol) (B : Bounds) (n : Nat) : List Node :=
  (List.range (n + 1)).flatMap fun k => frontierP P B k (initNode P)

/-- Every node the pruned search visits is a node the explorer visits. -/
theorem allNodesP_subset_allNodes {P : Protocol} {B : Bounds} {n : Nat} {x : Node}
    (h : x ∈ allNodesP P B n) : x ∈ allNodes P B n := by
  rw [allNodesP, List.mem_flatMap] at h
  obtain ⟨k, hk, hy⟩ := h
  rw [allNodes, List.mem_flatMap]
  exact ⟨k, hk, frontierP_subset_frontier hy⟩

/-- **The pruned explorer's answer.** Compare `Explore.explorerAttack`. -/
def explorerAttackP (P : Protocol) (B : Bounds) : Bool :=
  (allNodesP P B B.steps).any (nodeViolates P)

/-- **The pruned contract's answer.** Compare `Contract.attackFound`, the question the verdict
machinery consumes: the mirror is stated at this level so the equivalence lands where the contract
uses it. -/
def attackFoundP (q : Query) : Bool :=
  (allNodesP q.protocol q.bounds q.bounds.steps).any (nodeViolatesQuery q)

/-- A pruned attack is an attack: the pruning only removes events, so anything the pruned search
finds the explorer finds. -/
theorem explorerAttackP_imp {P : Protocol} {B : Bounds} (h : explorerAttackP P B = true) :
    explorerAttack P B = true := by
  rw [explorerAttackP, List.any_eq_true] at h
  obtain ⟨x, hx, hv⟩ := h
  rw [explorerAttack, List.any_eq_true]
  exact ⟨x, allNodesP_subset_allNodes hx, hv⟩

/-- A pruned attack on a query is an attack on it. -/
theorem attackFoundP_imp {q : Query} (h : attackFoundP q = true) : attackFound q = true := by
  rw [attackFoundP, attackFound, List.any_eq_true] at *
  obtain ⟨x, hx, hv⟩ := h
  exact ⟨x, allNodesP_subset_allNodes hx, hv⟩

/-! ### Pruned runs: what the compression has to produce -/

/-- **A pruned walk.** `prunedWalk P B C tr` says that walking `tr` from `C` takes a step that
stays inside the bounds at every event and that every one of those events is offered by
`candidatesP`. It is the property `runs_prune` constructs and `frontierP_of_prunedWalk` consumes. -/
def prunedWalk : (P : Protocol) -> (B : Bounds) -> Reference.Cfg -> List Reference.Ev -> Prop
  | _, _, _, [] => True
  | P, B, C, e :: tr =>
      ∃ C', stepB P B C e = some C' ∧ e ∈ candidatesP P B C ∧ prunedWalk P B C' tr

/-- The empty walk is pruned. -/
theorem prunedWalk_nil (P : Protocol) (B : Bounds) (C : Reference.Cfg) :
    prunedWalk P B C [] := trivial

/-- A bounded step by a pruned candidate, followed by a pruned walk, is a pruned walk. -/
theorem prunedWalk_cons {P : Protocol} {B : Bounds} {C C' : Reference.Cfg} {e : Reference.Ev}
    {tr : List Reference.Ev} (hstep : stepB P B C e = some C')
    (hmem : e ∈ candidatesP P B C) (h : prunedWalk P B C' tr) : prunedWalk P B C (e :: tr) :=
  ⟨C', hstep, hmem, h⟩

/-- Inversion for `prunedWalk`. -/
theorem prunedWalk_cons_inv {P : Protocol} {B : Bounds} {C : Reference.Cfg}
    {e : Reference.Ev} {tr : List Reference.Ev} (h : prunedWalk P B C (e :: tr)) :
    ∃ C', stepB P B C e = some C' ∧ e ∈ candidatesP P B C ∧ prunedWalk P B C' tr := h

/-- **R1: every bounded run has a pruned run that covers it extensionally.** Given a run of `tr`
from `C` whose configurations are all inside the bounds, and a configuration `C₀` extensionally
equal to `C`, there is a *pruned* run `tr'` from `C₀`, no longer than `tr`, whose visited
configurations correspond to the original ones in both directions up to `CfgEq`, and whose
authentication records are the original ones. The events the pruned run drops are exactly the idle
steps and the deductions of a message the configuration already knows - and the latter can be
dropped precisely because appending a copy of a known message is a `CfgEq`-no-op
(`cfgEq_publish_self`), which is also why the statement has to be up to `CfgEq` and not literal. -/
theorem runs_prune {P : Protocol} {B : Bounds} :
    ∀ {C₀ C : Reference.Cfg} {tr : List Reference.Ev} {Cs : List Reference.Cfg},
      CfgEq C₀ C -> Reference.Runs P C tr Cs -> (∀ C' ∈ Cs, inBounds P B C') ->
      ∃ (tr' : List Reference.Ev) (Cs' : List Reference.Cfg),
        Reference.Runs P C₀ tr' Cs' ∧ prunedWalk P B C₀ tr' ∧ tr'.length ≤ tr.length ∧
          (∀ D ∈ Cs', ∃ E ∈ Cs, CfgEq D E) ∧
          (∀ E ∈ Cs, ∃ D ∈ Cs', CfgEq D E) ∧
          (Reference.insts P Cs' tr').map instRec = (Reference.insts P Cs tr).map instRec := by
  intro C₀ C tr Cs h₀ hrun hb
  induction tr generalizing C₀ C Cs with
  | nil =>
      have hcs : Cs = [C] := runs_nil_inv hrun
      subst hcs
      refine ⟨[], [C₀], Reference.runs_nil P C₀, prunedWalk_nil P B C₀, by simp, ?_, ?_,
        by simp [Reference.insts]⟩
      · intro D hD
        rw [List.mem_singleton] at hD
        subst hD
        exact ⟨C, List.Mem.head _, h₀⟩
      · intro E hE
        rw [List.mem_singleton] at hE
        subst hE
        exact ⟨C₀, List.Mem.head _, h₀⟩
  | cons e rest ih =>
      rcases hstep : Reference.stepOf P C e with _ | C'
      · have h2 : Reference.run P C (e :: rest) = none := by
          rw [Reference.run, hstep]
        have h3 : Reference.run P C (e :: rest) = some Cs := hrun
        exact absurd (h2.symm.trans h3) (by simp)
      · obtain ⟨Rest, hcs, hRest⟩ := run_cons hstep hrun
        subst hcs
        have hRestB : ∀ D ∈ Rest, inBounds P B D := fun D hD => hb D (List.Mem.tail _ hD)
        have hC' : inBounds P B C' := hRestB C' (runs_head_mem hRest)
        by_cases hidle : e = Reference.Ev.idle
        · -- an idle step: drop it, the configuration does not change at all
          subst hidle
          have hsym : C = C' := by
            have hsid : Reference.stepOf P C Reference.Ev.idle = some C' := hstep
            simpa [Reference.stepOf] using hsid
          subst hsym
          obtain ⟨tr', Cs', hrun', hw, hlen, cov1, cov2, hrec⟩ := ih h₀ hRest hRestB
          refine ⟨tr', Cs', hrun', hw, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
          · intro D hD
            obtain ⟨E, hE, hde⟩ := cov1 D hD
            exact ⟨E, List.Mem.tail _ hE, hde⟩
          · intro E hE
            rw [List.mem_cons] at hE
            obtain h1 | h2 := hE
            · subst h1
              exact ⟨C₀, runs_head_mem hrun', h₀⟩
            · obtain ⟨D, hD, hde⟩ := cov2 E h2
              exact ⟨D, hD, hde⟩
          · rw [insts_records_cons, hrec]
            simp [instRecAt]
        · by_cases hded : ∃ t, e = Reference.Ev.ded t
          · -- a deduction: drop it when the message is already known, keep it otherwise
            obtain ⟨t, rfl⟩ := hded
            have hb1 : oneStepBool C.kn t = true := by
              by_cases h : oneStepBool C.kn t = true
              · exact h
              · have hnone : Reference.stepOf P C (Reference.Ev.ded t) = none := by
                  simp [Reference.stepOf, h]
                rw [hnone] at hstep
                cases hstep
            have hc' : C' = Reference.publish C t := by
              have hpub : Reference.stepOf P C (Reference.Ev.ded t) =
                  some (Reference.publish C t) := by simp [Reference.stepOf, hb1]
              exact (Option.some.inj (hpub.symm.trans hstep)).symm
            subst hc'
            by_cases hin : t ∈ C.kn
            · obtain ⟨tr', Cs', hrun', hw, hlen, cov1, cov2, hrec⟩ :=
                ih (cfgEq_trans h₀ (cfgEq_publish_self hin)) hRest hRestB
              refine ⟨tr', Cs', hrun', hw, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
              · intro D hD
                obtain ⟨E, hE, hde⟩ := cov1 D hD
                exact ⟨E, List.Mem.tail _ hE, hde⟩
              · intro E hE
                rw [List.mem_cons] at hE
                obtain h1 | h2 := hE
                · subst h1
                  exact ⟨C₀, runs_head_mem hrun', h₀⟩
                · obtain ⟨D, hD, hde⟩ := cov2 E h2
                  exact ⟨D, hD, hde⟩
              · rw [insts_records_cons, hrec]
                simp [instRecAt]
            · -- a genuine deduction: the message is new at C₀ too, since C₀ knows what C knows
              have h₀kn : t ∉ C₀.kn := fun h => hin ((h₀.2.2.2 t).mp h)
              have hb0 : oneStepBool C₀.kn t = true :=
                (oneStepBool_congr h₀.2.2.2 t).trans hb1
              have hstep₀ : Reference.stepOf P C₀ (Reference.Ev.ded t) =
                  some (Reference.publish C₀ t) := by simp [Reference.stepOf, hb0]
              have hC₀ : inBounds P B C₀ := (inBounds_congr h₀).mpr (hb C (List.Mem.head _))
              have hC₀' : inBounds P B (Reference.publish C₀ t) :=
                (inBounds_congr (cfgEq_publish h₀ t)).mpr hC'
              have hstepB₀ : stepB P B C₀ (Reference.Ev.ded t) =
                  some (Reference.publish C₀ t) := stepB_of hstep₀ hC₀'
              have hmem : Reference.Ev.ded t ∈ candidatesP P B C₀ :=
                candidatesP_of_rel (by exact hstep₀) hC₀ hC₀'
                  (by simp) (fun t' ht' => by
                    have h2 : t = t' := Reference.Ev.ded.inj ht'
                    subst h2
                    exact h₀kn)
              obtain ⟨tr', Cs', hrun', hw, hlen, cov1, cov2, hrec⟩ :=
                ih (cfgEq_publish h₀ t) hRest hRestB
              refine ⟨Reference.Ev.ded t :: tr', C₀ :: Cs',
                Reference.runs_cons (by exact hstep₀) hrun',
                prunedWalk_cons hstepB₀ hmem hw, Nat.succ_le_succ hlen, ?_, ?_, ?_⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C, List.Mem.head _, h₀⟩
                · obtain ⟨E, hE, hde⟩ := cov1 D h2
                  exact ⟨E, List.Mem.tail _ hE, hde⟩
              · intro E hE
                rw [List.mem_cons] at hE
                obtain h1 | h2 := hE
                · subst h1
                  exact ⟨C₀, List.Mem.head _, h₀⟩
                · obtain ⟨D, hD, hde⟩ := cov2 E h2
                  exact ⟨D, List.Mem.tail _ hD, hde⟩
              · rw [insts_records_cons, insts_records_cons, hrec]
                simp [instRecAt]
          · -- a session event: always offered, and its step transports along CfgEq
            obtain ⟨C₀', hstep₀, hcv⟩ := stepOf_pres (cfgEq_symm h₀) hstep
            have hC₀ : inBounds P B C₀ := (inBounds_congr h₀).mpr (hb C (List.Mem.head _))
            have hC₀' : inBounds P B C₀' := (inBounds_congr (cfgEq_symm hcv)).mpr hC'
            have hstepB₀ : stepB P B C₀ e = some C₀' := stepB_of hstep₀ hC₀'
            have hmem : e ∈ candidatesP P B C₀ :=
              candidatesP_of_rel (by exact hstep₀) hC₀ hC₀' hidle
                (by intro t' ht'; exact absurd ⟨t', ht'⟩ hded)
            obtain ⟨tr', Cs', hrun', hw, hlen, cov1, cov2, hrec⟩ :=
              ih (cfgEq_symm hcv) hRest hRestB
            refine ⟨e :: tr', C₀ :: Cs', Reference.runs_cons (by exact hstep₀) hrun',
              prunedWalk_cons hstepB₀ hmem hw, Nat.succ_le_succ hlen, ?_, ?_, ?_⟩
            · intro D hD
              rw [List.mem_cons] at hD
              obtain h1 | h2 := hD
              · subst h1
                exact ⟨C, List.Mem.head _, h₀⟩
              · obtain ⟨E, hE, hde⟩ := cov1 D h2
                exact ⟨E, List.Mem.tail _ hE, hde⟩
            · intro E hE
              rw [List.mem_cons] at hE
              obtain h1 | h2 := hE
              · subst h1
                exact ⟨C₀, List.Mem.head _, h₀⟩
              · obtain ⟨D, hD, hde⟩ := cov2 E h2
                exact ⟨D, List.Mem.tail _ hD, hde⟩
            · rw [insts_records_cons, insts_records_cons, hrec, instRecAt_congr h₀ (some e)]

/-- **The pruned frontier enumerates the pruned runs.** Compare `Explore.frontier_complete`: the
step that there uses `candidates_complete` to recover the event from the step relation is already
carried by `prunedWalk` here, so this induction is shorter than the one it mirrors. -/
theorem frontierP_of_prunedWalk {P : Protocol} {B : Bounds} :
    ∀ {x : Node}, isPrefix P B x -> ∀ {Cs : List Reference.Cfg},
      ∀ {tr : List Reference.Ev},
        Reference.Runs P x.cfg tr (x.cfg :: Cs) -> prunedWalk P B x.cfg tr ->
          ∃ y ∈ frontierP P B tr.length x, y.tr = x.tr ++ tr ∧ y.Cs = x.Cs ++ Cs := by
  intro x hx Cs tr hrun hw
  induction tr generalizing x Cs with
  | nil =>
      have hcs : Cs = [] := (List.cons.inj (runs_nil_inv hrun)).2
      subst hcs
      refine ⟨x, by simp, by simp, by simp⟩
  | cons e rest ih =>
      obtain ⟨C', hstepB, hmem, hrest⟩ := hw
      obtain ⟨Rest, hcs, hRest⟩ := run_cons (step_of_stepB hstepB) hrun
      have heq : Cs = Rest := (List.cons.inj hcs).2
      subst heq
      obtain ⟨l, hl⟩ := run_nonempty hRest
      subst hl
      set z : Node := { cfg := C', tr := x.tr ++ [e], Cs := x.Cs ++ [C'] } with hz
      have hzpre : isPrefix P B z :=
        isPrefix_of_extend hx (candidatesP_subset_candidates hmem) hstepB rfl rfl rfl
      have hzmem : z ∈ extendP P B x := by
        rw [mem_extendP_iff]
        exact ⟨e, C', hmem, hstepB, rfl, rfl, rfl⟩
      obtain ⟨y, hy, h1, h2⟩ := ih hzpre hRest hrest
      refine ⟨y, mem_frontierP_extend hzmem hy, ?_, ?_⟩
      · rw [h1]
        simp [List.append_assoc, hz]
      · rw [h2]
        simp [List.append_assoc, hz]
/-! ### Moving the verdict across the compression -/

/-- The executable violation test of the explorer agrees with the declarative one. -/
theorem nodeViolates_iff {P : Protocol} {x : Node} :
    nodeViolates P x = true <-> violates P x.Cs x.tr := by
  classical
  unfold nodeViolates violates authBreak
  rw [Bool.or_eq_true]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with hleak | hbreak
    · left
      exact (traceLeaksBool_iff P x.Cs).mp hleak
    · right
      intro hall
      have h2 := (agreesBool_iff (insts P x.Cs x.tr)).mpr hall
      simp [h2] at hbreak
  · rcases h with hleak | hbreak
    · left
      exact (traceLeaksBool_iff P x.Cs).mpr hleak
    · right
      have hfalse : agreesBool (insts P x.Cs x.tr) = false := by
        rw [Bool.eq_false_iff]
        intro hall
        exact hbreak ((agreesBool_iff (insts P x.Cs x.tr)).mp hall)
      simp [hfalse]

/-- **Non-injective agreement is a property of the record sequence, not of the positions**: two
configuration lists whose authentication records are the same sequence agree or fail together. This
is `Compress.agrees_renumber` applied to a record equality, not a new argument. -/
theorem agrees_congr_records {P : Protocol} {Cs Cs' : List Reference.Cfg}
    {tr tr' : List Reference.Ev}
    (hrec : (insts P Cs' tr').map instRec = (insts P Cs tr).map instRec) :
    agrees (insts P Cs' tr') <-> agrees (insts P Cs tr) :=
  agrees_renumber ⟨hrec, incIdx_insts P Cs' tr', incIdx_insts P Cs tr⟩

/-- The injective counterpart, via `Compress.agreesInj_renumber`. -/
theorem agreesInj_congr_records {P : Protocol} {Cs Cs' : List Reference.Cfg}
    {tr tr' : List Reference.Ev}
    (hrec : (insts P Cs' tr').map instRec = (insts P Cs tr).map instRec) :
    agreesInj (insts P Cs' tr') <-> agreesInj (insts P Cs tr) :=
  agreesInj_renumber ⟨hrec, incIdx_insts P Cs' tr', incIdx_insts P Cs tr⟩

/-- **Leaking is invariant under a `CfgEq` correspondence between two visited lists.** -/
theorem traceLeaks_congr {P : Protocol} {Cs Cs' : List Reference.Cfg}
    (cov1 : ∀ D ∈ Cs', ∃ E ∈ Cs, CfgEq D E)
    (cov2 : ∀ E ∈ Cs, ∃ D ∈ Cs', CfgEq D E) :
    traceLeaks P Cs' <-> traceLeaks P Cs := by
  refine ⟨?_, ?_⟩
  · rintro ⟨D, hD, s, hs, hk⟩
    obtain ⟨E, hE, hde⟩ := cov1 D hD
    exact ⟨E, hE, (leaks_congr hde).mp ⟨s, hs, hk⟩⟩
  · rintro ⟨E, hE, s, hs, hk⟩
    obtain ⟨D, hD, hde⟩ := cov2 E hE
    exact ⟨D, hD, (leaks_congr hde).mpr ⟨s, hs, hk⟩⟩

/-- **The explorer's violation is invariant under the compression.** -/
theorem violates_congr {P : Protocol} {Cs Cs' : List Reference.Cfg}
    {tr tr' : List Reference.Ev}
    (cov1 : ∀ D ∈ Cs', ∃ E ∈ Cs, CfgEq D E)
    (cov2 : ∀ E ∈ Cs, ∃ D ∈ Cs', CfgEq D E)
    (hrec : (insts P Cs' tr').map instRec = (insts P Cs tr).map instRec) :
    violates P Cs' tr' <-> violates P Cs tr := by
  classical
  unfold violates authBreak
  refine ⟨?_, ?_⟩
  · rintro (hleak | hbreak)
    · left
      exact (traceLeaks_congr cov1 cov2).mp hleak
    · right
      intro hall
      exact hbreak (agrees_congr_records hrec |>.mpr hall)
  · rintro (hleak | hbreak)
    · left
      exact (traceLeaks_congr cov1 cov2).mpr hleak
    · right
      intro hall
      exact hbreak (agrees_congr_records hrec |>.mp hall)

/-- **Every selected goal is invariant under the compression** - the statement `goalViolation` is
`CfgEq`-invariant, which is what lets the pruned search answer the contract's question. -/
theorem goalViolation_congr {P : Protocol} {g : Goal} {Cs Cs' : List Reference.Cfg}
    {tr tr' : List Reference.Ev}
    (cov1 : ∀ D ∈ Cs', ∃ E ∈ Cs, CfgEq D E)
    (cov2 : ∀ E ∈ Cs, ∃ D ∈ Cs', CfgEq D E)
    (hrec : (insts P Cs' tr').map instRec = (insts P Cs tr).map instRec) :
    goalViolation P g Cs' tr' <-> goalViolation P g Cs tr := by
  classical
  cases g with
  | secrecy =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact (traceLeaks_congr cov1 cov2).mp h
      · exact (traceLeaks_congr cov1 cov2).mpr h
  | agreement =>
      unfold goalViolation authBreak
      refine ⟨fun h hall => h (agrees_congr_records hrec |>.mpr hall),
        fun h hall => h (agrees_congr_records hrec |>.mp hall)⟩
  | agreementInj =>
      unfold goalViolation authBreakInj
      refine ⟨fun h hall => h (agreesInj_congr_records hrec |>.mpr hall),
        fun h hall => h (agreesInj_congr_records hrec |>.mp hall)⟩

/-! ### The equivalence -/

/-- **Completeness of the pruned search**: an attack has a pruned witness. This is the direction
that costs something, and it is the content of the refinement. -/
theorem explorerAttack_imp_explorerAttackP {P : Protocol} {B : Bounds}
    (h : explorerAttack P B = true) : explorerAttackP P B = true := by
  classical
  rw [explorerAttack, List.any_eq_true] at h
  obtain ⟨x, hx, hv⟩ := h
  obtain ⟨hpre, hlen⟩ := prefix_of_mem_allNodes hx
  obtain ⟨tr', Cs', hrun', hw, hlen', cov1, cov2, hrec⟩ :=
    runs_prune (P := P) (B := B) (C₀ := Reference.initCfg P) (C := Reference.initCfg P)
      (tr := x.tr) (Cs := x.Cs) (cfgEq_refl (Reference.initCfg P)) hpre.1 hpre.2.1
  obtain ⟨tl, htl⟩ := run_nonempty hrun'
  subst htl
  obtain ⟨y, hy, h1, h2⟩ :=
    frontierP_of_prunedWalk (P := P) (B := B) (isPrefix_initNode P B) hrun' hw
  have h1' : y.tr = tr' := by simpa [initNode] using h1
  have h2' : y.Cs = Reference.initCfg P :: tl := by simpa [initNode] using h2
  rw [explorerAttackP, List.any_eq_true]
  refine ⟨y, ?_, ?_⟩
  · rw [allNodesP, List.mem_flatMap]
    exact ⟨tr'.length, List.mem_range.mpr (by omega), hy⟩
  · rw [nodeViolates_iff, h1', h2']
    rw [violates_congr cov1 cov2 hrec]
    exact (nodeViolates_iff (P := P) (x := x)).mp hv

/-- **The refinement is exact**: the pruned enumerator and the explorer give the same answer. -/
theorem explorerAttack_equiv (P : Protocol) (B : Bounds) :
    explorerAttack P B = explorerAttackP P B :=
  Bool.eq_iff_iff.mpr ⟨explorerAttack_imp_explorerAttackP, explorerAttackP_imp⟩

/-- **Completeness of the pruned search, per query.** -/
theorem attackFound_imp_attackFoundP {q : Query} (h : attackFound q = true) :
    attackFoundP q = true := by
  classical
  rw [attackFound, List.any_eq_true] at h
  obtain ⟨x, hx, hv⟩ := h
  obtain ⟨hpre, hlen⟩ := prefix_of_mem_allNodes hx
  rw [nodeViolatesQuery, List.any_eq_true] at hv
  obtain ⟨g, hg, hgv⟩ := hv
  rw [goalViolationBool_iff] at hgv
  obtain ⟨tr', Cs', hrun', hw, hlen', cov1, cov2, hrec⟩ :=
    runs_prune (P := q.protocol) (B := q.bounds) (C₀ := Reference.initCfg q.protocol)
      (C := Reference.initCfg q.protocol) (tr := x.tr) (Cs := x.Cs)
      (cfgEq_refl (Reference.initCfg q.protocol)) hpre.1 hpre.2.1
  obtain ⟨tl, htl⟩ := run_nonempty hrun'
  subst htl
  obtain ⟨y, hy, h1, h2⟩ :=
    frontierP_of_prunedWalk (P := q.protocol) (B := q.bounds)
      (isPrefix_initNode q.protocol q.bounds) hrun' hw
  have h1' : y.tr = tr' := by simpa [initNode] using h1
  have h2' : y.Cs = Reference.initCfg q.protocol :: tl := by simpa [initNode] using h2
  rw [attackFoundP, List.any_eq_true]
  refine ⟨y, ?_, ?_⟩
  · rw [allNodesP, List.mem_flatMap]
    exact ⟨tr'.length, List.mem_range.mpr (by omega), hy⟩
  · rw [nodeViolatesQuery, List.any_eq_true]
    refine ⟨g, hg, (goalViolationBool_iff q.protocol g y.Cs y.tr).mpr ?_⟩
    rw [h1', h2']
    exact (goalViolation_congr cov1 cov2 hrec).mpr hgv

/-- **The refinement is exact where the contract consumes it.** -/
theorem attackFound_equiv (q : Query) : attackFound q = attackFoundP q :=
  Bool.eq_iff_iff.mpr ⟨attackFound_imp_attackFoundP, attackFoundP_imp⟩

/-- The pruned enumerator decides the bounded question, with no hypothesis about an encoding, a
representability condition or a solver: it inherits `Explore.explorer_correct` through the
equivalence. -/
theorem explorerAttackP_correct (P : Protocol) (B : Bounds) :
    explorerAttackP P B = true <-> Reference.Explore.BoundedAttack P B := by
  rw [← explorerAttack_equiv]
  exact explorer_correct P B

/-- **Bounded safety by pruned exhaustion.** -/
theorem boundedSafe_of_explorerP (P : Protocol) (B : Bounds)
    (h : explorerAttackP P B = false) : Reference.Explore.BoundedSafe P B :=
  boundedSafe_of_explorer P B (by rw [explorerAttack_equiv]; exact h)

/-- **Bounded safety of a query by pruned exhaustion.** -/
theorem boundedSafe_of_attackFoundP_false {q : Query} (h : attackFoundP q = false) :
    boundedSafe q :=
  boundedSafe_of_attackFound_false (by rw [attackFound_equiv]; exact h)

/-! ### The derived bound, decided -/

/-- The derived bounds keep the query's closure rounds, so they keep its message universe. -/
theorem rounds_derived (q : Query) : (derived q).bounds.rounds = q.bounds.rounds := rfl

/-- **Being inside the bounds is monotone in the closure rounds.** -/
theorem inBounds_mono_rounds {P : Protocol} {B B' : Bounds} (h : B.rounds ≤ B'.rounds)
    {C : Reference.Cfg} (hb : inBounds P B C) : inBounds P B' C := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  exact ⟨fun t ht => univ_mono h t (h1 t ht), fun v hv => univ_mono h v (h2 v hv),
    fun s hs p hp => univ_mono h p.2 (h3 s hs p hp), h4⟩

/-- A configuration inside the query's own bounds is inside its derived bounds: the derived bounds
add events, never closure rounds, so they do not add messages. -/
theorem inBounds_derived {q : Query} {C : Reference.Cfg} (hb : inBounds q.protocol q.bounds C) :
    inBounds q.protocol (derived q).bounds C :=
  inBounds_mono_rounds (show q.bounds.rounds ≤ (derived q).bounds.rounds from Nat.le_refl _) hb

/-- **The derived bound as a decision, not a reduction.** `Compress.safe_at_derived_bound* shows
that a violation at any length has a witness inside the derived bound; `runs_prune` shows that
witness has a *pruned* witness of the same or smaller length; and the pruned witness is enumerated
by `frontierP`. So one `decide` on `attackFoundP` at the derived bounds settles
`Compress.allLengthsSafe` - safety for executions of every length inside the query's own message
universe, sessions and nonce domain. -/
theorem allLengthsSafe_of_attackFoundP_false (q : Query)
    (h : attackFoundP (derived q) = false) : allLengthsSafe q := by
  classical
  intro tr Cs hrun hb g hg' hv
  have key : ∃ (tr₁ : List Reference.Ev) (Cs₁ : List Reference.Cfg),
      Reference.Runs q.protocol (Reference.initCfg q.protocol) tr₁ Cs₁ ∧
        boundedCfgs q.protocol q.bounds Cs₁ ∧
          tr₁.length ≤ Compress.derivedSteps q ∧ goalViolation q.protocol g Cs₁ tr₁ := by
    cases g with
    | secrecy =>
        obtain ⟨t₁, C₁, h₁, h₂, h₃, h₄⟩ :=
          compress_secrecy (P := q.protocol) (B := q.bounds) hrun hb
            ((goalViolation_secrecy q.protocol Cs tr).mp hv)
        exact ⟨t₁, C₁, h₁, h₂, by show _; exact h₃,
          (goalViolation_secrecy _ _ _).mpr h₄⟩
    | agreement =>
        obtain ⟨t₁, C₁, h₁, h₂, h₃, h₄⟩ :=
          compress_agreement (P := q.protocol) (B := q.bounds) hrun hb
            ((goalViolation_agreement q.protocol Cs tr).mp hv)
        exact ⟨t₁, C₁, h₁, h₂, by show _; exact h₃,
          (goalViolation_agreement _ _ _).mpr h₄⟩
    | agreementInj =>
        obtain ⟨t₁, C₁, h₁, h₂, h₃, h₄⟩ :=
          compress_agreementInj (P := q.protocol) (B := q.bounds) hrun hb
            ((goalViolation_agreementInj q.protocol Cs tr).mp hv)
        exact ⟨t₁, C₁, h₁, h₂, by show _; exact h₃,
          (goalViolation_agreementInj _ _ _).mpr h₄⟩
  obtain ⟨tr₁, Cs₁, hrun₁, hb₁, hlen₁, hv₁⟩ := key
  obtain ⟨tr', Cs', hrun', hw, hlen', cov1, cov2, hrec⟩ :=
    runs_prune (P := q.protocol) (B := (derived q).bounds)
      (C₀ := Reference.initCfg q.protocol) (C := Reference.initCfg q.protocol)
      (tr := tr₁) (Cs := Cs₁) (cfgEq_refl (Reference.initCfg q.protocol)) hrun₁
      (fun D hD => inBounds_derived (hb₁ D hD))
  obtain ⟨tl, htl⟩ := run_nonempty hrun'
  subst htl
  obtain ⟨y, hy, h1, h2⟩ :=
    frontierP_of_prunedWalk (P := q.protocol) (B := (derived q).bounds)
      (isPrefix_initNode q.protocol (derived q).bounds) hrun' hw
  have h1' : y.tr = tr' := by simpa [initNode] using h1
  have h2' : y.Cs = Reference.initCfg q.protocol :: tl := by simpa [initNode] using h2
  have hsteps : tr'.length ≤ (derived q).bounds.steps :=
    Nat.le_trans hlen' (Nat.le_trans hlen₁
      (Nat.le_max_right q.bounds.steps (Compress.derivedSteps q)))
  have hcon : attackFoundP (derived q) = true := by
    rw [attackFoundP, List.any_eq_true]
    refine ⟨y, ?_, ?_⟩
    · rw [allNodesP, List.mem_flatMap]
      exact ⟨tr'.length, List.mem_range.mpr (by omega), hy⟩
    · rw [nodeViolatesQuery, List.any_eq_true]
      refine ⟨g, hg', (goalViolationBool_iff q.protocol g y.Cs y.tr).mpr ?_⟩
      rw [h1', h2']
      exact (goalViolation_congr cov1 cov2 hrec).mpr hv₁
  rw [h] at hcon
  exact Bool.noConfusion hcon

/-! ### Gates

Every declaration below is kernel-checked by @@decide@@: the pruned enumeration is evaluated by the
kernel, not trusted to the compiler. Each gate is stated next to the closed answer it is meant to
agree with, and the agreement is the equivalence above, not a second computation. -/

namespace Gates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- **The contract's secure gate, pruned.** Three nodes instead of 258, and the answer is the same
`false` that `Explore.Gates.secure_explorer_finds_nothing` records. -/
theorem secure_explorerP_finds_nothing :
    explorerAttackP Explore.Gates.secureP Explore.Gates.secureB = false := by decide

/-- The unpruned closed answer, recovered from the pruned one through the equivalence. -/
theorem secure_explorer_finds_nothing :
    explorerAttack Explore.Gates.secureP Explore.Gates.secureB = false := by
  rw [explorerAttack_equiv]
  exact secure_explorerP_finds_nothing

/-- **The attack the CNF loses, pruned**: the transient-pair model still breaks, and the pruned
search is the one that finds it. -/
theorem transient_pairP_attack_found :
    explorerAttackP ProtSat.ExprDomain.boundsP ProtSat.ExprDomain.boundsB = true := by decide

/-- The unpruned closed answer, recovered from the pruned one. -/
theorem transient_pair_attack_found :
    explorerAttack ProtSat.ExprDomain.boundsP ProtSat.ExprDomain.boundsB = true := by
  rw [explorerAttack_equiv]
  exact transient_pairP_attack_found

/-- **Authentication, pruned**: the unmatched commit is still found. The break this model exposes is
a session that never advances, and `runs_prune` is what justifies keeping it: deleting the idle
events from that execution leaves the same claims and commits in the same order, so the agreement
monitor sees the same break. -/
theorem auth_explorerP_finds_the_break :
    explorerAttackP Explore.Gates.authP Explore.Gates.authB = true := by decide

/-- The unpruned closed answer, recovered from the pruned one. -/
theorem auth_explorer_finds_the_break :
    explorerAttack Explore.Gates.authP Explore.Gates.authB = true := by
  rw [explorerAttack_equiv]
  exact auth_explorerP_finds_the_break

/-- **NSL at the exhaustion bound, pruned**: the same `false` as
`Benchmarks.NSL2cqE_attackFound_false`. -/
theorem NSL2cqE_attackFoundP_false : attackFoundP Benchmarks.NSL2cqE = false := by decide

/-- The unpruned closed answer, recovered from the pruned one. -/
theorem NSL2cqE_attackFound_false : attackFound Benchmarks.NSL2cqE = false := by
  rw [attackFound_equiv]
  exact NSL2cqE_attackFoundP_false

/-- **NS at the exhaustion bound, pruned**: the same `false` as
`Benchmarks.NS2cqE_attackFound_false`. -/
theorem NS2cqE_attackFoundP_false : attackFoundP Benchmarks.NS2cqE = false := by decide

/-- The unpruned closed answer, recovered from the pruned one. -/
theorem NS2cqE_attackFound_false : attackFound Benchmarks.NS2cqE = false := by
  rw [attackFound_equiv]
  exact NS2cqE_attackFoundP_false

/-- **The Lowe-shaped break, pruned**: the same `true` as
`Benchmarks.NSL2earlyQ_attackFound_true`. -/
theorem NSL2earlyQ_attackFoundP_true : attackFoundP Benchmarks.NSL2earlyQ = true := by decide

/-- The unpruned closed answer, recovered from the pruned one. -/
theorem NSL2earlyQ_attackFound_true : attackFound Benchmarks.NSL2earlyQ = true := by
  rw [attackFound_equiv]
  exact NSL2earlyQ_attackFoundP_true

/-- **The 258 nodes, kernel-counted.** The explorer's own enumeration of the secure model at the
bound the analyst wrote. -/
theorem secureQ_nodeCount_unpruned :
    (allNodes Explore.Gates.secureP Explore.Gates.secureB 3).length = 258 := by decide

/-- **The 3 nodes, kernel-counted.** The pruned enumeration of the same query at the same bound. -/
theorem secureQ_nodeCount_pruned :
    (allNodesP Explore.Gates.secureP Explore.Gates.secureB 3).length = 3 := by decide

/-- **The pruning does not stop at the analyst's bound.** At the sixteen events the model derives,
the pruned search still visits exactly three configuration lists: every event past the third is
either idle or a deduction of a message already held, and `runs_prune` shows nothing is lost by not
trying them. -/
theorem secureQ_derived_nodeCount :
    (allNodesP Compress.secureQ.protocol (Compress.derived Compress.secureQ).bounds
      (Compress.derived Compress.secureQ).bounds.steps).length = 3 := by decide

/-- **The prize.** The pruned enumerator answers the query at the bound `Compress` *derives* from
the model - sixteen events on this model, against the three the analyst wrote - and says `false`.
The unpruned search cannot reach this query: it is at 258 nodes after three events. -/
theorem secureQ_derived_attackFoundP_false :
    attackFoundP (Compress.derived Compress.secureQ) = false := by decide

/-- **A reduction becomes a decision.** `Compress.secureQ` is safe for executions of *every*
length inside its own message universe, sessions and nonce domain - proved by the kernel above, with
no analyst-chosen number anywhere in the statement it is applied to. -/
theorem secureQ_allLengthsSafe : allLengthsSafe Compress.secureQ :=
  allLengthsSafe_of_attackFoundP_false Compress.secureQ secureQ_derived_attackFoundP_false

/-- The same decision read as safety at the derived bound itself, which is the hypothesis
`Compress.safe_at_derived_bound` asks for. -/
theorem secureQ_derived_boundedSafe : boundedSafe (Compress.derived Compress.secureQ) :=
  boundedSafe_of_attackFoundP_false secureQ_derived_attackFoundP_false

end Gates

end ProtSat.Prune
