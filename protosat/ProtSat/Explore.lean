/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.ExprDomain
import ProtSat.Reference

/-!
# ProtSat: an exhaustive bounded explorer over the repaired semantics

## What this module buys

The SAT pipeline answers "is there a bounded execution that leaks a declared secret" and nothing
else, and its completeness is conditional on a representability hypothesis the public bounds do not
imply (`ProtSat.Regressions.Bounds`). Adding authentication to that formula means a new variable
family inside `Complete.lean`, whose block-range lemmas are all stated against `nVarsAll`.

The repaired semantics makes a cheaper route available. `ProtSat.Reference.stepOf` is a total
deterministic function, and once a message universe and a nonce domain are fixed the set of events
worth trying at any configuration is finite, so the executions can simply be **enumerated**. This
module defines

`@
explorerAttack P B = does some execution of at most B.steps events, every configuration of which
                     stays inside univ P B and P.nonceDomain, leak a declared secret or break
                     non-injective agreement?
`@

and proves the answer *is* the security statement:

`@lean
Explore.explorer_correct        : explorerAttack P B = true <-> BoundedAttack P B
Explore.boundedSafe_of_explorer : explorerAttack P B = false -> BoundedSafe P B
`@

Neither direction mentions an encoding, a representability condition, or a solver. Both goals
`ProtSat.Query` distinguishes are covered, because the violation test reads `Reference.traceLeaks`
and `Reference.agreesBool` rather than the CNF's leak literals.

## The bound is on configurations, not on intermediate values

`inBounds` constrains what a configuration *knows, stores, and has declared secret*. It says nothing
about the values an expression computes on the way. That is the whole difference exposed by
`Regressions.Bounds` - see `ProtSat.ExprDomain` for the domain construction that makes it precise.
The CNF loses that attack; the explorer keeps it.

## Cost

Exponential: one branch per candidate event per step, no state merging (merging by configuration would
need further argument, because the violation predicates read the whole trace). This is a *reference*
decision procedure for small bounds and small universes - the role `ProtSat.DPLL` plays for the CNF,
and the independent oracle roadmap stage 6 asks for.
-/

namespace ProtSat.Reference.Explore

open ProtSat Term Protocol Bounded

/-! ### The public bound -/

/-- The executable form of "this configuration is inside the bounds". -/
def inBoundsBool (P : Protocol) (B : Bounds) (C : Cfg) : Bool :=
  (C.kn.all (fun t => t ∈ univ P B)) && (C.oblig.all (fun v => v ∈ univ P B)) &&
    (C.sess.all (fun s => s.store.all (fun p => p.2 ∈ univ P B))) &&
    (C.alloc.all (fun n => n ∈ P.nonceDomain))

/-- **The public bounded-execution predicate**: one condition over the reference semantics, from which
every compiler representability condition should be derived rather than added beside it. -/
def inBounds (P : Protocol) (B : Bounds) (C : Cfg) : Prop :=
  (∀ t ∈ C.kn, t ∈ univ P B) ∧ (∀ v ∈ C.oblig, v ∈ univ P B) ∧
    (∀ s ∈ C.sess, ∀ p ∈ s.store, p.2 ∈ univ P B) ∧ (∀ n ∈ C.alloc, n ∈ P.nonceDomain)

theorem inBoundsBool_iff {P : Protocol} {B : Bounds} {C : Cfg} :
    inBoundsBool P B C = true <-> inBounds P B C := by
  classical
  simp only [inBoundsBool, inBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  tauto

/-- Every configuration of a visited list is inside the bounds. -/
def boundedCfgs (P : Protocol) (B : Bounds) (Cs : List Cfg) : Prop :=
  ∀ C ∈ Cs, inBounds P B C

/-- **A bounded execution of the repaired semantics.** -/
def BoundedRun (P : Protocol) (B : Bounds) (tr : List Ev) (Cs : List Cfg) : Prop :=
  Runs P (initCfg P) tr Cs ∧ tr.length ≤ B.steps ∧ boundedCfgs P B Cs

/-- The violation a query cares about. -/
def violates (P : Protocol) (Cs : List Cfg) (tr : List Ev) : Prop :=
  traceLeaks P Cs ∨ authBreak P Cs tr

/-- **Bounded attack**: some permitted execution violates a property. -/
def BoundedAttack (P : Protocol) (B : Bounds) : Prop :=
  ∃ tr Cs, BoundedRun P B tr Cs ∧ violates P Cs tr

/-- **Bounded safety**: what a SAFE verdict is supposed to mean. -/
def BoundedSafe (P : Protocol) (B : Bounds) : Prop := ¬ BoundedAttack P B

/-- The seeds contain the initial knowledge and the declared secrets, and nothing is allocated or
stored at the start. -/
theorem inBounds_initCfg (P : Protocol) (B : Bounds) : inBounds P B (initCfg P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact Bounded.initKn_subset_univ P B t ht
  · intro v hv
    exact absurd hv (by simp [initCfg])
  · intro s hs p hp
    rw [initCfg] at hs
    obtain ⟨se, hse, hseq⟩ := List.mem_map.mp hs
    subst hseq
    exact absurd hp (by simp [initCfg])
  · intro n hn
    exact absurd hn (by simp [initCfg])

/-! ### The event enumeration -/

/-- The events worth trying at a configuration. -/
def sessionEvents (P : Protocol) (B : Bounds) (q : Nat) : List Ev :=
  (univ P B).map (Ev.recv q) ++ (P.nonceDomain.map (Ev.generate q)) ++ [Ev.act q]

def candidates (P : Protocol) (B : Bounds) (C : Cfg) : List Ev :=
  Ev.idle :: (univ P B).map Ev.ded ++
    (List.range P.sessions.length).flatMap (sessionEvents P B)

theorem mem_candidates_idle {P : Protocol} {B : Bounds} {C : Cfg} :
    Ev.idle ∈ candidates P B C := by simp [candidates]

theorem mem_candidates_ded {P : Protocol} {B : Bounds} {C : Cfg} {t : Term}
    (h : t ∈ univ P B) : Ev.ded t ∈ candidates P B C := by
  simp [candidates, h]

theorem mem_candidates_recv {P : Protocol} {B : Bounds} {C : Cfg} {q : Nat} {m : Term}
    (hq : q < P.sessions.length) (h : m ∈ univ P B) : Ev.recv q m ∈ candidates P B C := by
  simp [candidates, sessionEvents, hq, h]

theorem mem_candidates_generate {P : Protocol} {B : Bounds} {C : Cfg} {q : Nat} {n : NonceName}
    (hq : q < P.sessions.length) (h : n ∈ P.nonceDomain) : Ev.generate q n ∈ candidates P B C := by
  simp [candidates, sessionEvents, hq, h]

theorem mem_candidates_act {P : Protocol} {B : Bounds} {C : Cfg} {q : Nat}
    (hq : q < P.sessions.length) : Ev.act q ∈ candidates P B C := by
  simp [candidates, sessionEvents, hq]

/-- A session that acts is a session the model instantiates. -/
theorem lt_sessions_of_actionAt {P : Protocol} {q c : Nat} {act : Action}
    (h : P.actionAt q c = some act) : q < P.sessions.length := by
  by_contra hq
  have hdrop : P.sessions.drop q = [] := List.drop_eq_nil_of_le (by omega)
  have h1 : P.actionAt q c = none := by
    unfold Protocol.actionAt Protocol.roleAt
    rw [hdrop]
    simp
  rw [h1] at h
  exact absurd h (by simp)

/-- **The enumeration offers every bounded step.** -/
theorem candidates_complete {P : Protocol} {B : Bounds} {C C' : Cfg} {e : Ev}
    (hstep : Rel P C e C') (hC : inBounds P B C) (hC' : inBounds P B C') :
    e ∈ candidates P B C := by
  unfold Rel at hstep
  cases e
  · exact mem_candidates_idle
  · rename_i t
    by_cases hb : oneStepBool C.kn t
    · rw [stepOf, if_pos hb] at hstep
      have := Option.some.inj hstep
      subst this
      exact mem_candidates_ded (hC'.1 t (List.mem_append.mpr (Or.inr (List.Mem.head _))))
    · rw [stepOf, if_neg hb] at hstep
      cases hstep
  · rename_i q m
    rw [stepOf] at hstep
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at hstep
    | some act =>
        cases act with
        | recv _ x =>
            by_cases hm : m ∈ C.kn
            · simp [hact, hm] at hstep
              subst hstep
              exact mem_candidates_recv (lt_sessions_of_actionAt hact) (hC.1 m hm)
            · simp [hact, hm] at hstep
        | _ => simp [hact] at hstep
  · rename_i q n
    rw [stepOf] at hstep
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at hstep
    | some act =>
        cases act with
        | fresh _ _ =>
            simp [hact] at hstep
            rcases hstep with ⟨hdom, _, rfl⟩
            exact mem_candidates_generate (lt_sessions_of_actionAt hact) hdom
        | _ => simp [hact] at hstep
  · rename_i q
    rw [stepOf] at hstep
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at hstep
    | some act => exact mem_candidates_act (lt_sessions_of_actionAt hact)

/-- **The bounded step**: the semantics' step, restricted to successors inside the bounds. -/
def stepB (P : Protocol) (B : Bounds) (C : Cfg) (e : Ev) : Option Cfg :=
  (stepOf P C e).filter (inBoundsBool P B)

theorem step_of_stepB {P : Protocol} {B : Bounds} {C C' : Cfg} {e : Ev}
    (h : stepB P B C e = some C') : stepOf P C e = some C' :=
  (Option.filter_eq_some_iff.mp h).1

theorem inBounds_of_stepB {P : Protocol} {B : Bounds} {C C' : Cfg} {e : Ev}
    (h : stepB P B C e = some C') : inBounds P B C' :=
  inBoundsBool_iff.mp ((Option.filter_eq_some_iff.mp h).2)

theorem stepB_of {P : Protocol} {B : Bounds} {C C' : Cfg} {e : Ev}
    (hstep : stepOf P C e = some C') (hb : inBounds P B C') : stepB P B C e = some C' := by
  unfold stepB
  rw [hstep, Option.filter_eq_some_iff]
  exact ⟨rfl, inBoundsBool_iff.mpr hb⟩

/-! ### Nodes -/

/-- One point of the search: the current configuration, the events so far, and the configurations
visited. -/
structure Node where
  cfg : Cfg
  tr : List Ev
  Cs : List Cfg

/-- The start of the search. -/
def initNode (P : Protocol) : Node :=
  { cfg := initCfg P, tr := [], Cs := [initCfg P] }

/-- The last element of a nonempty list, in the defaulting formulation. -/
theorem lastD_mem {α : Type} (d : α) : ∀ (l : List α), l ≠ [] → l.getLastD d ∈ l := by
  intro l
  induction l with
  | nil =>
      intro hne
      exact absurd rfl hne
  | cons a as ih =>
      cases as with
      | nil => intro _; simp [List.getLastD]
      | cons x xs =>
          intro hne
          simpa [List.getLastD, List.getLast_cons] using (lastD_mem d (x :: xs) (by simp))

/-- Appending a singleton makes that element the last one. -/
theorem lastD_snoc {α : Type} (d : α) : ∀ (l : List α) (x : α), l ≠ [] → (l ++ [x]).getLastD d = x
  | [], _, hz => absurd rfl hz
  | a :: as, x, _ => by
      cases as with
      | nil => simpa [List.getLastD, List.append]
      | cons y ys =>
          simpa [List.getLastD, List.getLast_cons, List.append_assoc] using
            (lastD_snoc d (y :: ys) x (by simp))

/-- Appending one enabled event to a run appends its successor to the visited list. -/
theorem run_snoc {P : Protocol} {C : Cfg} {tr : List Ev} {Cs : List Cfg} {e : Ev} {C' : Cfg}
    (h : run P C tr = some Cs) (hstep : stepOf P (Cs.getLastD C) e = some C') :
    run P C (tr ++ [e]) = some (Cs ++ [C']) := by
  induction tr generalizing C Cs with
  | nil =>
      have h2 : run P C [] = some [C] := rfl
      rw [h2] at h
      have hcs : Cs = [C] := (Option.some.inj h).symm
      subst hcs
      have hstep' : stepOf P C e = some C' := by simpa [List.getLast_cons] using hstep
      simp [run, hstep']
  | cons a rest ih =>
      rcases hstep2 : stepOf P C a with _ | C''
      · simp only [run, hstep2] at h
        cases h
      · rcases hr : run P C'' rest with _ | Cs'
        · simp only [run, hstep2, hr] at h
          cases h
        · simp only [run, hstep2, hr] at h
          have hcs : Cs = C :: Cs' := (Option.some.inj h).symm
          subst hcs
          have hlen : Cs'.length = rest.length + 1 := run_length P rest C'' Cs' hr
          have hne : Cs' ≠ [] := by
            intro hz
            rw [hz, List.length_nil] at hlen
            omega
          have hlast : (C :: Cs').getLastD C = Cs'.getLastD C'' := by
            cases Cs' with
            | nil => exact absurd rfl hne
            | cons x xs => simp [List.getLastD]
          have hsub : stepOf P (Cs'.getLastD C'') e = some C' := by
            rw [← hlast]
            exact hstep
          have h1 : run P C'' (rest ++ [e]) = some (Cs' ++ [C']) := ih hr hsub
          show run P C (a :: rest ++ [e]) = some (C :: Cs' ++ [C'])
          simp only [List.cons_append, run, hstep2, h1]
          rfl

/-- **The prefix invariant**: a bounded execution from the initial configuration whose visited list
ends at its current configuration. -/
def isPrefix (P : Protocol) (B : Bounds) (x : Node) : Prop :=
  Runs P (initCfg P) x.tr x.Cs ∧ boundedCfgs P B x.Cs ∧
    x.Cs.getLastD (initCfg P) = x.cfg ∧ x.Cs.length = x.tr.length + 1

theorem isPrefix_initNode (P : Protocol) (B : Bounds) : isPrefix P B (initNode P) :=
  ⟨runs_nil P (initCfg P),
    fun C hC => by
      rw [initNode, List.mem_singleton] at hC
      subst hC
      exact inBounds_initCfg P B,
    by simp [initNode, List.getLast], rfl⟩

/-- One bounded step of a prefix node is again a prefix node. -/
theorem isPrefix_of_extend {P : Protocol} {B : Bounds} {x y : Node} {e : Ev} {C' : Cfg}
    (hx : isPrefix P B x) (he : e ∈ candidates P B x.cfg)
    (hstep : stepB P B x.cfg e = some C')
    (htr : y.tr = x.tr ++ [e]) (hCs : y.Cs = x.Cs ++ [C']) (hcfg : y.cfg = C') : isPrefix P B y := by
  obtain ⟨hrun, hb, hlast, hlen⟩ := hx
  have hne : x.Cs ≠ [] := by
    intro hz
    rw [hz, List.length_nil] at hlen
    omega
  have hC : inBounds P B x.cfg :=
    hb x.cfg (by rw [← hlast]; exact lastD_mem (initCfg P) x.Cs hne)
  have hstep' : stepOf P x.cfg e = some C' := step_of_stepB hstep
  have hstep'' : stepOf P (x.Cs.getLastD (initCfg P)) e = some C' := by rw [hlast]; exact hstep'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Runs at *
    rw [htr, hCs, run_snoc hrun hstep'']
  · intro z hz
    rw [hCs, List.mem_append] at hz
    rcases hz with hz | hz
    · exact hb z hz
    · rw [List.mem_singleton] at hz
      subst hz
      exact inBounds_of_stepB hstep
  · rw [hCs, hcfg]
    exact lastD_snoc (initCfg P) x.Cs C' hne
  · rw [htr, hCs]
    simp only [List.length_append, List.length_singleton]
    omega

/-- The one-step extension of a node. -/
def extend (P : Protocol) (B : Bounds) (x : Node) : List Node :=
  (candidates P B x.cfg).flatMap fun e =>
    match stepB P B x.cfg e with
    | none => []
    | some C' => [{ cfg := C', tr := x.tr ++ [e], Cs := x.Cs ++ [C'] }]

/-- Membership in `extend` is exactly a bounded step. -/
theorem mem_extend_iff {P : Protocol} {B : Bounds} {x y : Node} :
    y ∈ extend P B x <->
      ∃ e C', e ∈ candidates P B x.cfg ∧ stepB P B x.cfg e = some C' ∧
        y.cfg = C' ∧ y.tr = x.tr ++ [e] ∧ y.Cs = x.Cs ++ [C'] := by
  unfold extend
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

/-- **The frontier**: nodes reachable in exactly `k` bounded steps. -/
def frontier : (P : Protocol) -> (B : Bounds) -> Nat -> Node -> List Node
  | _, _, 0, x => [x]
  | P, B, k + 1, x => (extend P B x).flatMap (frontier P B k)

@[simp] theorem frontier_zero (P : Protocol) (B : Bounds) (x : Node) : frontier P B 0 x = [x] := rfl

/-- Extending a frontier member is a frontier member one step out. -/
theorem mem_frontier_extend {P : Protocol} {B : Bounds} {k : Nat} {x y z : Node}
    (hy : y ∈ extend P B x) (hz : z ∈ frontier P B k y) : z ∈ frontier P B (k + 1) x :=
  List.mem_flatMap.mpr ⟨y, hy, hz⟩

/-- Every node on the frontier is a prefix, extended by exactly `k` events. -/
theorem isPrefix_of_mem_frontier {P : Protocol} {B : Bounds} {k : Nat} {x y : Node}
    (hx : isPrefix P B x) (h : y ∈ frontier P B k x) :
    isPrefix P B y ∧ y.tr.length = x.tr.length + k := by
  induction k generalizing x y with
  | zero =>
      have : y = x := by simpa using h
      subst this
      exact ⟨hx, rfl⟩
  | succ k ih =>
      rw [frontier, List.mem_flatMap] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨e, C', he, hstep, hcfg, htr, hCs⟩ := (mem_extend_iff).mp hz
      have hzpre : isPrefix P B z := isPrefix_of_extend hx he hstep htr hCs hcfg
      obtain ⟨hy', hlen⟩ := ih hzpre hy
      exact ⟨hy', by rw [hlen, htr]; simp only [List.length_append, List.length_singleton]; omega⟩

/-- **Run decomposition.** A nonempty run visits a list starting with its own start configuration,
and the tail of the trace runs from the successor. -/
theorem run_cons {P : Protocol} {C : Cfg} {e : Ev} {C' : Cfg} {tr : List Ev} {Cs : List Cfg}
    (hstep : stepOf P C e = some C') (h : run P C (e :: tr) = some Cs) :
    ∃ D, Cs = C :: D ∧ run P C' tr = some D := by
  rw [run, hstep] at h
  obtain ⟨D, hD, hcs⟩ := Option.map_eq_some_iff.mp h
  exact ⟨D, by simpa using hcs.symm, hD⟩

/-- The visited list of a run is nonempty. -/
theorem run_nonempty {P : Protocol} {C : Cfg} {tr : List Ev} {Cs : List Cfg}
    (h : run P C tr = some Cs) : ∃ l, Cs = C :: l := by
  cases tr with
  | nil =>
      have h2 : run P C [] = some [C] := rfl
      rw [h2] at h
      exact ⟨[], (Option.some.inj h).symm⟩
  | cons e rest =>
      rcases hstep : stepOf P C e with _ | C'
      · rw [run, hstep] at h
        cases h
      · obtain ⟨D, hcs, _⟩ := run_cons hstep h
        exact ⟨D, hcs⟩

/-- Dropping the first element of a list with at least two elements does not change its last element,
whatever the default. -/
theorem lastD_drop_head {α : Type} (a b : α) (l : List α) (d d' : α) :
    (a :: b :: l).getLastD d = (b :: l).getLastD d' := by
  cases l with
  | nil => simp [List.getLastD, List.getLast_cons]
  | cons x xs => simp [List.getLastD, List.getLast_cons]

/-- **Completeness of the frontier.** Every bounded extension of a prefix node appears on the
frontier after exactly as many steps as the extending trace has events. -/
theorem frontier_complete {P : Protocol} {B : Bounds} :
    ∀ {x : Node}, isPrefix P B x -> ∀ {tr : List Ev} {Cs : List Cfg},
      Runs P x.cfg tr (x.cfg :: Cs) ->
        (∀ C' ∈ Cs, inBounds P B C') ->
          ∃ y ∈ frontier P B tr.length x,
            y.tr = x.tr ++ tr ∧ y.Cs = x.Cs ++ Cs ∧
              y.cfg = (x.cfg :: Cs).getLastD x.cfg := by
  intro x hx tr
  induction tr generalizing x with
  | nil =>
      intro Cs hrun hb
      have h2 : run P x.cfg [] = some (x.cfg :: Cs) := hrun
      have h3 : run P x.cfg [] = some [x.cfg] := rfl
      rw [h3] at h2
      have hnil : Cs = [] := ((List.cons.inj (Option.some.inj h2)).2).symm
      refine ⟨x, by simp [frontier], by simp [hnil], by simp [hnil], by simp [hnil]⟩
  | cons e rest ih =>
      intro Cs hrun hb
      unfold Runs at hrun
      rcases hstep : stepOf P x.cfg e with _ | C'
      · rw [run, hstep] at hrun
        cases hrun
      · obtain ⟨D, hcs, hsub⟩ := run_cons hstep hrun
        have hCsD : Cs = D := (List.cons.inj hcs).2
        subst hCsD
        obtain ⟨l, hD⟩ := run_nonempty hsub
        subst hD
        have hC'lb : inBounds P B C' := hb C' (List.Mem.head _)
        have hxlb : inBounds P B x.cfg := by
          obtain ⟨_, hb', hlast, hlen⟩ := hx
          have hne : x.Cs ≠ [] := by
            intro hz
            rw [hz, List.length_nil] at hlen
            omega
          exact hb' x.cfg (by rw [← hlast]; exact lastD_mem (initCfg P) x.Cs hne)
        have hmem : e ∈ candidates P B x.cfg :=
          candidates_complete (by exact hstep) hxlb hC'lb
        have hstepB : stepB P B x.cfg e = some C' := stepB_of hstep hC'lb
        have hzpre : isPrefix P B
            { cfg := C', tr := x.tr ++ [e], Cs := x.Cs ++ [C'] } :=
          isPrefix_of_extend hx hmem hstepB rfl rfl rfl
        have hzmem : { cfg := C', tr := x.tr ++ [e], Cs := x.Cs ++ [C'] } ∈ extend P B x := by
          rw [mem_extend_iff]
          exact ⟨e, C', hmem, hstepB, rfl, rfl, rfl⟩
        obtain ⟨y, hy, h1, h2, h3⟩ := ih hzpre
          (by unfold Runs; exact hsub)
          (fun w hw => hb w (List.Mem.tail _ hw))
        refine ⟨y, mem_frontier_extend hzmem hy, ?_, ?_, ?_⟩
        · rw [h1]
          simp [List.append_assoc]
        · rw [h2]
          simp [List.append_assoc]
        · rw [h3]
          exact lastD_drop_head x.cfg C' l (initCfg P) C'

/-! ### The explorer -/

/-- All nodes reachable in at most `n` bounded steps from the initial node. -/
def allNodes (P : Protocol) (B : Bounds) (n : Nat) : List Node :=
  (List.range (n + 1)).flatMap fun k => frontier P B k (initNode P)

/-- Does this node's execution violate a property? -/
def nodeViolates (P : Protocol) (x : Node) : Bool :=
  (traceLeaksBool P x.Cs) || ! (agreesBool (insts P x.Cs x.tr))

/-- **The executable question**: does some bounded execution violate a property? -/
def explorerAttack (P : Protocol) (B : Bounds) : Bool :=
  (allNodes P B B.steps).any (nodeViolates P)

/-- **Soundness**: a positive answer is a genuine bounded attack. -/
theorem explorer_sound {P : Protocol} {B : Bounds} (h : explorerAttack P B = true) :
    BoundedAttack P B := by
  classical
  rw [explorerAttack, List.any_eq_true] at h
  obtain ⟨x, hx, hv⟩ := h
  rw [allNodes, List.mem_flatMap] at hx
  obtain ⟨k, hk, hy⟩ := hx
  obtain ⟨hpre, hlen⟩ := isPrefix_of_mem_frontier (isPrefix_initNode P B) hy
  rw [nodeViolates, Bool.or_eq_true] at hv
  rw [BoundedAttack]
  refine ⟨x.tr, x.Cs, ⟨hpre.1, ?_, hpre.2.1⟩, ?_⟩
  · rw [hlen]
    simp only [initNode, List.length_nil, Nat.zero_add]
    exact Nat.le_of_lt_succ (List.mem_range.mp hk)
  · rcases hv with hleak | hbreak
    · left
      exact (traceLeaksBool_iff P x.Cs).mp hleak
    · right
      intro hall
      have h2 := agreesBool_iff (insts P x.Cs x.tr) |>.mpr hall
      simp [h2] at hbreak

/-- **Completeness**: a genuine bounded attack is found. -/
theorem explorer_complete {P : Protocol} {B : Bounds} (h : BoundedAttack P B) :
    explorerAttack P B = true := by
  classical
  obtain ⟨tr, Cs, ⟨hrun, hlen, hb⟩, hv⟩ := h
  obtain ⟨l, hCs⟩ := run_nonempty hrun
  subst hCs
  obtain ⟨y, hy, h1, h2, h3⟩ :=
    frontier_complete (isPrefix_initNode P B)
      (by unfold Runs; exact hrun)
      (fun C hC => hb C (List.Mem.tail _ hC))
  simp [initNode] at h1 h2
  rw [explorerAttack, List.any_eq_true]
  refine ⟨y, ?_, ?_⟩
  · rw [allNodes, List.mem_flatMap]
    refine ⟨tr.length, List.mem_range.mpr (by omega), ?_⟩
    exact h1 ▸ hy
  · rw [nodeViolates, Bool.or_eq_true]
    rw [← h2, ← h1] at hv
    rcases hv with hleak | hbreak
    · left
      exact (traceLeaksBool_iff P y.Cs).mpr hleak
    · right
      have hfalse : agreesBool (insts P y.Cs y.tr) = false := by
        rw [Bool.eq_false_iff]
        intro hall
        exact hbreak ((agreesBool_iff (insts P y.Cs y.tr)).mp hall)
      simp [hfalse]

/-- **The explorer decides the bounded question**: its answer is the security statement, with no
hypothesis about encodings, representability, or solver behaviour. -/
theorem explorer_correct (P : Protocol) (B : Bounds) :
    explorerAttack P B = true <-> BoundedAttack P B :=
  ⟨explorer_sound, explorer_complete⟩

/-- **Bounded safety by exhaustion**: if the explorer finds nothing, no permitted execution violates
a property. This is the statement a SAFE verdict is supposed to mean. -/
theorem boundedSafe_of_explorer (P : Protocol) (B : Bounds) (h : explorerAttack P B = false) :
    BoundedSafe P B := by
  intro ⟨tr, Cs, hrun, hv⟩
  exact absurd (explorer_complete ⟨tr, Cs, hrun, hv⟩) (by simpa using h)

/-! ### Gates

Every declaration below is kernel-checked by @@decide@@: the enumeration is evaluated by the kernel,
not trusted to the compiler. -/

namespace Gates

open ProtSat.ExprDomain

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A session generates a nonce, declares it secret, and publishes it encrypted under a key the
attacker does not hold. -/
def secureP : Protocol :=
  { roles := [{ acts := [Action.fresh 0 0, Action.secret (Expr.var 0),
                         Action.send 0 (Expr.encS (Expr.var 0) (Expr.shrk 0 1))] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := [7]
    compromised := []
    secrets := []
    auths := [] }

def secureB : Bounds := { steps := 3, rounds := 0 }

/-- **Non-vacuity.** The honest execution really reaches the generation, the declaration and the
publication, so the safety statement below is not the safety of a dead role. -/
theorem secure_honest_run :
    run secureP (initCfg secureP)
      [Ev.generate 0 7, Ev.act 0, Ev.act 0] ≠ none := by decide

/-- The obligation is taken, and the published message is not the secret. -/
theorem secure_obligation_and_publication :
    let Cs := (run secureP (initCfg secureP)
      [Ev.generate 0 7, Ev.act 0, Ev.act 0]).getD []
    (Cs.getLastD (initCfg secureP)).oblig = [Term.nonce 7] ∧
      Term.nonce 7 ∉ (Cs.getLastD (initCfg secureP)).kn := by decide

/-- **Bounded safety, proved by exhaustion.** The explorer enumerates every execution of at most
three events inside the universe, and none of them leaks the declared secret. -/
theorem secure_explorer_finds_nothing : explorerAttack secureP secureB = false := by decide

/-- Hence the query is safe: no permitted execution violates the selected property. This is the
verdict the project is for, and it carries no hypothesis about any encoding. -/
theorem secure_bounded_safe : BoundedSafe secureP secureB :=
  boundedSafe_of_explorer secureP secureB secure_explorer_finds_nothing

/-- **The attack the CNF loses.** The transient-pair model of @@ProtSat.Regressions.Bounds@@: every
configuration stays inside the universe, so the explorer finds the leak that the encoding's
representability condition excludes. -/
theorem transient_pair_attack_found : explorerAttack boundsP boundsB = true := by decide

/-- Hence it is a genuine bounded attack - which, combined with
@@ProtSat.Regressions.Bounds.not_withinBounds@@, is the precise statement of the gap: the public
bounded semantics says attack, the CNF says unsatisfiable. -/
theorem transient_pair_bounded_attack : BoundedAttack boundsP boundsB :=
  explorer_sound transient_pair_attack_found

/-- **Authentication is decidable here and not in the CNF.** The two-session claim/commit model of
@@ProtSat.Reference.Gates@@: the attacker may simply let the committing session run and the claiming
session idle, which is an unmatched commit. The old monitor missed this
(@@Regressions.Semantics.later_claim_excuses_commit@@) and the CNF cannot express it at all. -/
def authP : Protocol := ProtSat.Reference.Gates.pairP

def authB : Bounds := { steps := 2, rounds := 0 }

theorem auth_explorer_finds_the_break : explorerAttack authP authB = true := by decide

theorem auth_bounded_attack : BoundedAttack authP authB :=
  explorer_sound auth_explorer_finds_the_break

/-- And the same procedure says *no* when there is nothing to find: with a step bound of zero only
the initial configuration is inspected. -/
theorem zero_step_is_safe : explorerAttack authP { steps := 0, rounds := 0 } = false := by decide

end Gates

end ProtSat.Reference.Explore