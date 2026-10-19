/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Query
import ProtSat.Explore

/-!
# ProtSat: the goal-indexed contract over the repaired semantics

## Why this module exists

`ProtSat.Query` states the contract, but its goal-indexed predicates are written over the *old*
reference semantics (`ProtSat.Operational`) because that is what the generated CNF is proved
against. Two things follow. Authentication cannot be decided there at all: the monitor is unsound
(`ProtSat.Regressions.Semantics.later_claim_excuses_commit`) and the formula has no clause for it
(`ProtSat.Encode.violationLits` lists leak literals only). And the safety conclusion needs a
representability hypothesis the public bounds do not imply (`ProtSat.Regressions.Bounds`). So
`ProtSat.analyzeQuery` can report `encodingUnsat` but never `boundedSafe`
(`ProtSat.analyzeQuery_ne_boundedSafe`).

`ProtSat.Reference` repairs the semantics and `ProtSat.Reference.Explore` enumerates it
exhaustively. That combination *can* answer the intended question for both goals with no encoding
hypothesis at all. This module turns that into the public contract:

* `goalViolation P g` / `goalViolationBool P g` - the executions violating goal `g` over the
  repaired semantics: `ProtSat.Reference.traceLeaks` for secrecy, `ProtSat.Reference.authBreak`
  (ordered, role-aware, non-injective) for agreement.
* `boundedAttack q` - some **selected** goal of `q` is violated by some execution `q` permits
  (`ProtSat.Reference.Explore.BoundedRun`: from the initial configuration, at most
  `bounds.steps` events, every configuration inside `univ q.protocol q.bounds` and
  `q.protocol.nonceDomain`).
* `boundedSafe q` - **the meaning SAFE is supposed to have**: no permitted execution violates any
  selected goal.
* `attackFound q` / `findAttack q` - the executable question and its witness.
* `analyze q` - a verdict whose `boundedSafe` case is *produced by a proof* and whose `attack`
  case carries the violating execution itself.

## What each answer means

| `analyze q`       | what is proved                                                     |
|---------------------|--------------------------------------------------------------------|
| `invalidModel ds` | the model fails `ProtSat.validate`; `ds` says where                            |
| `noGoals`         | the query selected nothing, so there is nothing to be safe about    |
| `attack x`        | `x` is a permitted execution of `q` violating a selected goal                  |
| `boundedSafe e`   | `e.safe : boundedSafe q`, discharged by exhaustion                               |

There is no `unsupportedGoals` case: this analyser is not an encoding, so it represents the
authentication violation as directly as the secrecy violation. There is no `unknown` case either:
the procedure is total (exponential in the bounds, but total).

## The theorems that matter

`attackFound_decides` - the executable answer is equivalent to `boundedAttack q` in both
directions with no side condition. From it `analyze_attack_sound`, `analyze_boundedSafe_sound`
and `analyze_correct`. `Gates` instantiates all four verdicts on models that already carry
permanent counterexample witnesses elsewhere in the project.

## Why the namespace is `ProtSat.Reference.Contract`

The repaired semantics lives in `ProtSat.Reference` and the old one is declared directly in
`ProtSat`, so a module in `ProtSat` would resolve `Cfg` and `Ev` to the *old* configuration
and event types. Nesting the contract inside `ProtSat.Reference` makes the unqualified names mean
the repaired ones, which is the difference between a theorem about the model and a theorem about the
wrong model.
-/

namespace ProtSat.Reference.Contract

open ProtSat.Reference.Explore

/-! ### Which executions violate which goal -/

/-- **Goal-indexed violation over the repaired semantics.** Secrecy is "some configuration of the
trace knows a declared secret" (long-term declarations plus snapshot obligations); agreement is
"some commit has no matching earlier claim". Both are propositions about the reference semantics
alone: no CNF, no variable numbering and no solver appears here. -/
def goalViolation (P : Protocol) (g : Goal) (Cs : List Cfg) (tr : List Ev) : Prop :=
  match g with
  | Goal.secrecy => traceLeaks P Cs
  | Goal.agreement => authBreak P Cs tr

theorem goalViolation_secrecy (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    goalViolation P Goal.secrecy Cs tr <-> traceLeaks P Cs := Iff.rfl

theorem goalViolation_agreement (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    goalViolation P Goal.agreement Cs tr <-> authBreak P Cs tr := Iff.rfl

/-- The executable twin of `goalViolation`, via the two proved monitors. -/
def goalViolationBool (P : Protocol) (g : Goal) (Cs : List Cfg) (tr : List Ev) : Bool :=
  match g with
  | Goal.secrecy => traceLeaksBool P Cs
  | Goal.agreement => ! (agreesBool (insts P Cs tr))

theorem goalViolationBool_iff (P : Protocol) (g : Goal) (Cs : List Cfg) (tr : List Ev) :
    goalViolationBool P g Cs tr = true <-> goalViolation P g Cs tr := by
  cases g
  · exact traceLeaksBool_iff P Cs
  · simp only [goalViolation, goalViolationBool, authBreak]
    have key : (Bool.not (agreesBool (insts P Cs tr)) = true) <->
        ¬ agreesBool (insts P Cs tr) = true := by
      cases agreesBool (insts P Cs tr) <;> simp
    rw [key, Iff.not (agreesBool_iff (insts P Cs tr))]

/-! ### The bounded question -/

/-- An attack on query `q` through goal `g`: an execution the query permits that violates `g`. -/
def boundedAttackFor (q : Query) (g : Goal) : Prop :=
  ∃ (tr : List Ev) (Cs : List Cfg),
    BoundedRun q.protocol q.bounds tr Cs ∧ goalViolation q.protocol g Cs tr

/-- **The query has an attack**: some *selected* goal is violated by some permitted execution. -/
def boundedAttack (q : Query) : Prop := ∃ g ∈ q.goals, boundedAttackFor q g

/-- **The intended meaning of SAFE**: no execution permitted by the query's model, domains and bounds
violates any goal the query selected. Compare `ProtSat.boundedSafeGoals`, which states the same
shape over the old semantics the CNF is proved against. -/
def boundedSafe (q : Query) : Prop := ¬ boundedAttack q

/-- Does this enumerated node violate one of the query's selected goals? -/
def nodeViolatesQuery (q : Query) (x : Node) : Bool :=
  q.goals.any fun g => goalViolationBool q.protocol g x.Cs x.tr

/-- **The executable question**: is some enumerated execution a violation of a selected goal? -/
def attackFound (q : Query) : Bool :=
  (allNodes q.protocol q.bounds q.bounds.steps).any (nodeViolatesQuery q)

/-- The first enumerated execution that violates a selected goal, if there is one. -/
def findAttack (q : Query) : Option Node :=
  (allNodes q.protocol q.bounds q.bounds.steps).find? (nodeViolatesQuery q)

/-! ### Three list lemmas: `find?` and `any` say the same thing -/

/-- If `find?` returns a witness, some element of the list satisfies the predicate. -/
theorem exists_of_find? {α : Type} {p : α -> Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : ∃ y ∈ l, p y = true := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons a as ih =>
      by_cases hp : p a = true
      · exact ⟨a, List.Mem.head _, hp⟩
      · rw [List.find?_cons_of_neg hp] at h
        obtain ⟨y, hy, hpy⟩ := ih h
        exact ⟨y, List.Mem.tail _ hy, hpy⟩

/-- The witness `find?` returns is in the list and satisfies the predicate. -/
theorem find?_some_mem {α : Type} {p : α -> Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : x ∈ l ∧ p x = true := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons a as ih =>
      by_cases hp : p a = true
      · rw [List.find?_cons_of_pos hp] at h
        have hax : a = x := Option.some.inj h
        subst hax
        exact ⟨List.Mem.head _, hp⟩
      · rw [List.find?_cons_of_neg hp] at h
        obtain ⟨h1, h2⟩ := ih h
        exact ⟨List.Mem.tail _ h1, h2⟩

/-- If some element satisfies the predicate, `find?` finds one. -/
theorem find?_some_of_any {α : Type} (p : α -> Bool) :
    ∀ {l : List α}, l.any p = true -> ∃ x, l.find? p = some x
  | [], h => absurd h (by simp)
  | a :: as, h => by
      rw [List.any_cons] at h
      by_cases hp : p a = true
      · exact ⟨a, List.find?_cons_of_pos hp⟩
      · obtain ⟨x, hx⟩ := find?_some_of_any p (by simpa [hp] using h)
        exact ⟨x, by rw [List.find?_cons_of_neg hp]; exact hx⟩

/-- If no element satisfies the predicate, `find?` finds nothing. -/
theorem find?_eq_none_of_any_false {α : Type} (p : α -> Bool) :
    ∀ {l : List α}, l.any p = false -> l.find? p = none := by
  intro l hl
  classical
  cases h : l.find? p with
  | none => rfl
  | some x =>
      obtain ⟨y, hy, hpy⟩ := exists_of_find? h
      have h2 : l.any p = true := List.any_eq_true.mpr ⟨y, hy, hpy⟩
      rw [hl] at h2
      exact absurd h2 (by simp)

/-- The positive answer is equivalent to the existence of a witness. -/
theorem findAttack_some_of_attackFound {q : Query} (h : attackFound q = true) :
    ∃ x, findAttack q = some x :=
  find?_some_of_any (nodeViolatesQuery q) h

/-- The negative answer is equivalent to the absence of a witness. -/
theorem findAttack_none_of_attackFound_false {q : Query} (h : attackFound q = false) :
    findAttack q = none :=
  find?_eq_none_of_any_false (nodeViolatesQuery q) h

/-- And the converse: an empty witness search means the answer was negative. -/
theorem attackFound_false_of_findAttack_none {q : Query} (h : findAttack q = none) :
    attackFound q = false := by
  classical
  by_cases hf : attackFound q = true
  · obtain ⟨x, hx⟩ := findAttack_some_of_attackFound hf
    rw [hx] at h
    exact absurd h (by simp)
  · exact by simpa using hf

/-! ### Soundness and completeness of the enumeration -/

/-- **Soundness**: a positive answer of the executable question is a genuine attack on the query. -/
theorem boundedAttack_of_attackFound {q : Query} (h : attackFound q = true) : boundedAttack q := by
  classical
  rw [attackFound, List.any_eq_true] at h
  obtain ⟨x, hx, hv⟩ := h
  obtain ⟨hpre, hlen⟩ := prefix_of_mem_allNodes hx
  rw [nodeViolatesQuery, List.any_eq_true] at hv
  obtain ⟨g, hg, hv⟩ := hv
  refine ⟨g, hg, x.tr, x.Cs, ⟨hpre.1, hlen, hpre.2.1⟩, ?_⟩
  exact (goalViolationBool_iff q.protocol g x.Cs x.tr).mp hv

/-- **Completeness**: every genuine attack on the query is enumerated. This is the step the CNF route
cannot match, because it needs the representability hypothesis the public bounds do not imply. -/
theorem attackFound_of_boundedAttack (q : Query) (h : boundedAttack q) : attackFound q = true := by
  classical
  obtain ⟨g, hg, tr, Cs, hrun, hv⟩ := h
  obtain ⟨hrun', hlen, hb⟩ := hrun
  obtain ⟨l, hCs⟩ := run_nonempty hrun'
  subst hCs
  obtain ⟨y, hy, h1, h2, h3⟩ :=
    frontier_complete (isPrefix_initNode q.protocol q.bounds)
      (by unfold Runs; exact hrun') (fun C hC => hb C (List.Mem.tail _ hC))
  simp [initNode] at h1 h2
  rw [attackFound, List.any_eq_true]
  refine ⟨y, ?_, ?_⟩
  · rw [allNodes, List.mem_flatMap]
    refine ⟨tr.length, List.mem_range.mpr (by omega), ?_⟩
    exact h1 ▸ hy
  · rw [nodeViolatesQuery, List.any_eq_true]
    refine ⟨g, hg, ?_⟩
    rw [goalViolationBool_iff]
    rwa [← h1, ← h2] at hv

/-- **The enumeration decides the query's question** in both directions, with no hypothesis about
encodings, representability or solver behaviour. -/
theorem attackFound_decides (q : Query) : attackFound q = true <-> boundedAttack q :=
  ⟨boundedAttack_of_attackFound, attackFound_of_boundedAttack q⟩

/-- Nothing found means safe. -/
theorem boundedSafe_of_attackFound_false {q : Query} (h : attackFound q = false) : boundedSafe q :=
  fun hat => absurd (attackFound_of_boundedAttack q hat) (by simpa using h)

/-- If the witness search finds nothing, the query is safe. -/
theorem boundedSafe_of_findAttack_none {q : Query} (h : findAttack q = none) : boundedSafe q :=
  boundedSafe_of_attackFound_false (attackFound_false_of_findAttack_none h)

/-- **Safety in the explorer's sense implies safety of the query**: selecting goals can only ask about
a subset of what the explorer already ruled out. -/
theorem boundedSafe_of_BoundedSafe {q : Query} (h : BoundedSafe q.protocol q.bounds) :
    boundedSafe q := by
  intro hat
  obtain ⟨g, hg, tr, Cs, hrun, hv⟩ := hat
  refine h ⟨tr, Cs, hrun, ?_⟩
  cases g
  · exact Or.inl hv
  · exact Or.inr hv

/-- Dually, an attack the explorer finds is an attack on any query that selected both goals. -/
theorem boundedAttack_of_BoundedAttack {q : Query} (hsec : Goal.secrecy ∈ q.goals)
    (hag : Goal.agreement ∈ q.goals) (h : BoundedAttack q.protocol q.bounds) : boundedAttack q := by
  obtain ⟨tr, Cs, hrun, hv⟩ := h
  rcases hv with hleak | hbreak
  · exact ⟨Goal.secrecy, hsec, tr, Cs, hrun, hleak⟩
  · exact ⟨Goal.agreement, hag, tr, Cs, hrun, hbreak⟩

/-! ### Evidence and verdicts -/

/-- **Evidence for a bounded-safety verdict**: the query it is evidence *for*, and the proof that no
execution that query permits violates a selected goal. The record cannot be replayed against a
different protocol, bounds or goal set, because its `safe` field is a proposition about its own
`query` field. Compare `ProtSat.SafeEvidence`, which carries the old-semantics statement the CNF
route would have to prove. -/
structure SafeEvidence where
  query : Query
  safe : boundedSafe query

/-- The answer of the enumeration analyser. Every case is meaningful: unlike the CNF verdict there is
no "the formula has no model" case, because nothing here is a formula. -/
inductive Verdict where
  | invalidModel : List Diagnostic -> Verdict
  | noGoals : Verdict
  | attack : Node -> Verdict
  | boundedSafe : SafeEvidence -> Verdict

/-- The violating execution the search found, given that it found one. The `getD` fallback is
unreachable: `findAttack_some_of_attackFound` supplies a real witness whenever the answer is
positive, and `foundNode_eq` identifies the verdict's node with it. -/
def foundNode (q : Query) : Node :=
  (findAttack q).getD (initNode q.protocol)

/-- The answer for a query that selected at least one goal: the witness if the enumeration found one,
otherwise safety with its evidence attached. This is what lets the `boundedSafe` case be *produced*
rather than withheld. -/
def answer (q : Query) : Verdict :=
  if h : attackFound q = true then
    Verdict.attack (foundNode q)
  else
    Verdict.boundedSafe
      { query := q, safe := boundedSafe_of_attackFound_false (by simpa using h) }

/-- **The enumeration analyser**: validation first, then goal selection, then the decision
procedure. -/
def analyze (q : Query) : Verdict :=
  if (validate q).isEmpty then
    if q.goals.isEmpty then Verdict.noGoals else answer q
  else Verdict.invalidModel (validate q)

/-! ### What the verdicts mean -/

theorem foundNode_eq {q : Query} {x : Node} (hx : findAttack q = some x) : foundNode q = x := by
  rw [foundNode, hx]
  rfl

/-- An `attack` verdict names a witness the enumeration really found. -/
theorem answer_attack {q : Query} (hf : attackFound q = true) {x : Node}
    (hx : findAttack q = some x) : answer q = Verdict.attack x := by
  classical
  simp [answer, foundNode, hf, hx]

/-- A negative search produces safety, with the proof attached. -/
theorem answer_boundedSafe {q : Query} (hf : attackFound q = false) :
    ∃ e, answer q = Verdict.boundedSafe e := by
  classical
  refine ⟨{ query := q, safe := boundedSafe_of_attackFound_false hf }, ?_⟩
  simp [answer, hf]

/-- The two security answers are exclusive. -/
theorem answer_ne_attack {q : Query} (hf : attackFound q = false) (x : Node) :
    answer q ≠ Verdict.attack x := by
  classical
  simp [answer, hf]

theorem answer_ne_boundedSafe {q : Query} (hf : attackFound q = true) (e : SafeEvidence) :
    answer q ≠ Verdict.boundedSafe e := by
  classical
  simp [answer, hf]

/-- An `attack` verdict means the search was positive. -/
theorem attackFound_of_answer_attack {q : Query} {x : Node} (h : answer q = Verdict.attack x) :
    attackFound q = true := by
  classical
  by_cases hf : attackFound q = true
  · exact hf
  · have hf' : attackFound q = false := by simpa using hf
    exact absurd h (answer_ne_attack hf' x)

/-- A model that fails validation gets `invalidModel` and nothing else. -/
theorem analyze_invalid (q : Query) (h : (validate q).isEmpty = false) :
    analyze q = Verdict.invalidModel (validate q) := by
  rw [analyze, h]
  simp

/-- A query that selected nothing gets `noGoals`: there is no property to be safe about. -/
theorem analyze_noGoals (q : Query) (hval : (validate q).isEmpty = true)
    (h : q.goals.isEmpty = true) : analyze q = Verdict.noGoals := by
  rw [analyze, hval, h]
  simp

/-- A well formed query with a selected goal and a positive search gets an `attack` verdict. -/
theorem analyze_attack (q : Query) (hval : (validate q).isEmpty = true)
    (hne : q.goals.isEmpty = false) (hf : attackFound q = true) :
    ∃ x, analyze q = Verdict.attack x := by
  classical
  obtain ⟨x, hx⟩ := findAttack_some_of_attackFound hf
  refine ⟨x, ?_⟩
  rw [analyze, hval, hne]
  simp
  exact answer_attack hf hx

/-- A well formed query with a selected goal and a negative search gets `boundedSafe`. -/
theorem analyze_boundedSafe (q : Query) (hval : (validate q).isEmpty = true)
    (hne : q.goals.isEmpty = false) (hf : attackFound q = false) :
    ∃ e, analyze q = Verdict.boundedSafe e := by
  classical
  obtain ⟨e, he⟩ := answer_boundedSafe hf
  refine ⟨e, ?_⟩
  rw [analyze, hval, hne]
  simp
  exact he

/-- **An `attack` verdict is sound**: the query really has an attack, witnessed by the execution the
verdict carries. -/
theorem analyze_attack_sound (q : Query) {x : Node} (h : analyze q = Verdict.attack x) :
    boundedAttack q := by
  classical
  by_cases hval : (validate q).isEmpty = true
  · by_cases hne : q.goals.isEmpty = true
    · rw [analyze_noGoals q hval hne] at h
      cases h
    · have hnf : q.goals.isEmpty = false := by simpa using hne
      rw [analyze, hval, hnf] at h
      simp at h
      exact boundedAttack_of_attackFound (attackFound_of_answer_attack h)
  · have hnf : (validate q).isEmpty = false := by simpa using hval
    rw [analyze_invalid q hnf] at h
    cases h

/-- **A `boundedSafe` verdict is sound**: no permitted execution of the query violates a selected
goal. This is the implication the roadmap asked for, and it carries no encoding hypothesis. -/
theorem analyze_boundedSafe_sound (q : Query) {e : SafeEvidence}
    (h : analyze q = Verdict.boundedSafe e) : boundedSafe q := by
  classical
  by_cases hval : (validate q).isEmpty = true
  · by_cases hne : q.goals.isEmpty = true
    · rw [analyze_noGoals q hval hne] at h
      cases h
    · have hnf : q.goals.isEmpty = false := by simpa using hne
      rw [analyze, hval, hnf] at h
      simp at h
      by_cases hf : attackFound q = true
      · exact absurd h (answer_ne_boundedSafe hf e)
      · exact boundedSafe_of_attackFound_false (by simpa using hf)
  · have hnf : (validate q).isEmpty = false := by simpa using hval
    rw [analyze_invalid q hnf] at h
    cases h

/-- **The analyser is correct**: for a well formed query that selected a goal, it reports an attack
exactly when the query has one. -/
theorem analyze_correct (q : Query) (hval : (validate q).isEmpty = true)
    (hne : q.goals.isEmpty = false) : (∃ x, analyze q = Verdict.attack x) <-> boundedAttack q := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    exact analyze_attack_sound q hx
  · intro hat
    exact analyze_attack q hval hne (attackFound_of_boundedAttack q hat)

/-- Exactly one of the two security answers is produced for a well formed query with a selected goal. -/
theorem analyze_exclusive (q : Query) (hval : (validate q).isEmpty = true)
    (hne : q.goals.isEmpty = false) :
    (∃ x, analyze q = Verdict.attack x) <-> ¬ ∃ e, analyze q = Verdict.boundedSafe e := by
  classical
  by_cases hf : attackFound q = true
  · refine ⟨fun hex hno => ?_, fun _ => analyze_attack q hval hne hf⟩
    obtain ⟨x, hx⟩ := hex
    obtain ⟨e, he⟩ := hno
    rw [analyze, hval, hne] at hx he
    simp at hx he
    exact answer_ne_boundedSafe hf e he
  · have hf' : attackFound q = false := by simpa using hf
    refine ⟨fun hex hno => ?_, fun hno => absurd (analyze_boundedSafe q hval hne hf') hno⟩
    obtain ⟨x, hx⟩ := hex
    obtain ⟨e, he⟩ := hno
    rw [analyze, hval, hne] at hx he
    simp at hx he
    rw [hx] at he
    cases he

/-! ### The attack verdict is a certificate -/

/-- **An `attack` verdict carries its own certificate**: the node it names is a bounded execution of
the query (a run from the initial configuration, inside the bounds at every step, no longer than
`bounds.steps`) and it violates one of the goals the query selected. -/
theorem answer_attack_certificate {q : Query} {x : Node} (h : answer q = Verdict.attack x) :
    isPrefix q.protocol q.bounds x ∧ x.tr.length ≤ q.bounds.steps
      ∧ ∃ g ∈ q.goals, goalViolationBool q.protocol g x.Cs x.tr = true := by
  classical
  have hf : attackFound q = true := attackFound_of_answer_attack h
  obtain ⟨y, hy⟩ := findAttack_some_of_attackFound hf
  have h2 : answer q = Verdict.attack y := answer_attack hf hy
  rw [h] at h2
  cases h2
  obtain ⟨hmem, hp⟩ := find?_some_mem (p := nodeViolatesQuery q) hy
  obtain ⟨hpre, hlen⟩ := prefix_of_mem_allNodes hmem
  rw [nodeViolatesQuery, List.any_eq_true] at hp
  obtain ⟨g, hg, hgv⟩ := hp
  exact ⟨hpre, hlen, g, hg, hgv⟩

/-- The same statement for the full analyser: an `attack` answer is a certificate, not a claim. -/
theorem analyze_attack_certificate {q : Query} {x : Node} (h : analyze q = Verdict.attack x) :
    isPrefix q.protocol q.bounds x ∧ x.tr.length ≤ q.bounds.steps
      ∧ ∃ g ∈ q.goals, goalViolationBool q.protocol g x.Cs x.tr = true := by
  classical
  by_cases hval : (validate q).isEmpty = true
  · by_cases hne : q.goals.isEmpty = true
    · rw [analyze_noGoals q hval hne] at h
      cases h
    · have hnf : q.goals.isEmpty = false := by simpa using hne
      rw [analyze, hval, hnf] at h
      simp at h
      exact answer_attack_certificate h
  · have hnf : (validate q).isEmpty = false := by simpa using hval
    rw [analyze_invalid q hnf] at h
    cases h

/-- **Independent re-check of a witness**, without running the search: the trace really is a run from
the initial configuration, every configuration it visits stays inside the bounds, it fits the step
bound, and it violates a selected goal. Every conjunct is a `Bool` computation over the certificate
and the query's own data. -/
def checkWitness (q : Query) (x : Node) : Bool :=
  (decide (run q.protocol (initCfg q.protocol) x.tr = some x.Cs))
    && (decide (x.tr.length ≤ q.bounds.steps))
    && (x.Cs.all (fun C => inBoundsBool q.protocol q.bounds C))
    && nodeViolatesQuery q x

/-- **A checked witness is an attack.** Soundness of the re-checker, with no hypothesis about any
encoding: this is what an `attack` verdict can be reduced to for a verifier that does not trust the
search. -/
theorem checkWitness_sound {q : Query} {x : Node} (h : checkWitness q x = true) : boundedAttack q := by
  classical
  rw [checkWitness] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hrun, hlen⟩, hcfgs⟩, hv⟩ := h
  rw [nodeViolatesQuery, List.any_eq_true] at hv
  obtain ⟨g, hg, hgv⟩ := hv
  refine ⟨g, hg, x.tr, x.Cs, ⟨hrun, hlen, ?_⟩, ?_⟩
  · intro C hC
    exact (inBoundsBool_iff.mp (hcfgs C hC))
  · exact (goalViolationBool_iff q.protocol g x.Cs x.tr).mp hgv

/-- The witness an `attack` verdict produces passes the independent re-checker. -/
theorem answer_checkWitness {q : Query} (hf : attackFound q = true) :
    checkWitness q (foundNode q) = true := by
  classical
  obtain ⟨x, hx⟩ := findAttack_some_of_attackFound hf
  have hcert := answer_attack_certificate (answer_attack hf hx)
  have hfn : foundNode q = x := foundNode_eq hx
  rw [hfn]
  obtain ⟨hpre, hlen, g, hg, hgv⟩ := hcert
  simp only [checkWitness, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨hpre.1, hlen⟩, ?_⟩, List.any_eq_true.mpr ⟨g, hg, hgv⟩⟩
  intro C hC
  exact inBoundsBool_iff.mpr (hpre.2.1 C hC)

/-! ### The acceptance gate: nothing else may produce a security verdict -/

/-- A malformed model gets neither verdict that says anything about security. -/
theorem analyze_ne_security_of_invalid (q : Query) (h : (validate q).isEmpty = false) :
    (∀ x, analyze q ≠ Verdict.attack x) ∧ ∀ e, analyze q ≠ Verdict.boundedSafe e := by
  rw [analyze_invalid q h]
  refine ⟨fun x hc => ?_, fun e hc => ?_⟩
  · cases hc
  · cases hc

/-- A query that selected nothing gets no security verdict either: safety of nothing is not reported as
safety. -/
theorem analyze_ne_security_of_noGoals (q : Query) (hval : (validate q).isEmpty = true)
    (h : q.goals.isEmpty = true) :
    (∀ x, analyze q ≠ Verdict.attack x) ∧ ∀ e, analyze q ≠ Verdict.boundedSafe e := by
  rw [analyze_noGoals q hval h]
  refine ⟨fun x hc => ?_, fun e hc => ?_⟩
  · cases hc
  · cases hc

/-- Safety of the query implies the analyser never reports an attack on it. -/
theorem analyze_ne_attack_of_boundedSafe (q : Query) (h : boundedSafe q) (x : Node) :
    analyze q ≠ Verdict.attack x := by
  classical
  by_cases hval : (validate q).isEmpty = true
  · by_cases hne : q.goals.isEmpty = true
    · rw [analyze_noGoals q hval hne]
      intro hc
      cases hc
    · have hnf : q.goals.isEmpty = false := by simpa using hne
      rw [analyze, hval, hnf]
      simp
      have hf : attackFound q = false := by
        by_cases hc : attackFound q = true
        · exact absurd ((attackFound_decides q).mp hc) h
        · exact by simpa using hc
      exact answer_ne_attack hf x
  · have hnf : (validate q).isEmpty = false := by simpa using hval
    rw [analyze_invalid q hnf]
    intro hc
    cases hc

/-- One-line rendering of an answer, for the command-line driver. -/
def describe : Verdict -> String
  | Verdict.invalidModel ds =>
      "INVALID MODEL (" ++ toString ds.length ++ " diagnostics)"
  | Verdict.noGoals => "NO GOALS SELECTED (nothing was asked)"
  | Verdict.attack x => "ATTACK (" ++ toString x.tr.length ++ " events); execution accepted"
  | Verdict.boundedSafe _ => "BOUNDED SAFE (no permitted execution violates a selected goal)"

/-! ### Gates

Each gate instantiates one verdict on a model that already carries a permanent witness elsewhere in
the project. The `decide` calls are kernel computations: the enumeration is evaluated by the
kernel, not trusted to the compiler. -/

namespace Gates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The explorer's secure model with **both** goals selected. -/
def secureQ : Query :=
  Query.mk Explore.Gates.secureP Explore.Gates.secureB [Goal.secrecy, Goal.agreement]

/-- The authentication model of `ProtSat.Reference.Gates`, asking the question the CNF cannot ask. -/
def authQ : Query :=
  Query.mk Explore.Gates.authP Explore.Gates.authB [Goal.agreement]

/-- The transient-pair model: the attack the CNF's representability condition excludes. -/
def transientQ : Query :=
  Query.mk ProtSat.ExprDomain.boundsP ProtSat.ExprDomain.boundsB [Goal.secrecy]

/-- A query that selects nothing. -/
def emptyQ : Query := Query.mk Explore.Gates.secureP Explore.Gates.secureB []

/-- A well formed model with a session naming a role that does not exist. -/
def badQ : Query :=
  Query.mk { Explore.Gates.secureP with sessions := [{ role := 5, self := 0, peer := 1 }] }
    Explore.Gates.secureB [Goal.secrecy]

theorem secureQ_wellFormed : (validate secureQ).isEmpty = true := by decide
theorem secureQ_hasGoals : secureQ.goals.isEmpty = false := by decide

/-- **Bounded safety, with evidence, on a model whose honest execution is proved reachable**
(`Explore.Gates.secure_honest_run`). This is the verdict the project exists to produce. -/
theorem secureQ_verdict : ∃ e, analyze secureQ = Verdict.boundedSafe e :=
  analyze_boundedSafe secureQ secureQ_wellFormed secureQ_hasGoals
    (by decide : attackFound secureQ = false)

/-- The same conclusion from the explorer's already kernel-checked answer, at no extra cost. -/
theorem secureQ_boundedSafe : boundedSafe secureQ :=
  boundedSafe_of_BoundedSafe Explore.Gates.secure_bounded_safe

/-- And no attack verdict is possible for it. -/
theorem secureQ_no_attack_verdict : ∀ x, analyze secureQ ≠ Verdict.attack x :=
  analyze_ne_attack_of_boundedSafe secureQ secureQ_boundedSafe

theorem authQ_wellFormed : (validate authQ).isEmpty = true := by decide
theorem authQ_hasGoals : authQ.goals.isEmpty = false := by decide

/-- **Authentication is decidable here.** The commit-only model, on the question the CNF refuses to
answer: the analyser produces the violating execution. -/
theorem authQ_verdict : ∃ x, analyze authQ = Verdict.attack x :=
  analyze_attack authQ authQ_wellFormed authQ_hasGoals
    (by decide : attackFound authQ = true)

/-- The attack is a violation of the *selected* goal, not of something else. -/
theorem authQ_boundedAttack : boundedAttack authQ := by
  obtain ⟨x, hx⟩ := authQ_verdict
  exact analyze_attack_sound authQ hx

/-- For comparison, the CNF analyser refuses the question outright rather than answering it. -/
theorem authQ_cnf_refused : analyzeQuery authQ = Result.unsupportedGoals [Goal.agreement] := by
  have hsel : ∃ g ∈ authQ.goals, ! goalEncoded g :=
    ⟨Goal.agreement, by simp [authQ], by decide⟩
  rw [analyzeQuery_unsupported_of_unencoded (by simpa using authQ_wellFormed)
    (by simpa using authQ_hasGoals) hsel]
  have : unsupported authQ = [Goal.agreement] := by decide
  rw [this]

/-- The authentication verdict's witness passes the independent re-checker. -/
theorem authQ_witness_checks : checkWitness authQ (foundNode authQ) = true :=
  answer_checkWitness (by decide : attackFound authQ = true)

/-- And the transient-pair verdict's witness does too. -/
theorem transientQ_witness_checks : checkWitness transientQ (foundNode transientQ) = true :=
  answer_checkWitness (by decide : attackFound transientQ = true)

theorem transientQ_wellFormed : (validate transientQ).isEmpty = true := by decide
theorem transientQ_hasGoals : transientQ.goals.isEmpty = false := by decide

/-- The leak the encoding cannot represent is an attack here;
`ProtSat.Regressions.Bounds.analyze_encodingUnsat` proves the same query's CNF unsatisfiable, which
is the gap stated exactly. -/
theorem transientQ_verdict : ∃ x, analyze transientQ = Verdict.attack x :=
  analyze_attack transientQ transientQ_wellFormed transientQ_hasGoals
    (by decide : attackFound transientQ = true)

theorem transientQ_boundedAttack : boundedAttack transientQ := by
  obtain ⟨x, hx⟩ := transientQ_verdict
  exact analyze_attack_sound transientQ hx

theorem emptyQ_wellFormed : (validate emptyQ).isEmpty = true := by decide

/-- Selecting nothing is reported as such, never as safety. -/
theorem emptyQ_verdict : analyze emptyQ = Verdict.noGoals :=
  analyze_noGoals emptyQ emptyQ_wellFormed (by simp [emptyQ])

theorem badQ_validate : validate badQ = [Diagnostic.roleOutOfRange 0 5] := by decide

/-- A malformed model gets its diagnostics, not a security verdict. -/
theorem badQ_verdict : analyze badQ = Verdict.invalidModel [Diagnostic.roleOutOfRange 0 5] := by
  rw [analyze_invalid badQ (by rw [badQ_validate]; simp), badQ_validate]

end Gates

end ProtSat.Reference.Contract
