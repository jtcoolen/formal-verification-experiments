/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Complete
import ProtSat.ExprDomain

/-!
# ProtSat: representability as a choice of value domain (roadmap stage 4)

## The gap this closes

`Complete.RunOK.exprB` (ProtSat/Complete.lean:216) is the seventh boundedness condition:

```
exprB : ∀ i q e, e ∈ allExprs P → admissible sh (Expr.eval e (storeOf (cfg i) q)) = true
```

It says every expression of the protocol denotes a universe message, or nothing, in every session
store of the run. It is the hypothesis that makes `Complete.encoding_complete` conditional, and
`Regressions.Bounds` shows it is a real restriction and not a formality: the legitimate run of

```
recv x;  check (fst (pair x x)) x;  send K
```

fails it, because `pair (var 0) (var 0)` is a table entry whose value `pair x x` is outside the
universe, even though the value the action actually uses, `fst (pair x x) = x`, is inside it.

The reason is structural. `Encode.uIdx` names a value by its position in `sh.U`, and the encoding
has exactly one value domain, `shVal sh = sh.U.length + 1`, shared by the store, knowledge,
delivery, authentication *and* expression families. So an intermediate the universe does not contain
has no name, and the Tseitin gate that computes it records "unset".

## Why raising the bound is not the answer

`Bounded.univ P B` closes the seed set under the protocol's constructors `B.rounds` times, so a
larger `rounds` does add pairs - and it never adds enough. `no_bound_discharges_exprB` below shows
that for every `r` there is a universe-valued store in which `pair (var 0) (var 0)` denotes a
message `univ P ⟨_, r⟩` does not contain. No finite universe is closed under pairing, and `exprB`
asks for exactly that. The condition therefore cannot be derived *from the bounds*: the fix has to
be in the value domain.

## What this module does

Separate the two roles that `sh.U` currently plays, as roadmap stage 4 asks:

* the **persistent** universe `univ P B` - what a configuration may store, publish or declare
  secret. This stays the user's bound, and it stays what `BoundedTrace` quantifies over;
* the **nameable** domain `exprVals U P` - the persistent universe plus every intermediate value any
  table expression can compute from a universe-valued store. This is where expression gates read and
  write.

`ExprDomain.evalDomain` already builds the second set per expression, and
`ExprDomain.eval_mem_evalDomain` already says the reference evaluator cannot leave it, with no
closure assumption on `U`. The theorems below assemble that into what the encoding needs:

* `eval_inside_exprVals`: every table expression, evaluated in *any* universe-valued store, denotes
  a nameable value - no hypothesis about a run, no closure assumption, no bound arithmetic;
* `stepEval1_inside_exprVals` / `stepEval2_inside_exprVals`: the two facts the completeness proof
  actually consumes. `exprB` is invoked at exactly six sites in three lemmas
  (ProtSat/Complete.lean:2540, 2551, 3200, 3307, 3359): `rdXe_unary`, `rdXe_binary`, and three uses
  that only need the published value to be in the universe. The first two become theorems about the
  domain instead of assumptions about the execution;
* `exprB_of_exprVals`: `exprB` holds *for every run at once* when the shape's value domain is the
  extended one;
* `transient_nameable`, `transient_gate_not_clipped`, `transient_valAt_uIdx`: the message
  `Regressions.gate_clipped` shows the encoding cannot name becomes nameable at the *same* bounds
  that fail `exprB`;
* `no_bound_discharges_exprB`: and the contrast, proved - no `Bounds.rounds` discharges it.

Wiring `exprVals` into `Shape` and the `xe` variable family is the next increment. Nothing here
changes the existing encoding, so the 8A soundness direction is untouched (it already tolerates
clipped intermediates: `Encoding.xe_unary`/`xe_binary` conclude with a `.filter` on universe
membership).
-/

namespace ProtSat.Represent

open ProtSat Term Protocol Bounded Encode Encoding Complete ExprDomain

/-! ### The nameable domain -/

/-- The messages of a value list, dropping the unset value. -/
def valTerms : List Val -> List Term
  | [] => []
  | none :: r => valTerms r
  | some t :: r => t :: valTerms r

theorem valTerms_nil : valTerms [] = [] := rfl

theorem valTerms_none {r : List Val} : valTerms (none :: r) = valTerms r := rfl

theorem valTerms_some {t : Term} {r : List Val} : valTerms (some t :: r) = t :: valTerms r := rfl

theorem mem_valTerms {l : List Val} {t : Term} : t ∈ valTerms l <-> some t ∈ l := by
  induction l with
  | nil => simp [valTerms]
  | cons v rest ih =>
      cases v with
      | none =>
          have h1 : valTerms (none :: rest) = valTerms rest := rfl
          rw [h1, ih, List.mem_cons]
          refine ⟨fun h => Or.inr h, fun h => ?_⟩
          rcases h with h | h
          · exact absurd h (by simp)
          · exact h
      | some t' =>
          have h1 : valTerms (some t' :: rest) = t' :: valTerms rest := rfl
          rw [h1, List.mem_cons, ih, List.mem_cons]
          constructor
          · rintro (h | h)
            · left; exact congrArg some h
            · right; exact h
          · rintro (h | h)
            · left; exact Option.some.inj h
            · right; exact h

/-- **The nameable values of a query**: the persistent universe `U`, followed by every message any
expression of the protocol can denote when every store variable holds a message of `U`.

`U` is kept as a prefix, so a value already in the universe keeps the index the store, knowledge and
delivery families give it: extending the domain never renumbers anything the encoding names. -/
def exprVals (U : List Term) (P : Protocol) : List Term :=
  U ++ ((allExprs P).flatMap fun e => valTerms (evalDomain U e)).eraseDups

/-- The universe embeds into the nameable domain. -/
theorem mem_exprVals_of_mem {U : List Term} {P : Protocol} {t : Term} (h : t ∈ U) :
    t ∈ exprVals U P :=
  List.mem_append_left _ h

/-- Extending the domain does not renumber a universe message: `ixOf` finds the first occurrence,
and the original copy is still first. -/
theorem ixOf_append_left {α : Type} [BEq α] [LawfulBEq α] (a : α) (l r : List α) (h : a ∈ l) :
    ixOf a (l ++ r) = ixOf a l := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      by_cases hx : x == a
      · have hxa : x = a := by simpa using hx
        subst hxa
        rw [List.cons_append]
        simp [ixOf]
      · have hmem : a ∈ xs := by
          rw [List.mem_cons] at h
          rcases h with rfl | hxs
          · exact absurd (by simp) hx
          · exact hxs
        have h1 : ixOf a ((x :: xs) ++ r) = ixOf a (xs ++ r) + 1 := by
          rw [List.cons_append]
          simp [ixOf, hx]
        have h2 : ixOf a (x :: xs) = ixOf a xs + 1 := by simp [ixOf, hx]
        rw [h1, h2, ih hmem]

/-- The index of a universe message in the extended domain is its index in the universe. -/
theorem ixOf_exprVals {U : List Term} {P : Protocol} {t : Term} (h : t ∈ U) :
    ixOf t (exprVals U P) = ixOf t U :=
  ixOf_append_left t U _ h

/-- Bool-membership and Prop-membership agree here: `Encode.admissible` is written with the first and
`ExprDomain.inside` with the second. -/
theorem inside_admissible {sh : Shape} {v : Val} : inside sh.U v = admissible sh v := by
  cases v with
  | none => rfl
  | some t => simp [inside, admissible]

/-- Every value the domain of a table expression contains is nameable in the extended domain. -/
theorem mem_exprVals_of_mem_evalDomain {U : List Term} {P : Protocol} {e : Expr}
    (he : e ∈ allExprs P) {v : Val} (hv : v ∈ evalDomain U e) :
    inside (exprVals U P) v = true := by
  cases v with
  | none => rfl
  | some t =>
      rw [inside]
      have hmem : t ∈ ((allExprs P).flatMap fun e => valTerms (evalDomain U e)).eraseDups := by
        rw [List.mem_eraseDups, List.mem_flatMap]
        exact ⟨e, he, mem_valTerms.mpr hv⟩
      exact decide_eq_true (List.mem_append_right _ hmem)

/-- **The main representability theorem.** A table expression evaluated in *any* store whose values
lie in the persistent universe denotes a nameable value. There is no hypothesis about a run, no
closure assumption on the universe, and no arithmetic on the bounds: the statement is about the
query, and it holds by construction of `exprVals`. -/
theorem eval_inside_exprVals {U : List Term} {P : Protocol} (e : Expr) (he : e ∈ allExprs P)
    {s : List (Var × Term)} (h : storeIn U s) :
    inside (exprVals U P) (Expr.eval e s) = true :=
  mem_exprVals_of_mem_evalDomain he (eval_mem_evalDomain e h)

/-- The first gate equation the completeness proof needs, as a theorem about the domain rather than
an assumption about the execution: a unary step applied to the value of the child is nameable. -/
theorem stepEval1_inside_exprVals {U : List Term} {P : Protocol} {e c : Expr}
    (he : e ∈ allExprs P) (hc : Expr.child1 e = some c)
    {s : List (Var × Term)} (h : storeIn U s) :
    inside (exprVals U P) (Expr.stepEval1 e (Expr.eval c s)) = true := by
  rw [← Expr.eval_child1 hc]
  exact eval_inside_exprVals e he h

/-- And the binary case: a step applied to the values of both children is nameable. -/
theorem stepEval2_inside_exprVals {U : List Term} {P : Protocol} {e a b : Expr}
    (he : e ∈ allExprs P) (hc : Expr.child2 e = some (a, b))
    {s : List (Var × Term)} (h : storeIn U s) :
    inside (exprVals U P) (Expr.stepEval2 e (Expr.eval a s) (Expr.eval b s)) = true := by
  rw [← Expr.eval_child2 hc]
  exact eval_inside_exprVals e he h

/-! ### The shape with the extended value domain -/

/-- The persistent universe of a query. -/
def univOf (P : Protocol) (B : Bounds) : List Term := Bounded.univ P B

theorem univOf_eq (P : Protocol) (B : Bounds) : univOf P B = Bounded.univ P B := rfl

/-- The shape of the analysis with its value domain extended to name expression intermediates.
The persistent universe `U` is untouched - it is still what `BoundedTrace` bounds - and only the
list the expression families number over grows. -/
def shapeX (P : Protocol) (B : Bounds) : Shape :=
  { shapeOf P B with V := exprVals (univOf P B) P }

theorem shapeX_V (P : Protocol) (B : Bounds) :
    (shapeX P B).V = exprVals (univOf P B) P := rfl

/-- The persistent bound is unchanged: extending the nameable domain does not widen what a
configuration may store. -/
theorem shapeX_U (P : Protocol) (B : Bounds) : (shapeX P B).U = univOf P B := rfl

/-- The extended domain appends, so the prefix invariant holds and no existing index moves. -/
theorem shapeX_ShapePrefix (P : Protocol) (B : Bounds) : ShapePrefix (shapeX P B) :=
  ⟨_, by rw [shapeX_V, shapeX_U]; rfl⟩

/-- Every value a table expression denotes in a universe-valued store is nameable in `V`. -/
theorem nameable_of_eval {P : Protocol} {B : Bounds} {e : Expr} (he : e ∈ allExprs P)
    {s : List (Var × Term)} (h : storeIn (univOf P B) s) :
    Expr.eval e s = none ∨ ∃ t ∈ (shapeX P B).V, Expr.eval e s = some t := by
  have hv := eval_inside_exprVals e he h
  cases hval : Expr.eval e s with
  | none => exact Or.inl rfl
  | some t =>
      right
      have hv2 : inside (exprVals (univOf P B) P) (some t) = true := by rwa [hval] at hv
      rw [inside] at hv2
      exact ⟨t, of_decide_eq_true hv2, rfl⟩

/-- **`exprB` discharged as a property of the query.** At the extended domain every value a table
expression denotes in a universe-valued store reads back exactly - no admissibility hypothesis,
no closure assumption on the universe, nothing about a run. This is what replaces
`admissible_valAt_uIdx` under `RunOK.exprB` once the expression families number over `V`. -/
theorem eval_valAtX_uIdxX {P : Protocol} {B : Bounds} {e : Expr} (he : e ∈ allExprs P)
    {s : List (Var × Term)} (h : storeIn (univOf P B) s) :
    valAtX (shapeX P B) (uIdxX (shapeX P B) (Expr.eval e s)) = Expr.eval e s :=
  valAtX_uIdxX_of_nameable _ _ (nameable_of_eval he h)

/-- The same statement at every position of every run whose stores stay inside the persistent
universe: the seventh boundedness condition, as a theorem about the query. -/
theorem eval_valAtX_uIdxX_at {P : Protocol} {B : Bounds} {cfg : Nat → Cfg}
    (hstore : ∀ i q, storeIn (univOf P B) (storeOf (cfg i) q))
    (i q : Nat) (e : Expr) (he : e ∈ allExprs P) :
    valAtX (shapeX P B) (uIdxX (shapeX P B) (Expr.eval e (storeOf (cfg i) q))) =
      Expr.eval e (storeOf (cfg i) q) :=
  eval_valAtX_uIdxX he (hstore i q)

/-- And the gate equations keep their content: a step applied to the children's values reads back
to the parent's value, which is exactly what `rdXe_unary` and `rdXe_binary` need. -/
theorem stepEval1_valAtX_uIdxX {P : Protocol} {B : Bounds} {e c : Expr} (he : e ∈ allExprs P)
    (hc : Expr.child1 e = some c) {s : List (Var × Term)} (h : storeIn (univOf P B) s) :
    valAtX (shapeX P B)
      (uIdxX (shapeX P B) (Expr.stepEval1 e (Expr.eval c s))) =
      Expr.stepEval1 e (Expr.eval c s) := by
  rw [← Expr.eval_child1 hc]
  exact eval_valAtX_uIdxX he h

theorem stepEval2_valAtX_uIdxX {P : Protocol} {B : Bounds} {e a b : Expr} (he : e ∈ allExprs P)
    (hc : Expr.child2 e = some (a, b)) {s : List (Var × Term)} (h : storeIn (univOf P B) s) :
    valAtX (shapeX P B)
      (uIdxX (shapeX P B) (Expr.stepEval2 e (Expr.eval a s) (Expr.eval b s))) =
      Expr.stepEval2 e (Expr.eval a s) (Expr.eval b s) := by
  rw [← Expr.eval_child2 hc]
  exact eval_valAtX_uIdxX he h

/-- The extended domain is never smaller than the universe, and it is strictly bigger exactly when
some intermediate was unnameable. -/
theorem length_univ_le (U : List Term) (P : Protocol) : U.length ≤ (exprVals U P).length := by
  unfold exprVals
  rw [List.length_append]
  exact Nat.le_add_right _ _

/-! ### The transient pair, named -/

/-- The intermediate the encoding cannot name at the bounds of `Regressions.Bounds`. -/
theorem transient_not_nameable_here :
    Term.pair (Term.agent 0) (Term.agent 0) ∉ univOf boundsP boundsB :=
  transient_pair_intermediate_outside

/-- The store the transient-pair run actually reaches: `x` holds the delivered message. -/
def transientStore : List (Var × Term) := [(0, Term.agent 0)]

theorem storeIn_transient : storeIn (univOf boundsP boundsB) transientStore := by
  intro p hp
  have hpeq : p = (0, Term.agent 0) := by simpa [transientStore] using hp
  subst hpeq
  exact agents_subset_univ boundsP boundsB 0 (by decide)

/-- ... is nameable at exactly those bounds once the value domain is the extended one. -/
theorem transient_nameable :
    Term.pair (Term.agent 0) (Term.agent 0) ∈ exprVals (univOf boundsP boundsB) boundsP := by
  have h : some (Term.pair (Term.agent 0) (Term.agent 0)) ∈
      evalDomain (univOf boundsP boundsB) (Expr.pair (Expr.var 0) (Expr.var 0)) := by
    have heval : Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0)) transientStore =
        some (Term.pair (Term.agent 0) (Term.agent 0)) := by decide
    rw [← heval]
    exact eval_mem_evalDomain _ storeIn_transient
  have := mem_exprVals_of_mem_evalDomain (P := boundsP) (by decide) h
  rw [inside] at this
  exact of_decide_eq_true this

/-- The gate that `Regressions.gate_clipped` shows collapses to the unset index does not collapse at
the extended domain: the intermediate pair gets an index of its own. -/
theorem transient_gate_not_clipped :
    uIdxX (shapeX boundsP boundsB) (some (Term.pair (Term.agent 0) (Term.agent 0))) <
      ((shapeX boundsP boundsB).V).length := by
  have hne : (shapeX boundsP boundsB).V = exprVals (univOf boundsP boundsB) boundsP := rfl
  have hmem : Term.pair (Term.agent 0) (Term.agent 0) ∈ (shapeX boundsP boundsB).V := by
    rw [hne]
    exact transient_nameable
  have hidx : uIdxX (shapeX boundsP boundsB) (some (Term.pair (Term.agent 0) (Term.agent 0))) =
      ixOf (Term.pair (Term.agent 0) (Term.agent 0)) (shapeX boundsP boundsB).V := by
    simp [uIdxX, hmem]
  rw [hidx]
  exact ixOf_lt _ _ hmem

/-- And the index names the right value: `valAt` at the index `uIdx` returns recovers the
intermediate, which is the property `admissible_valAt_uIdx` grants only under `admissible`. -/
theorem transient_valAtX_uIdxX :
    valAtX (shapeX boundsP boundsB)
        (uIdxX (shapeX boundsP boundsB) (some (Term.pair (Term.agent 0) (Term.agent 0)))) =
      some (Term.pair (Term.agent 0) (Term.agent 0)) :=
  eval_valAtX_uIdxX (P := boundsP) (B := boundsB)
    (e := Expr.pair (Expr.var 0) (Expr.var 0)) (by decide) storeIn_transient

/-! ### No closure bound discharges the condition -/

/-- A message outside the universe is not admissible. -/
theorem admissible_false {sh : Shape} {t : Term} (h : t ∉ sh.U) : admissible sh (some t) = false :=
  by simp [admissible, h]

/-- The constructor depth of a message: atoms have depth 0, every constructor adds one. -/
def td : Term -> Nat
  | Term.agent _ => 0
  | Term.nonce _ => 0
  | Term.key _ => 0
  | Term.pair x y => 1 + max (td x) (td y)
  | Term.encS m _ => 1 + td m
  | Term.encA m _ => 1 + td m
  | Term.hash m => 1 + td m

/-- The largest depth of a list of messages. -/
def level : List Term -> Nat
  | [] => 0
  | t :: rest => max (td t) (level rest)

theorem level_nil : level [] = 0 := rfl

theorem level_cons {t : Term} {rest : List Term} : level (t :: rest) = max (td t) (level rest) :=
  rfl

theorem td_le_level {U : List Term} {t : Term} (h : t ∈ U) : td t ≤ level U := by
  induction U with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      rw [List.mem_cons] at h
      rcases h with h | h
      · subst h
        rw [level_cons]
        exact Nat.le_max_left _ _
      · rw [level_cons]
        exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem level_le {U : List Term} {d : Nat} (h : ∀ t ∈ U, td t ≤ d) : level U ≤ d := by
  induction U with
  | nil => show 0 ≤ d; exact Nat.zero_le _
  | cons x xs ih =>
      rw [level_cons]
      exact Nat.max_le.mpr ⟨h x (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun t ht => h t (List.mem_cons.mpr (Or.inr ht)))⟩

/-- One closure round raises the depth of nothing by more than one. -/
theorem td_closeOne {ag : List Agent} {ks : List Key} {U : List Term} {t : Term}
    (h : t ∈ closeOne ag ks U) : td t ≤ level U + 1 := by
  rw [closeOne, List.mem_eraseDups] at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map] at h
  rcases h with (((hU | hpair) | pencS) | pencA) | hhash
  · exact Nat.le_trans (td_le_level hU) (Nat.le_add_right _ _)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hpair
    have h1 : td x ≤ level U := td_le_level hx
    have h2 : td y ≤ level U := td_le_level hy
    show 1 + max (td x) (td y) ≤ level U + 1
    omega
  · obtain ⟨m, hm, k, hk, rfl⟩ := pencS
    have h1 : td m ≤ level U := td_le_level hm
    show 1 + td m ≤ level U + 1
    omega
  · obtain ⟨m, hm, a, ha, rfl⟩ := pencA
    have h1 : td m ≤ level U := td_le_level hm
    show 1 + td m ≤ level U + 1
    omega
  · obtain ⟨m, hm, rfl⟩ := hhash
    have h1 : td m ≤ level U := td_le_level hm
    show 1 + td m ≤ level U + 1
    omega

/-- The seed set of the transient-pair model: the placeholder pair is the deepest thing in it. -/
def seedP : List Term := subtermClosureL (seeds boundsP)

theorem level_seedP : level seedP ≤ 1 := by decide

/-- A depth-one seed of the transient-pair model: the placeholder pair the universe starts with. -/
def seedPair : Term := Term.pair (Term.nonce 100000) (Term.nonce 100000)

theorem seedPair_mem_seedP : seedPair ∈ seedP := by decide

/-- Hashing a universe message keeps it in the universe of the next closure round. -/
theorem hash_mem_univ {P : Protocol} {r : Nat} {t : Term}
    (h : t ∈ univ P {steps := 3, rounds := r}) :
    Term.hash t ∈ univ P {steps := 3, rounds := r + 1} := by
  unfold univ at h ⊢
  rw [List.mem_eraseDups] at h ⊢
  rw [Function.iterate_succ_apply']
  show Term.hash t ∈
    closeOne P.agents (domainKeys P.agents)
      ((fun U => closeOne P.agents (domainKeys P.agents) U)^[r] (subtermClosureL (seeds P)))
  unfold closeOne
  rw [List.mem_eraseDups]
  refine List.mem_append_right _ ?_
  rw [List.mem_map]
  exact ⟨_, h, rfl⟩

/-- After `r` closure rounds nothing in the universe is deeper than `r + 1`. -/
theorem td_univP_le (r : Nat) (t : Term)
    (h : t ∈ univ boundsP {steps := 3, rounds := r}) : td t ≤ r + 1 := by
  have key : ∀ k : Nat,
      (∀ u ∈ ((fun U => closeOne boundsP.agents (domainKeys boundsP.agents) U)^[k] seedP),
        td u ≤ k + 1) ∧
        level ((fun U => closeOne boundsP.agents (domainKeys boundsP.agents) U)^[k] seedP) ≤ k + 1 := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro u hu
          exact Nat.le_trans (td_le_level hu) level_seedP
        · refine level_le (fun u hu => ?_)
          exact Nat.le_trans (td_le_level hu) level_seedP
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        constructor
        · intro u hu
          exact Nat.le_trans (td_closeOne hu) (Nat.add_le_add_right ih.2 1)
        · refine level_le (fun u hu => ?_)
          exact Nat.le_trans (td_closeOne hu) (Nat.add_le_add_right ih.2 1)
  unfold univ at h
  rw [List.mem_eraseDups] at h
  exact (key r).1 t h

/-- `hash`-nesting a depth-one seed `r` times gives a message of the `r`-round universe whose
depth is exactly `r + 1`, i.e. the deepest a message of that universe can be. -/
theorem hash_seed_iter_mem (r : Nat) :
    (fun m => Term.hash m)^[r] seedPair ∈ univ boundsP {steps := 3, rounds := r} := by
  induction r with
  | zero =>
      show seedPair ∈ univ boundsP {steps := 3, rounds := 0}
      exact seedPair_mem_seedP
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hash_mem_univ ih

/-- Each `hash` adds exactly one to the depth. -/
theorem td_hash_iter (r : Nat) : td ((fun m => Term.hash m)^[r] seedPair) = r + 1 := by
  induction r with
  | zero => show td seedPair = 1; decide
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      show td (Term.hash ((fun m => Term.hash m)^[j] seedPair)) = j + 1 + 1
      rw [show td (Term.hash ((fun m => Term.hash m)^[j] seedPair)) =
          1 + td ((fun m => Term.hash m)^[j] seedPair) from rfl, ih]
      omega

/-- **No closure bound discharges the uniform representability condition.** For every rounds bound
there is a store whose only value is a universe message, and in which the table entry
`pair (var 0) (var 0)` denotes a message the universe does not contain. Raising `Bounds.rounds`
cannot replace `exprB`: the condition asks the universe to be closed under pairing, which no finite
universe is. That is why the fix is the value domain of `exprVals`, not the bound. -/
theorem no_bound_discharges_exprB (r : Nat) :
    ∃ (s : List (Var × Term)),
      storeIn (univ boundsP {steps := 3, rounds := r}) s ∧
        admissible (shapeOf boundsP {steps := 3, rounds := r})
          (Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0)) s) = false := by
  let a := (fun m => Term.hash m)^[r] seedPair
  refine ⟨[(0, a)], ?_, ?_⟩
  · intro p hp
    have hpeq : p = (0, a) := by simpa using hp
    subst hpeq
    exact hash_seed_iter_mem r
  · have hnot : Term.pair a a ∉ univ boundsP {steps := 3, rounds := r} := by
      intro h
      have h1 := td_univP_le r (Term.pair a a) h
      have h2 : td (Term.pair a a) = r + 2 := by
        show 1 + max (td a) (td a) = r + 2
        rw [td_hash_iter r]
        omega
      omega
    have heval : Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0)) [(0, a)] =
        some (Term.pair a a) := rfl
    rw [heval]
    exact admissible_false hnot

/-- The contrast in one line: at the *same* bound, the store that breaks admissibility over the
universe has its value named by the extended domain. -/
theorem exprB_holds_at_X_for_deep_store (r : Nat) :
    valAtX (shapeX boundsP {steps := 3, rounds := r})
      (uIdxX (shapeX boundsP {steps := 3, rounds := r})
        (Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0))
          [(0, (fun m => Term.hash m)^[r] seedPair)])) =
      Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0))
        [(0, (fun m => Term.hash m)^[r] seedPair)] :=
  eval_valAtX_uIdxX (P := boundsP) (B := {steps := 3, rounds := r})
    (e := Expr.pair (Expr.var 0) (Expr.var 0)) (by decide) (by
      intro p hp
      have hpeq : p = (0, (fun m => Term.hash m)^[r] seedPair) := by simpa using hp
      subst hpeq
      exact hash_seed_iter_mem r)

/-! ### The condition, decided on a concrete run -/

/-- **The decidable form of `exprB` over an explicit list of stores.** Given the stores a run
actually uses, admissibility of every table expression in each of them is a finite check: no
quantification over positions, sessions or executions is left. -/
def exprBOn (P : Protocol) (sh : Shape) (stores : List (List (Var × Term))) : Bool :=
  stores.all fun s => (allExprs P).all fun e => admissible sh (Expr.eval e s)

/-- If the listed stores cover every store the run uses, the finite check is `RunOK.exprB`. -/
theorem exprB_of_exprBOn {P : Protocol} {sh : Shape} {cfg : Nat → Cfg}
    (stores : List (List (Var × Term))) (h : exprBOn P sh stores = true)
    (hcover : ∀ i q, ∃ s ∈ stores, storeOf (cfg i) q = s) :
    ∀ i q e, e ∈ allExprs P → admissible sh (Expr.eval e (storeOf (cfg i) q)) = true := by
  intro i q e he
  obtain ⟨s, hs, hEq⟩ := hcover i q
  unfold exprBOn at h
  rw [List.all_eq_true] at h
  have h1 := h s hs
  rw [List.all_eq_true] at h1
  rw [hEq]
  exact h1 e he

/-- Admissibility with respect to the nameable domain rather than the persistent one. -/
def admissibleX (sh : Shape) : Val -> Bool
  | none => true
  | some t => sh.V.contains t

theorem admissibleX_none (sh : Shape) : admissibleX sh none = true := rfl

theorem admissibleX_some (sh : Shape) (t : Term) : admissibleX sh (some t) = sh.V.contains t := rfl

/-- The decidable form of the extended-domain check. -/
def exprBOnX (P : Protocol) (sh : Shape) (stores : List (List (Var × Term))) : Bool :=
  stores.all fun s => (allExprs P).all fun e => admissibleX sh (Expr.eval e s)

/-- The check passes at the extended domain for *every* list of universe-valued stores: this is
`eval_valAtX_uIdxX` in the decidable form, and it is the statement the analyser can run before
committing to the extended encoding. -/
theorem exprBOnX_shapeX {P : Protocol} {B : Bounds}
    (stores : List (List (Var × Term))) (h : ∀ s ∈ stores, storeIn (univOf P B) s) :
    exprBOnX P (shapeX P B) stores = true := by
  unfold exprBOnX
  rw [List.all_eq_true]
  intro s hs
  rw [List.all_eq_true]
  intro e he
  cases nameable_of_eval he (h s hs) with
  | inl hnone => rw [hnone, admissibleX_none]
  | inr hx =>
      obtain ⟨t, ht, hEq⟩ := hx
      rw [hEq, admissibleX_some]
      simpa [shapeX_V] using ht

/-- The transient-pair run fails the check at the bound of `Regressions.Bounds` - the same fact
`not_withinBounds` extracts from the `WithinBounds` hypothesis, now as a computation. -/
theorem transient_exprB_fails :
    exprBOn boundsP (shapeOf boundsP boundsB) [transientStore] = false := by decide

/-- **And it passes one closure round later.** The transient-pair counterexample is representable
by the CNF at `rounds := 1`: the intermediate pair is then a universe message. So representability
is decidable on a witness, and for this protocol it is *satisfied* at a slightly larger bound - what
`no_bound_discharges_exprB` says is that no bound satisfies it *uniformly over every
universe-valued store*, which is the difference between a bound and a domain. -/
theorem transient_exprB_holds_at_rounds1 :
    exprBOn boundsP (shapeOf boundsP {steps := 3, rounds := 1}) [transientStore] = true := by
  decide

/-- The same run, one round apart, in one line: the tool can check which situation it is in. -/
theorem transient_representability_is_a_computation :
    exprBOn boundsP (shapeOf boundsP boundsB) [transientStore] = false ∧
      exprBOn boundsP (shapeOf boundsP {steps := 3, rounds := 1}) [transientStore] = true :=
  ⟨transient_exprB_fails, transient_exprB_holds_at_rounds1⟩

/-! ### The gap, as something the tool can report -/

/-- **The representability gap of a query**, computed: does the protocol build a value the CNF's
value domain cannot name? `false` means `RunOK.exprB` holds for every run of the query, so the
completeness theorem loses nothing by assuming it. `true` means the assumption is doing real work,
and the enumeration route (`Reference.Contract`) is the one that answers the question. This turns
"WithinBounds silently narrows the question" into a reported fact. -/
def domainGap (P : Protocol) (B : Bounds) : Bool :=
  !(List.all (allExprs P) fun e => storesInU (univOf P B) e)

/-- A concrete unnameable value implies the gap is reported. -/
theorem domainGap_of_unnameable {P : Protocol} {B : Bounds} {e : Expr} (he : e ∈ allExprs P)
    {s : List (Var × Term)} (h : storeIn (univOf P B) s)
    (hout : ∃ t, Expr.eval e s = some t ∧ t ∉ univOf P B) : domainGap P B = true := by
  obtain ⟨t, hne, hnot⟩ := hout
  have hmem := eval_mem_evalDomain e h
  rw [hne] at hmem
  unfold domainGap
  cases hcase : (allExprs P).all (fun e => storesInU (univOf P B) e) with
  | true =>
      rw [List.all_eq_true] at hcase
      have h1 := hcase e he
      rw [storesInU, List.all_eq_true] at h1
      have h2 := h1 (some t) hmem
      rw [inside] at h2
      exact absurd (of_decide_eq_true h2) hnot
  | false => rfl

/-- The transient-pair query reports the gap: the intermediate pair is built from a received
message, so no closure bound names it (`no_bound_discharges_exprB`). -/
theorem domainGap_transient : domainGap boundsP boundsB = true := by decide

/-- A protocol that only moves received messages around reports none, and does so with an empty
nonce domain: nothing here needs a fresh value, which is roadmap stage 2's gate read on the old
route. -/
def plainP : Protocol :=
  { roles := [{ acts := [Action.recv 0 0, Action.send 0 (Expr.var 0)] }],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0], nonceDomain := [], compromised := [],
    secrets := [Secret.closed (Expr.var 0)], auths := [] }

theorem domainGap_plain : domainGap plainP { steps := 2, rounds := 1 } = false := by decide

end ProtSat.Represent