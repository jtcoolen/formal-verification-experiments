/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Bounded

/-!
# ProtSat: finite domains for expression intermediates (roadmap stage 3)

## The problem this solves

A finite message universe cannot be closed under the protocol's own constructors: for any finite
`U` there is an `x in U` with `pair x x not in U`. The encoding handles this by *clipping*:
`Encode.uIdx` maps every value outside the universe to the "unset" index, so a gate over
`pair x x` records no value, and `Complete.RunOK.exprB` then demands that no protocol expression
denote an out-of-universe value in any store of the run. That demand is what makes
`Complete.encoding_complete` conditional, and `ProtSat.Regressions.Bounds` shows it is a real
restriction: the protocol

`@
recv x;  check (fst (pair x x)) x;  send K
`@

is a perfectly good bounded execution - `fst (pair x x)` really is `x`, which is in the universe -
and yet `WithinBounds` fails for it, so the CNF is not obliged to have a model for it, and it has
none.

## The fix

Separate the two things that were conflated:

* **persistent values** - what a configuration stores, publishes, or declares secret. These stay
  bounded by the universe `U`, and that bound is a modelling choice the user makes;
* **intermediate values** - what an expression computes on the way to its result. These get their own
  finite domain, `evalDomain U e`, built compositionally from the domains of `e`'s children and
  never clipped to `U`.

The main theorem says the reference evaluator cannot leave the domain:

`@lean
ExprDomain.eval_mem_evalDomain : storeIn U s -> Expr.eval e s in evalDomain U e
`@

so an expression whose *result* is in `U` is admissible even when its intermediates are not.
`transient_pair_intermediate_outside`, `transient_pair_result_in_domain` and
`transient_pair_stores_in_U` hold simultaneously, which is exactly what the encoding could not
express.
-/

namespace ProtSat.ExprDomain

open ProtSat Term Protocol Bounded

/-- A value is inside the universe if it is nothing, or a message of the universe. -/
def inside (U : List Term) (v : Val) : Bool :=
  match v with
  | none => true
  | some t => t ∈ U

/-- A store is universe-valued. -/
def storeIn (U : List Term) (s : List (Var × Term)) : Prop :=
  ∀ p ∈ s, p.2 ∈ U

/-- A successful lookup returns a value the store holds. -/
theorem some_mem_of_lookup {x : Var} {s : List (Var × Term)} {t : Term}
    (h : Expr.lookup x s = some t) : ∃ p ∈ s, p.2 = t := by
  induction s with
  | nil => exact absurd h (by simp [Expr.lookup])
  | cons p rest ih =>
      unfold Expr.lookup at h
      by_cases hp : p.1 = x
      · rw [if_pos hp] at h
        cases h
        exact ⟨p, List.mem_cons.mpr (Or.inl rfl), rfl⟩
      · rw [if_neg hp] at h
        obtain ⟨q, hq, rfl⟩ := ih h
        exact ⟨q, List.mem_cons.mpr (Or.inr hq), rfl⟩

/-- Every value a universe-valued store can return is inside the universe. -/
theorem inside_lookup {U : List Term} {s : List (Var × Term)} (h : storeIn U s)
    {x : Var} {v : Val} (hv : Expr.lookup x s = v) : inside U v = true := by
  cases v with
  | none => rfl
  | some t =>
      rw [inside]
      obtain ⟨p, hp, hpt⟩ := some_mem_of_lookup hv
      rw [← hpt]
      exact decide_eq_true (h p hp)

/-! ### The domain construction -/

/-- The Cartesian image of two lists under a binary operation. -/
def vprod (f : Val -> Val -> Val) : List Val -> List Val -> List Val
  | [], _ => []
  | x :: xs, l => (l.map (f x)) ++ vprod f xs l

theorem mem_vprod {f : Val -> Val -> Val} {l₁ l₂ : List Val} {v : Val} :
    v ∈ vprod f l₁ l₂ <-> ∃ x ∈ l₁, ∃ y ∈ l₂, f x y = v := by
  induction l₁ with
  | nil =>
      constructor
      · intro h; exact absurd h (by simp [vprod])
      · rintro ⟨x, hx, y, hy, rfl⟩; exact absurd hx (by simp)
  | cons a as ih =>
      rw [vprod, List.mem_append]
      constructor
      · intro h
        rcases h with h | h
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
          exact ⟨a, List.mem_cons.mpr (Or.inl rfl), y, hy, rfl⟩
        · obtain ⟨x, hx, y, hy, rfl⟩ := ih.mp h
          exact ⟨x, List.mem_cons.mpr (Or.inr hx), y, hy, rfl⟩
      · rintro ⟨x, hx, y, hy, rfl⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · left
          exact List.mem_map.mpr ⟨y, hy, rfl⟩
        · right
          exact ih.mpr ⟨x, hx, y, hy, rfl⟩

/-- The image of a list of values under a one-step unary operation, with failure included. -/
def vmap1 (e : Expr) (l : List Val) : List Val := none :: (l.map (Expr.stepEval1 e)).eraseDups

/-- The image of two lists of values under a one-step binary operation, with failure included. -/
def vmap2 (e : Expr) (l₁ l₂ : List Val) : List Val :=
  none :: (vprod (Expr.stepEval2 e) l₁ l₂).eraseDups

theorem mem_vmap1 {e : Expr} {l : List Val} {v : Val} :
    v ∈ vmap1 e l <-> v = none ∨ ∃ x ∈ l, Expr.stepEval1 e x = v := by
  rw [vmap1, List.mem_cons]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp h)
      exact Or.inr ⟨x, hx, rfl⟩
  · rintro (h | ⟨x, hx, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩))

theorem mem_vmap2 {e : Expr} {l₁ l₂ : List Val} {v : Val} :
    v ∈ vmap2 e l₁ l₂ <-> v = none ∨ ∃ x ∈ l₁, ∃ y ∈ l₂, Expr.stepEval2 e x y = v := by
  rw [vmap2, List.mem_cons]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨x, hx, y, hy, rfl⟩ := mem_vprod.mp (List.mem_eraseDups.mp h)
      exact Or.inr ⟨x, hx, y, hy, rfl⟩
  · rintro (h | ⟨x, hx, y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (List.mem_eraseDups.mpr (mem_vprod.mpr ⟨x, hx, y, hy, rfl⟩))

/-- **The finite domain of an expression** over the universe `U`: every value the expression can
denote in a universe-valued store, plus `none` for the stores in which it is stuck. Constructors and
destructors take the image of their children's domains, so nothing is clipped to `U` on the way. -/
def evalDomain (U : List Term) : Expr -> List Val
  | Expr.agent A => [some (Term.agent A)]
  | Expr.nonce N => [some (Term.nonce N)]
  | Expr.shrk a b => [some (Term.key (Key.shrk a b))]
  | Expr.pubk a => [some (Term.key (Key.pub a))]
  | Expr.privk a => [some (Term.key (Key.priv a))]
  | Expr.var x => none :: (U.map some)
  | e@(Expr.pair a b) => vmap2 e (evalDomain U a) (evalDomain U b)
  | e@(Expr.encS a b) => vmap2 e (evalDomain U a) (evalDomain U b)
  | e@(Expr.decS a b) => vmap2 e (evalDomain U a) (evalDomain U b)
  | e@(Expr.encA a n) => vmap1 e (evalDomain U a)
  | e@(Expr.decA a n) => vmap1 e (evalDomain U a)
  | e@(Expr.hash a) => vmap1 e (evalDomain U a)
  | e@(Expr.fst a) => vmap1 e (evalDomain U a)
  | e@(Expr.snd a) => vmap1 e (evalDomain U a)

/-- **Soundness of the domain.** Evaluating an expression in a universe-valued store yields a value
of its domain. The universe need not be closed under any constructor. -/
theorem eval_mem_evalDomain {U : List Term} (e : Expr) {s : List (Var × Term)}
    (h : storeIn U s) : Expr.eval e s ∈ evalDomain U e := by
  induction e with
  | agent A => simp [evalDomain, Expr.eval]
  | nonce N => simp [evalDomain, Expr.eval]
  | shrk a b => simp [evalDomain, Expr.eval]
  | pubk a => simp [evalDomain, Expr.eval]
  | privk a => simp [evalDomain, Expr.eval]
  | var x =>
      unfold evalDomain
      rw [Expr.eval]
      rcases hv : Expr.lookup x s with _ | t
      · simp [hv]
      · right
        obtain ⟨p, hp, hpt⟩ := some_mem_of_lookup hv
        have ht : t ∈ U := by rw [← hpt]; exact h p hp
        exact List.mem_map.mpr ⟨t, ht, rfl⟩
  | pair a b ih₁ ih₂ =>
      rw [Expr.eval_child2 (s := s) (show Expr.child2 (Expr.pair a b) = some (a, b) from rfl)]
      unfold evalDomain
      rw [mem_vmap2]
      right
      exact ⟨_, ih₁, _, ih₂, rfl⟩
  | encS a b ih₁ ih₂ =>
      rw [Expr.eval_child2 (s := s) (show Expr.child2 (Expr.encS a b) = some (a, b) from rfl)]
      unfold evalDomain
      rw [mem_vmap2]
      right
      exact ⟨_, ih₁, _, ih₂, rfl⟩
  | decS a b ih₁ ih₂ =>
      rw [Expr.eval_child2 (s := s) (show Expr.child2 (Expr.decS a b) = some (a, b) from rfl)]
      unfold evalDomain
      rw [mem_vmap2]
      right
      exact ⟨_, ih₁, _, ih₂, rfl⟩
  | encA a n ih =>
      rw [Expr.eval_child1 (s := s) (show Expr.child1 (Expr.encA a n) = some a from rfl)]
      unfold evalDomain
      rw [mem_vmap1]
      right
      exact ⟨_, ih, rfl⟩
  | decA a n ih =>
      rw [Expr.eval_child1 (s := s) (show Expr.child1 (Expr.decA a n) = some a from rfl)]
      unfold evalDomain
      rw [mem_vmap1]
      right
      exact ⟨_, ih, rfl⟩
  | hash a ih =>
      rw [Expr.eval_child1 (s := s) (show Expr.child1 (Expr.hash a) = some a from rfl)]
      unfold evalDomain
      rw [mem_vmap1]
      right
      exact ⟨_, ih, rfl⟩
  | fst a ih =>
      rw [Expr.eval_child1 (s := s) (show Expr.child1 (Expr.fst a) = some a from rfl)]
      unfold evalDomain
      rw [mem_vmap1]
      right
      exact ⟨_, ih, rfl⟩
  | snd a ih =>
      rw [Expr.eval_child1 (s := s) (show Expr.child1 (Expr.snd a) = some a from rfl)]
      unfold evalDomain
      rw [mem_vmap1]
      right
      exact ⟨_, ih, rfl⟩

/-! ### The admissibility criteria -/

/-- **The persistent bound**: an action that stores or publishes the value of `e` is admissible when
every value `e` can denote is inside the universe. -/
def storesInU (U : List Term) (e : Expr) : Bool := (evalDomain U e).all (inside U)

/-- If the domain of `e` lies inside the universe, so does every value `e` denotes in a
universe-valued store. -/
theorem inside_of_storesInU {U : List Term} {e : Expr} (h : storesInU U e = true)
    {s : List (Var × Term)} (hs : storeIn U s) : inside U (Expr.eval e s) = true := by
  have hmem := eval_mem_evalDomain e hs
  rw [storesInU, List.all_eq_true] at h
  exact h _ hmem

/-! ### The transient pair, handled -/

/-- The model of `ProtSat.Regressions.Bounds`: receive a message, test
`fst (pair x x) = x`, publish a declared secret. -/
def boundsP : Protocol :=
  { roles := [{ acts := [Action.recv 0 0,
      Action.check (Expr.fst (Expr.pair (Expr.var 0) (Expr.var 0))) (Expr.var 0),
      Action.send 0 (Expr.shrk 0 0)] }],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0], nonceDomain := [0], compromised := [],
    secrets := [Secret.closed (Expr.shrk 0 0)], auths := [] }

def boundsB : Bounds := { steps := 3, rounds := 0 }

/-- The universe of that model, spelled out so the kernel can reduce over it. -/
def U0 : List Term :=
  [Term.agent 0, Term.nonce 0, Term.key (Key.pub 0), Term.key (Key.priv 0),
    Term.key (Key.shrk 0 0), Term.nonce 100000,
    Term.pair (Term.nonce 100000) (Term.nonce 100000)]

/-- This really is the universe the bounds generate. -/
theorem U0_eq : Bounded.univ boundsP boundsB = U0 := by decide

/-- The expression at the centre of the counterexample. -/
def transient : Expr := Expr.fst (Expr.pair (Expr.var 0) (Expr.var 0))

/-- The intermediate pair, evaluated at the store the run actually reaches, is outside the universe.
This is what `RunOK.exprB` refuses. -/
theorem transient_pair_intermediate_outside :
    Term.pair (Term.agent 0) (Term.agent 0) ∉ U0 := by decide

/-- The result is inside the universe, and it is the value the reference evaluator computes. -/
theorem transient_pair_result_in_domain :
    Expr.eval transient [(0, Term.agent 0)] = some (Term.agent 0) ∧
      some (Term.agent 0) ∈ evalDomain U0 transient := by
  exact ⟨by decide, by decide⟩

/-- And the storing criterion is met: every value the expression can denote is inside the universe,
even though an intermediate value is not. -/
theorem transient_pair_stores_in_U : storesInU U0 transient = true := by decide

/-- The contrast in one line: the intermediate value is *not* inside the universe, so a bound that
quantifies over every value an expression touches would reject the action... -/
theorem transient_intermediate_not_inside :
    inside U0 (Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0)) [(0, Term.agent 0)]) = false := by
  decide

/-- ...while a bound on what the action *yields* accepts it. This pair of theorems is the whole of
roadmap stage 3's gate: the transient-pair counterexample is representable, and the persistent bound
still excludes any action that really did store or publish an out-of-universe message. -/
theorem transient_bounds_agree :
    storesInU U0 transient = true ∧
      inside U0 (Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0)) [(0, Term.agent 0)]) = false :=
  ⟨transient_pair_stores_in_U, transient_intermediate_not_inside⟩

/-- The check action is genuinely enabled: both sides denote the same value. -/
theorem transient_check_enabled :
    Expr.eval transient [(0, Term.agent 0)] = Expr.eval (Expr.var 0) [(0, Term.agent 0)] := by
  decide

/-- The declared secret the run publishes *is* in the universe, so the persistent bound does not
exclude the attack either: the run is bounded, and the CNF still has no model for it. -/
theorem transient_secret_in_U :
    Term.key (Key.shrk 0 0) ∈ U0 ∧ Expr.eval (Expr.shrk 0 0) [] =
      some (Term.key (Key.shrk 0 0)) := by
  exact ⟨by decide, by decide⟩

end ProtSat.ExprDomain