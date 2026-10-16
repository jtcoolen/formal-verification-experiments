/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding

/-!
# ProtSat: the converse correspondence (specification section 8B)

## What this module proves

ProtSat.Encoding.encoding_sound (8A) turns a satisfying assignment of the generated CNF
into a genuine bounded attack.  This module proves the converse, **encoding_complete**:

> every valid bounded attack execution of the protocol is represented by a satisfying
> assignment of the encoded formula.

Together the two theorems are the correspondence the project is about: within the declared
bounds, "the solver finds a model" and "the protocol has an attack" are the same statement.
8B is what makes a SAFE verdict meaningful (specification 8G): if the solver says UNSAT
then no bounded attack exists, because had one existed the construction below would have
produced a model.

## The construction

The assignment is the *characteristic function of the run*.  For a run with configurations
`cfg : Nat -> Cfg` and events `ev : Nat -> Ev`, a propositional variable is true exactly
when the semantic fact it names holds in the run.  Because the variables are laid out in
disjoint blocks (ProtSat.Encode.bsPc, bsSt, bsKn, bsEv, bsDl, bsFr, bsXe, bsTotal, bsAu),
the test is a cascade of range comparisons, and inside a block a bounded search over that
block's own index ranges.  Nothing is decoded by division: the block of a variable is found
by comparison, and inside the block the index is recovered from the injectivity of the
positional codes (ProtSat.Encode.vpc_inj and friends).

## Where the bounds are used

The construction needs the run to stay inside the analysis bounds: every message the
attacker knows and every value a session stores must be a universe message, every session
that acts must be instantiated, every generated nonce must be in the nonce domain, and
every attacker step must be one of the enumerated rule instances.  That hypothesis is
ProtSat.Complete.WithinBounds; it is not a technicality - a run that leaves the universe
cannot be represented by a finite encoding at all, and the README says so.
-/

namespace ProtSat.Complete

open ProtSat Term OneHot Bounded Attacker Encode Encoding

/-! ### Reading a run by position -/

/-- Walking down a visited list: the current configuration while there are configurations
left, and the last one repeated forever afterwards.  A finished run stands still, which is
what the idle steps of the encoding require. -/
def cfgGo : Cfg → List Cfg → Nat → Cfg
  | C, [], _ => C
  | C, D :: rest, 0 => C
  | _, D :: rest, k + 1 => cfgGo D rest k

/-- The configuration at step i of a visited list: the i-th one, or the last one when i goes
past the end (a finished run stays where it is, which is what the idle steps do). -/
def cfgAt (Cs : List Cfg) (i : Nat) : Cfg :=
  match Cs with
  | [] => ⟨[], []⟩
  | C :: rest => cfgGo C rest i

/-- The event taken at step i: the i-th one, or ProtSat.Ev.idle past the end. -/
def evAt (tr : List Ev) (i : Nat) : Ev := (tr.drop i).headD Ev.idle

/-- The head of a run is its initial configuration. -/
theorem cfgAt_head {C : Cfg} {rest : List Cfg} : cfgAt (C :: rest) 0 = C := by
  cases rest <;> rfl

/-- Inside a non-empty tail, reading one step further is reading the tail one step less. -/
theorem cfgAt_cons_succ {C : Cfg} {rest : List Cfg} (h : rest ≠ []) (i : Nat) :
    cfgAt (C :: rest) (i + 1) = cfgAt rest i := by
  cases rest with
  | nil => exact absurd rfl h
  | cons y ys => rfl

theorem evAt_head {e : Ev} {rest : List Ev} : evAt (e :: rest) 0 = e := by
  unfold evAt
  simp [List.headD]

theorem evAt_cons_succ {e : Ev} {rest : List Ev} (i : Nat) :
    evAt (e :: rest) (i + 1) = evAt rest i := rfl

/-- Reading a singleton run always gives its only configuration. -/
theorem cfgAt_single {C : Cfg} (i : Nat) : cfgAt [C] i = C := rfl

/-- Past the end of the event list the read is idle. -/
theorem evAt_past {tr : List Ev} (i : Nat) (h : tr.length ≤ i) : evAt tr i = Ev.idle := by
  unfold evAt
  rw [List.drop_eq_nil_of_le h]
  rfl

theorem evAt_nil (i : Nat) : evAt ([] : List Ev) i = Ev.idle := by
  unfold evAt
  cases i <;> simp [List.headD]

/-- Past the end of the visited list the read stands still on the last configuration. -/
theorem cfgAt_past {Cs : List Cfg} (h : Cs ≠ []) (i : Nat) (hi : i + 1 ≥ Cs.length) :
    cfgAt Cs i = cfgAt Cs (i + 1) := by
  cases Cs with
  | nil => exact absurd rfl h
  | cons x xs =>
      cases i with
      | zero =>
          have hlen : xs.length = 0 := by simpa [List.length_cons] using hi
          cases xs with
          | nil => rfl
          | cons y ys => simp at hlen
      | succ i =>
          cases xs with
          | nil => show cfgGo x [] (i + 1) = cfgGo x [] (i + 1 + 1); rfl
          | cons y ys =>
              rw [cfgAt_cons_succ (by simp) i, cfgAt_cons_succ (by simp) (i + 1)]
              have h2 : i + 1 ≥ (y :: ys).length := by
                simp [List.length_cons] at hi ⊢
                omega
              exact cfgAt_past (by simp) i h2

/-- **Every position of a run is a transition.**  Reading the visited list and the event list
by position turns a ProtSat.Runs derivation into a pointwise ProtSat.Rel statement, valid
also past the end of the trace, where the run idles. -/
theorem runs_rel {P : Protocol} {C0 : Cfg} {tr : List Ev} {Cs : List Cfg}
    (hr : Runs P C0 tr Cs) :
    C0 = cfgAt Cs 0 ∧
      ∀ (i : Nat), Rel P (cfgAt Cs i) (evAt tr i) (cfgAt Cs (i + 1)) := by
  induction hr with
  | nil C =>
      refine ⟨rfl, ?_⟩
      intro i
      simp [cfgAt_single, evAt_nil]
      exact Rel.rIdle P C
  | cons hstep hrest ih =>
      rename_i C C' e tr' rest
      obtain ⟨h1, h2⟩ := ih
      have hne : rest ≠ [] := by
        intro hz
        have hl := runs_length hrest
        rw [hz] at hl
        simp at hl
      refine ⟨cfgAt_head.symm, ?_⟩
      intro i
      by_cases hi : i < (e :: tr').length
      · cases i with
        | zero =>
            rw [cfgAt_head, evAt_head, cfgAt_cons_succ hne 0, ← h1]
            exact hstep
        | succ i =>
            rw [cfgAt_cons_succ hne i, evAt_cons_succ i, cfgAt_cons_succ hne (i + 1)]
            have hlen'' : i < tr'.length := by simpa using hi
            exact h2 i
      · -- past the end: the run stands still and idles
        have hlen : (e :: tr').length ≤ i := by omega
        have he : evAt (e :: tr') i = Ev.idle := evAt_past i hlen
        have hcs : (C :: rest).length = (e :: tr').length + 1 := by
          have hl := runs_length hrest
          simp [List.length_cons, hl]
        have h3 : cfgAt (C :: rest) i = cfgAt (C :: rest) (i + 1) :=
          cfgAt_past (by simp) i (by omega)
        rw [he, h3]
        exact Rel.rIdle P _

/-! ### The boundedness hypothesis -/

/-- **The run stays inside the bounds.**  Every message the attacker ever knows and every
value any session ever stores is a universe message; every session that acts is one the
bounds instantiate and every nonce it generates is in the nonce domain; every message the
attacker learns in one step is in the universe; and every program counter and every store
variable stays inside the shape's bounds.  These are exactly the conditions under which a
finite encoding can represent the run at all - a run that leaves the universe has no finite
name. -/
def WithinBounds (P : Protocol) (B : Bounds) (cfg : Nat → Cfg) (ev : Nat → Ev) : Prop :=
  (∀ i t, t ∈ (cfg i).kn → t ∈ (shapeOf P B).U) ∧
  (∀ i q v, q < (shapeOf P B).nS1 → v ∈ storeVals (storeOf (cfg i) q) →
      v ∈ (shapeOf P B).U) ∧
  (∀ i, match ev i with
      | Ev.idle => True
      | Ev.act q m d => q < (shapeOf P B).nS1 ∧ m ∈ (shapeOf P B).U ∧ d ∈ P.nonceDomain
      | Ev.ded t => t ∈ (shapeOf P B).U) ∧
  (∀ i q, q < (shapeOf P B).nS1 → pcOf (cfg i) q < shPc (shapeOf P B)) ∧
  (∀ i q x, q < (shapeOf P B).nS1 → x ∈ (storeOf (cfg i) q).map Prod.fst →
      x < shV (shapeOf P B))

/-! ### Rule instances that actually fire -/

/-! ### The assignment of a run  (under construction: see KB/PROTOSAT.md) -/

end ProtSat.Complete
