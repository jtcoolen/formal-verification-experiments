/-
# Dijkstra's algorithm

A terminating, purely functional implementation of Dijkstra's algorithm on a finite
directed graph with `ℕ` weights.

The state holds

* `dist : V → WithTop ℕ` — tentative distances (`⊤ = ∞` means "not yet known");
* `pred : V → Option V` — predecessor pointers for path reconstruction;
* `order : List V` — the finalized vertices, oldest first.

One *step* selects the unvisited vertex with the smallest finite tentative distance
(ties broken by the fixed `LinearOrder` on `V`), relaxes all arcs leaving it, and
finalizes it.  The step returns `none` exactly when no reachable unvisited vertex is
left, which is the usual termination condition.  The loop is written with a decreasing
natural-number fuel bound (`Fintype.card V`), so it is structurally terminating; in
`Dijkstra/Correctness.lean` we prove that this bound is always large enough, i.e. that
the loop really does run to completion on every finite graph.

Selection uses a finite-set minimum scan rather than a binary heap; the brief allows
this, and it keeps the correctness proof independent of heap bookkeeping.
-/
import Mathlib
import Dijkstra.Paths

set_option linter.unusedSectionVars false

universe u

namespace Dijkstra

/-- The state of Dijkstra's algorithm. -/
structure State (V : Type u) where
  /-- Tentative distances; `⊤` means "no path found so far". -/
  dist : V → WithTop Nat
  /-- Predecessor pointers, used to reconstruct shortest paths. -/
  pred : V → Option V
  /-- Finalized ("visited") vertices, in the order they were finalized (oldest first). -/
  order : List V

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace State

/-- `st.visited v` means that `v` has been finalized. -/
def visited (st : State V) (v : V) : Prop := v ∈ st.order

/-- The unvisited vertices with a finite tentative distance. -/
def candidates (st : State V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ st.order ∧ st.dist v ≠ ⊤)

theorem mem_candidates {st : State V} {v : V} :
    v ∈ st.candidates ↔ ¬ st.visited v ∧ st.dist v ≠ ⊤ := by
  simp [candidates, visited]

theorem candidates_nonempty_of {st : State V} {v : V}
    (hv : ¬ st.visited v) (hd : st.dist v ≠ ⊤) : st.candidates.Nonempty :=
  Finset.filter_nonempty_iff.mpr ⟨v, Finset.mem_univ v, by simpa [visited] using hv, hd⟩

/-- The smallest tentative distance among the candidates. -/
def minCandidateDist (st : State V) (h : st.candidates.Nonempty) : WithTop Nat :=
  (st.candidates.image st.dist).min' (h.image st.dist)

theorem minCandidateDist_le (st : State V) (h : st.candidates.Nonempty) (x : V)
    (hx : x ∈ st.candidates) : minCandidateDist st h ≤ st.dist x := by
  unfold minCandidateDist
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

theorem minCandidateDist_attained (st : State V) (h : st.candidates.Nonempty) :
    ∃ v ∈ st.candidates, st.dist v = minCandidateDist st h := by
  unfold minCandidateDist
  exact Finset.mem_image.mp (Finset.min'_mem _ _)

/-- The candidates attaining the minimal tentative distance. -/
def tied (st : State V) (h : st.candidates.Nonempty) : Finset V :=
  st.candidates.filter (fun v => st.dist v = st.minCandidateDist h)

theorem mem_tied {st : State V} (h : st.candidates.Nonempty) {v : V} :
    v ∈ st.tied h ↔ v ∈ st.candidates ∧ st.dist v = st.minCandidateDist h :=
  Finset.mem_filter

theorem tied_nonempty (st : State V) (h : st.candidates.Nonempty) : (st.tied h).Nonempty :=
  Finset.filter_nonempty_iff.mpr (st.minCandidateDist_attained h)

/-- The candidate whose tentative distance is minimal; among several such vertices the
`LinearOrder` on `V` decides, so the choice is unique. -/
def selectFrom (st : State V) (h : st.candidates.Nonempty) : V :=
  (st.tied h).min' (st.tied_nonempty h)

theorem selectFrom_mem (st : State V) (h : st.candidates.Nonempty) :
    st.selectFrom h ∈ st.candidates := by
  have hm := Finset.min'_mem (st.tied h) (st.tied_nonempty h)
  rw [mem_tied] at hm
  exact hm.1

theorem selectFrom_dist (st : State V) (h : st.candidates.Nonempty) :
    st.dist (st.selectFrom h) = st.minCandidateDist h := by
  have hm := Finset.min'_mem (st.tied h) (st.tied_nonempty h)
  rw [mem_tied] at hm
  exact hm.2

theorem selectFrom_least (st : State V) (h : st.candidates.Nonempty) (x : V)
    (hx : x ∈ st.candidates) (hd : st.dist x = st.minCandidateDist h) :
    st.selectFrom h ≤ x :=
  Finset.min'_le (st.tied h) x (by rw [mem_tied]; exact ⟨hx, hd⟩)

/-- Select the next vertex to finalize: the unvisited vertex with the smallest finite
tentative distance, ties broken by the fixed `LinearOrder` on `V`.  `none` means that no
reachable unvisited vertex is left. -/
def select (st : State V) : Option V :=
  if h : st.candidates.Nonempty then some (st.selectFrom h) else none

theorem select_some {st : State V} {u : V} (h : st.select = some u) :
    ¬ st.visited u ∧ st.dist u ≠ ⊤ ∧
      (∀ x, ¬ st.visited x → st.dist x ≠ ⊤ → st.dist u ≤ st.dist x) := by
  by_cases hc : st.candidates.Nonempty
  · have h1 : st.selectFrom hc ∈ st.candidates := st.selectFrom_mem hc
    have h3 : ∀ x ∈ st.candidates, st.minCandidateDist hc ≤ st.dist x :=
      fun x hx => st.minCandidateDist_le hc x hx
    have hsel : st.select = some (st.selectFrom hc) := by simp [select, hc]
    rw [hsel] at h
    obtain rfl := Option.some.inj h
    refine ⟨(mem_candidates.mp h1).1, (mem_candidates.mp h1).2, ?_⟩
    intro x hxv hxd
    rw [st.selectFrom_dist hc]
    exact h3 x (mem_candidates.mpr ⟨hxv, hxd⟩)
  · have hsel : st.select = none := by simp [select, hc]
    rw [hsel] at h
    exact absurd h (by simp)

theorem select_none {st : State V} (h : st.select = none) (x : V)
    (hx : ¬ st.visited x) : st.dist x = ⊤ := by
  by_cases hc : st.candidates.Nonempty
  · have hsel : st.select = some (st.selectFrom hc) := by simp [select, hc]
    rw [hsel] at h
    exact absurd h (by simp)
  · by_cases hdx : st.dist x = ⊤
    · exact hdx
    · exfalso
      exact hc ⟨x, mem_candidates.mpr ⟨hx, hdx⟩⟩

theorem select_ne_none {st : State V} {v : V} (hv : ¬ st.visited v) (hd : st.dist v ≠ ⊤) :
    st.select ≠ none := by
  intro hsel
  exact hd (select_none hsel v hv)

end State

/-! ### The initial state -/

/-- The initial state: the source is finalized at distance `0` and its outgoing arcs have
been relaxed.  Every other vertex has distance `⊤` unless it is the head of an arc out of
the source, in which case that arc's weight is its tentative distance and its predecessor is
the source.

This is Dijkstra's usual first iteration, performed eagerly so that the source is finalized
from the outset (its optimality is immediate because all weights are non-negative). -/
def init (G : Digraph V) (s : V) : State V where
  dist := fun v => if v = s then 0 else G.extendedWeight s v
  pred := fun v => if v = s then none else match G.edge s v with
    | some _ => some s
    | none => none
  order := [s]

@[simp] theorem init_order (G : Digraph V) (s : V) : (init G s).order = [s] := rfl

@[simp] theorem init_src (G : Digraph V) (s : V) : (init G s).dist s = (0 : WithTop Nat) := by
  simp [init]

@[simp] theorem init_pred_src (G : Digraph V) (s : V) : (init G s).pred s = none := by
  simp [init]

theorem init_dist (G : Digraph V) (s v : V) (h : v ≠ s) :
    (init G s).dist v = G.extendedWeight s v := by
  simp [init, h]

theorem init_pred_some {G : Digraph V} {s v : V} (h : v ≠ s) (he : G.edge s v = some w) :
    (init G s).pred v = some s := by
  simp [init, h, he]

theorem init_pred_none {G : Digraph V} {s v : V} (h : v ≠ s) (he : G.edge s v = none) :
    (init G s).pred v = none := by
  simp [init, h, he]

/-! ### Relaxation -/

/-- Relax all arcs leaving `u` and finalize `u`.

A tentative distance `st.dist v` is replaced by
`min (st.dist v) (st.dist u + weight u v)`, where a missing arc has weight `⊤` and so can
never improve anything.  The predecessor pointer is updated only on a *strict* improvement;
that is what keeps the pointer graph acyclic in the presence of zero-weight arcs. -/
def relax (G : Digraph V) (st : State V) (u : V) : State V where
  dist := fun v => min (st.dist v) (st.dist u + G.extendedWeight u v)
  pred := fun v => if st.dist u + G.extendedWeight u v < st.dist v then some u else st.pred v
  order := st.order ++ [u]

@[simp] theorem relax_order (G : Digraph V) (st : State V) (u : V) :
    (relax G st u).order = st.order ++ [u] := rfl

theorem relax_dist (G : Digraph V) (st : State V) (u v : V) :
    (relax G st u).dist v = min (st.dist v) (st.dist u + G.extendedWeight u v) := rfl

theorem relax_pred (G : Digraph V) (st : State V) (u v : V) :
    (relax G st u).pred v =
      if st.dist u + G.extendedWeight u v < st.dist v then some u else st.pred v := rfl

theorem relax_dist_le (G : Digraph V) (st : State V) (u v : V) :
    (relax G st u).dist v ≤ st.dist v := by
  simp [relax_dist]

/-! ### The step function and the main loop -/

/-- One iteration of Dijkstra's loop: `none` signals that no reachable unvisited vertex
remains, i.e. the algorithm has terminated. -/
def step (G : Digraph V) (st : State V) : Option (State V) :=
  match st.select with
  | none => none
  | some u => some (relax G st u)

theorem step_none {st : State V} (h : st.select = none) : step G st = none := by
  simp [step, h]

theorem step_some {st : State V} {u : V} (h : st.select = some u) :
    step G st = some (relax G st u) := by
  simp [step, h]

/-- The loop, run with `n` units of fuel: `n` is a structurally decreasing iteration
bound, which is what makes the definition terminating. -/
def loop (G : Digraph V) : Nat → State V → State V
  | 0, st => st
  | n + 1, st => match step G st with
    | none => st
    | some st' => loop G n st'

theorem loop_zero (G : Digraph V) (st : State V) : loop G 0 st = st := rfl

theorem loop_succ_none {st : State V} (h : step G st = none) :
    loop G (n + 1) st = st := by
  simp [loop, h]

theorem loop_succ_some {st st' : State V} (h : step G st = some st') :
    loop G (n + 1) st = loop G n st' := by
  simp [loop, h]

/-- The state in which the algorithm finishes: `Fintype.card V` iterations are always
enough (proved in `Dijkstra/Correctness.lean`). -/
def finalState (G : Digraph V) (s : V) : State V := loop G (Fintype.card V) (init G s)

/-- The distance function computed by Dijkstra's algorithm, as an element of
`WithTop ℕ`: `⊤` means "unreachable". -/
def dijkstra (G : Digraph V) (s : V) : V → WithTop Nat := (finalState G s).dist

/-- The same result as an `Option ℕ`-valued function: `none` marks an unreachable vertex,
`some n` a reachable one at distance `n`.

Lean *defines* `WithTop ℕ` to be `Option ℕ` (with `⊤ = none`), so this is the very same
data presented in the `Option` view; the two views are interchangeable by `rfl`. -/
def dijkstraOpt (G : Digraph V) (s : V) (v : V) : Option Nat := dijkstra G s v

theorem dijkstraOpt_none_iff {G : Digraph V} {s v : V} :
    dijkstraOpt G s v = none ↔ dijkstra G s v = ⊤ := Iff.rfl

theorem dijkstraOpt_some_iff {G : Digraph V} {s v : V} {n : Nat} :
    dijkstraOpt G s v = some n ↔ dijkstra G s v = (n : WithTop Nat) := Iff.rfl

theorem dijkstraOpt_eq_some_of_ne_top {G : Digraph V} {s v : V} (h : dijkstra G s v ≠ ⊤) :
    ∃ n, dijkstraOpt G s v = some n ∧ dijkstra G s v = (n : WithTop Nat) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  refine ⟨n, ?_, hn.symm⟩
  show (dijkstra G s v : Option Nat) = some n
  exact hn.symm

/-! ### Path reconstruction -/

/-- Follow predecessor pointers for at most `n` steps, producing the walk from the source
to `v` as a list of the vertices entered after the source.

The bound is what makes the definition structurally terminating; the correctness proof shows
that `n = st.order.length` always suffices, because a predecessor is finalized strictly
before its successor. -/
def pathBound (st : State V) : Nat → V → List V
  | 0, _ => []
  | n + 1, v => match st.pred v with
    | some y => pathBound st n y ++ [v]
    | none => []

/-- Reconstruct the shortest path to `v` by following predecessor pointers.  The result is
the list of vertices entered after the source; the full path is `s :: reconstruct st v`.
For a vertex that was never finalized the result is `[]`. -/
def reconstruct (st : State V) (v : V) : List V := pathBound st st.order.length v

/-- The path computed by Dijkstra from `s` to `v`, as a list of vertices *including* the
source. -/
def dijkstraPath (G : Digraph V) (s v : V) : List V := s :: reconstruct (finalState G s) v

end Dijkstra
