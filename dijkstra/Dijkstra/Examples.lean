/-
# Executable examples

Seven worked examples, each checked by `decide` (kernel reduction — no `native_decide`,
no axioms beyond Lean's standard three) and, where useful, displayed with `#eval`.

1. a simple connected graph;
2. several competing routes;
3. a disconnected graph with an isolated vertex;
4. zero-weight edges;
5. equal-cost shortest paths (ties);
6. a graph with cycles;
7. a single-vertex graph.
-/
import Mathlib
import Dijkstra.Correctness

namespace Dijkstra.Examples

open Dijkstra

/-! ### 1. A simple connected graph -/

/-- `0 --2--> 1 --3--> 2` with a long direct arc `0 --10--> 2`. -/
def g1 : Digraph (Fin 3) where
  edge u v :=
    if u = 0 && v = 1 then some 2
    else if u = 1 && v = 2 then some 3
    else if u = 0 && v = 2 then some 10
    else none

example (v : Fin 3) : dijkstra g1 0 v ≠ ⊤ := by
  fin_cases v <;> decide

example : dijkstraOpt g1 0 0 = some 0 := by decide
example : dijkstraOpt g1 0 1 = some 2 := by decide
example : dijkstraOpt g1 0 2 = some 5 := by decide

/-- The direct arc of weight 10 is *not* used: the shortest path is `0 → 1 → 2`. -/
example : dijkstraPath g1 0 2 = [0, 1, 2] := by decide

#eval (List.ofFn fun v : Fin 3 => dijkstraOpt g1 0 v)

/-! ### 2. Several competing routes -/

/-- Competing routes from `0` to `4`: `0→1→2→3→4` costs `1+1+1+1 = 4` while the direct
arc `0→4` costs 20. -/
def g2 : Digraph (Fin 5) where
  edge u v :=
    if u = 0 && v = 1 then some 1
    else if u = 0 && v = 2 then some 4
    else if u = 1 && v = 2 then some 1
    else if u = 1 && v = 3 then some 5
    else if u = 2 && v = 3 then some 1
    else if u = 3 && v = 4 then some 1
    else if u = 0 && v = 4 then some 20
    else none

example : dijkstraOpt g2 0 4 = some 4 := by decide
example : dijkstraOpt g2 0 1 = some 1 := by decide
example : dijkstraOpt g2 0 2 = some 2 := by decide
example : dijkstraOpt g2 0 3 = some 3 := by decide
example : dijkstraPath g2 0 4 = [0, 1, 2, 3, 4] := by decide
example : (finalState g2 0).order = [0, 1, 2, 3, 4] := by decide

#eval (List.ofFn fun v : Fin 5 => dijkstraOpt g2 0 v)

/-! ### 3. A disconnected graph -/

/-- `0 → 1` and a separate component `2 → 3`; vertex 4 is isolated. -/
def g3 : Digraph (Fin 5) where
  edge u v :=
    if u = 0 && v = 1 then some 5
    else if u = 2 && v = 3 then some 7
    else none

example : dijkstraOpt g3 0 0 = some 0 := by decide
example : dijkstraOpt g3 0 1 = some 5 := by decide
/-- Vertices in other components are unreachable and reported as `none`. -/
example : dijkstraOpt g3 0 2 = none := by decide
example : dijkstraOpt g3 0 3 = none := by decide
example : dijkstraOpt g3 0 4 = none := by decide
/-- The isolated vertex is still at distance 0 from itself. -/
example : dijkstraOpt g3 4 4 = some 0 := by decide
example : dijkstraOpt g3 4 3 = none := by decide
/-- Only the reachable component is finalized. -/
example : (finalState g3 0).order = [0, 1] := by decide

#eval (List.ofFn fun v : Fin 5 => dijkstraOpt g3 0 v)

/-! ### 4. Zero-weight edges -/

/-- Zero-weight arcs must not confuse the algorithm, nor make the predecessor pointers
cycle. -/
def g4 : Digraph (Fin 3) where
  edge u v :=
    if u = 0 && v = 1 then some 0
    else if u = 1 && v = 2 then some 0
    else if u = 0 && v = 2 then some 5
    else none

example : dijkstraOpt g4 0 1 = some 0 := by decide
example : dijkstraOpt g4 0 2 = some 0 := by decide
example : dijkstraPath g4 0 2 = [0, 1, 2] := by decide
/-- The source keeps distance 0 even though zero-weight arcs lead back into it. -/
example : dijkstraPath g4 0 0 = [0] := by decide

#eval (List.ofFn fun v : Fin 3 => dijkstraOpt g4 0 v)

/-! ### 5. Equal-cost shortest paths -/

/-- Two routes of cost 4 from `0` to `3`.  The tie is broken by the vertex order, so the
reconstructed path is the one through `1`. -/
def g5 : Digraph (Fin 4) where
  edge u v :=
    if u = 0 && v = 1 then some 2
    else if u = 0 && v = 2 then some 2
    else if u = 1 && v = 3 then some 2
    else if u = 2 && v = 3 then some 2
    else none

example : dijkstraOpt g5 0 3 = some 4 := by decide
example : dijkstraPath g5 0 3 = [0, 1, 3] := by decide
/-- Both routes are shortest: the *distance* does not depend on the tie-breaking. -/
example : ShortestDistance g5 0 3 = (4 : WithTop Nat) := by
  rw [← dijkstra_correct (v := (3 : Fin 4))]
  decide

#eval (List.ofFn fun v : Fin 4 => dijkstraOpt g5 0 v)

/-! ### 6. A graph with cycles -/

/-- A directed cycle `0 → 1 → 2 → 0` plus a chord.  Going around the cycle is more
expensive than the chord, and the algorithm must not loop forever. -/
def g6 : Digraph (Fin 3) where
  edge u v :=
    if u = 0 && v = 1 then some 1
    else if u = 1 && v = 2 then some 1
    else if u = 2 && v = 0 then some 1
    else if u = 0 && v = 2 then some 3
    else none

example : dijkstraOpt g6 0 0 = some 0 := by decide
example : dijkstraOpt g6 0 1 = some 1 := by decide
example : dijkstraOpt g6 0 2 = some 2 := by decide
example : dijkstraPath g6 0 2 = [0, 1, 2] := by decide
/-- Cycles make every vertex reachable, so the loop finalizes all of them. -/
example : (finalState g6 0).order.length = 3 := by decide

#eval (List.ofFn fun v : Fin 3 => dijkstraOpt g6 0 v)

/-! ### 7. A single-vertex graph -/

/-- The one-vertex graph with no arcs. -/
def g7 : Digraph (Fin 1) where
  edge _ _ := none

example : dijkstraOpt g7 0 0 = some 0 := by decide
example : dijkstraPath g7 0 0 = [0] := by decide
example : (finalState g7 0).order = [0] := by decide
example : ShortestDistance g7 0 0 = (0 : WithTop Nat) := ShortestDistance_src g7 0

/-! ### Extras: a self-loop and the edgeless graph -/

/-- A self-loop of weight 0 must not be mistaken for a shorter path to the source. -/
def g8 : Digraph (Fin 2) where
  edge u v :=
    if u = 0 && v = 0 then some 0
    else if u = 0 && v = 1 then some 3
    else none

example : dijkstraOpt g8 0 0 = some 0 := by decide
example : dijkstraOpt g8 0 1 = some 3 := by decide

/-- The edgeless graph on four vertices: only the source is reachable. -/
def g9 : Digraph (Fin 4) := Digraph.edgeless

example : dijkstraOpt g9 1 1 = some 0 := by decide
example : dijkstraOpt g9 1 0 = none := by decide
example : dijkstraOpt g9 1 2 = none := by decide
example : dijkstraOpt g9 1 3 = none := by decide

end Dijkstra.Examples
