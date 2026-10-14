/-
# Demo executable for the verified Dijkstra implementation

Run with:

```sh
lake exe dijkstra
```

Every number and path printed here is produced by the *verified* implementation;
`Dijkstra/Correctness.lean` proves they agree with the mathematical shortest-path
distance on every finite graph.
-/
import Dijkstra

open Dijkstra

/-- `Option Nat` distances rendered as text: `none` means unreachable. -/
def showOpt (o : Option Nat) : String :=
  match o with
  | none => "unreachable"
  | some n => toString n

def row {n : Nat} (G : Dijkstra.Digraph (Fin n)) (s : Fin n) (v : Fin n) : String :=
  if h : dijkstra G s v = ⊤ then
    s!"  {v.val} → unreachable"
  else
    s!"  {v.val} → {showOpt (dijkstraOpt G s v)}   path: {dijkstraPath G s v}"

def report {n : Nat} (name : String) (G : Dijkstra.Digraph (Fin n)) (s : Fin n) : IO Unit := do
  IO.println s!"\n{name}   [source {s.val}]"
  for v in List.ofFn (fun (i : Fin n) => i) do
    IO.println (row G s v)

def main : IO Unit := do
  IO.println "=== Formally verified Dijkstra shortest paths (Lean 4 + Mathlib) ==="
  IO.println "Distances are `Option Nat`: `none` = unreachable from the source."

  report "1. simple connected graph" Examples.g1 0
  report "2. competing routes" Examples.g2 0
  report "3. disconnected graph (vertex 4 isolated)" Examples.g3 0
  report "4. zero-weight edges" Examples.g4 0
  report "5. equal-cost paths (tie broken by vertex order)" Examples.g5 0
  report "6. cyclic graph" Examples.g6 0
  report "7. single-vertex graph" Examples.g7 0
  report "8. self-loop of weight 0" Examples.g8 0
  report "9. edgeless graph" Examples.g9 1

  IO.println "\nDone."
