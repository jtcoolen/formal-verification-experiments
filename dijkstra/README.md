# Formally verified Dijkstra's shortest-path algorithm in Lean 4

A from-scratch, machine-checked development of **Dijkstra's algorithm** on finite directed
graphs with natural-number weights, built on **Lean 4 + Mathlib**.  The implementation is
executable (`#eval`, `lake exe dijkstra`), it is a genuine Dijkstra loop (select the closest
unvisited vertex, relax its outgoing arcs, finalize it — *not* an enumeration of paths), and
every claim about it is proved for **arbitrary finite graphs**: disconnected graphs, isolated
vertices, self-loops, cycles and **zero-weight edges** are all covered.

There is no `sorry`, no `admit`, no `partial`, no `unsafe` and no user-declared axiom
(`lake env lean Axioms.lean` prints the axiom footprint of every main theorem: only Lean's
three standard axioms `propext`, `Classical.choice`, `Quot.sound` appear).

## Build instructions

Requires [elan](https://github.com/leanprover/elan) and network access for the first build.

```sh
cd dijkstra
lake update            # resolves Mathlib (pinned to the v4.34.1 release)
# Fast path: download Mathlib's prebuilt .olean files instead of compiling Mathlib
# (several hours).  MATHLIB_CACHE_DIR keeps the download inside this workspace.
mkdir -p .mathlibcache
MATHLIB_CACHE_DIR=$PWD/.mathlibcache lake exe cache get
lake build             # builds the library and the demo executable
lake exe dijkstra      # runs the worked demonstration
lake env lean Axioms.lean   # audits every main theorem for hidden axioms
```

If you skip the cache step, `lake build` still works but compiles Mathlib from source.
The pinned toolchain is `lean-toolchain` (`leanprover/lean4:v4.34.1`), which is exactly the
Lean version Mathlib `v4.34.1` is released against.

## Project layout

| File | Contents |
|---|---|
| `Dijkstra/Graph.lean` | The graph model: `Digraph V` with `edge : V → V → Option Nat`. |
| `Dijkstra/Paths.lean` | `Walk`, `walkWeight`, `Reachable`, `ShortestDistance` — the *mathematics*, independent of the algorithm. |
| `Dijkstra/Algorithm.lean` | `State`, `init`, `relax`, `select`, `step`, `loop`, `dijkstra`, `dijkstraOpt`, `pathBound`/`reconstruct`. |
| `Dijkstra/Correctness.lean` | The loop invariant `Inv` and all correctness proofs (requirements A–F). |
| `Dijkstra/Examples.lean` | Nine executable graphs, each checked with `decide`. |
| `Main.lean` | `lake exe dijkstra` demo. |
| `Axioms.lean` | `#print axioms` audit of every main theorem. |

## 1. Graph representation (`Dijkstra/Graph.lean`)

```lean
structure Digraph (V : Type u) where
  edge : V → V → Option Nat
```

* **Finite vertex type.**  Finiteness is only required where the algorithm needs it:
  the theorems about the algorithm assume `[Fintype V] [DecidableEq V] [LinearOrder V]`,
  while the specification files work for any `V`.
* **Non-negative integer weights.**  `Nat` weights; `0` is allowed and is exercised by the
  examples and the proofs (nothing anywhere assumes positivity).
* **Explicit missing edges.**  `edge u v = none` means "there is no arc", `some w` means
  "an arc of weight `w`".  Relaxation reads an absent arc as `⊤ = ∞`
  (`Digraph.extendedWeight`), so a missing arc can never improve a distance.
* **Disconnected graphs / isolated vertices** need no special case: they simply have no arcs
  between components, and the algorithm reports those vertices as unreachable.

## 2. The mathematical specification (`Dijkstra/Paths.lean`)

```lean
inductive Walk (G : Digraph V) : V → List V → Prop where
  | nil  : Walk G s []
  | step : G.edge a b = some w → Walk G b vs → Walk G a (b :: vs)

def walkWeight (G : Digraph V) : V → List V → Nat
def Reachable (G : Digraph V) (s t : V) : Prop
noncomputable def ShortestDistance (G : Digraph V) (s t : V) : WithTop Nat
```

* `Walk G s vs` is the brief's **ValidPath**: `vs` lists the vertices entered after starting
  at `s`, each step following an arc.  `endpoint s vs` is the vertex reached.
* `walkWeight` is the brief's **PathWeight**: the sum of the arc weights along the walk.
* `ShortestDistance G s t` is
  `⨅ (p : WalkTo G s t), walkWeight G s p` — the infimum of the weights of *all* walks from
  `s` to `t`, taken in `WithTop ℕ = ℕ ∪ {∞}`.  It is defined without any reference to
  Dijkstra, and because `WithTop ℕ` is a complete lattice the infimum over the empty family
  is `⊤`, i.e. **unreachable = ∞**.  `Reachable` and `ShortestDistance ≠ ⊤` are proved
  equivalent (`reachable_iff_ShortestDistance_ne_top`), and `ShortestDistance G s s = 0`
  (`ShortestDistance_src`).
* The algorithm's public answer is `Option Nat`-valued (`dijkstraOpt`): `none` for
  unreachable, `some n` for a distance of `n`.  (`WithTop ℕ` *is* `Option ℕ` in Lean, so
  the two views are interchangeable by `rfl`; `dijkstraOpt_none_iff` and
  `dijkstraOpt_some_iff` state the correspondence.)

## 3. The algorithm (`Dijkstra/Algorithm.lean`)

```lean
structure State (V : Type u) where
  dist  : V → WithTop Nat     -- tentative distances, ⊤ = "not known yet"
  pred  : V → Option V        -- predecessor pointers
  order : List V              -- finalized vertices, oldest first

def init   (G : Digraph V) (s : V) : State V        -- source finalized at 0, its arcs relaxed
def relax  (G : Digraph V) (st : State V) (u : V) : State V
def select (st : State V) : Option V                -- closest unvisited vertex, fixed tie-break
def step   (G : Digraph V) (st : State V) : Option (State V)
def loop   (G : Digraph V) : Nat → State V → State V
def finalState (G : Digraph V) (s : V) : State V := loop G (Fintype.card V) (init G s)
def dijkstra   (G : Digraph V) (s : V) : V → WithTop Nat := (finalState G s).dist
```

* **Selection.**  `select` takes the unvisited vertex with the smallest *finite* tentative
  distance; ties are resolved by the fixed `LinearOrder` on `V` (implemented as
  `Finset.min'` over the candidates attaining `minCandidateDist`).  A finite-set minimum
  scan is used instead of a binary heap — the brief allows this and it keeps the proof free
  of heap invariants.
* **Relaxation.**  `dist v := min (dist v) (dist u + weight u v)` for every `v`, with absent
  arcs contributing `⊤`.  The predecessor pointer is updated **only on a strict
  improvement** — that is what keeps the pointer graph acyclic when zero-weight arcs make
  distances equal.
* **Termination condition.**  `step` returns `none` exactly when `select` finds no
  unvisited vertex with a finite distance, i.e. when no reachable unvisited vertex remains.
* **Terminating definition.**  `loop` recurses on a decreasing `Nat` fuel bound
  (`Fintype.card V`), so the definition is structurally terminating; `Correctness.lean`
  then proves the bound is *sufficient* (`dijkstra_terminated`), which is the real content
  of the termination theorem.

## 4. What is proved (`Dijkstra/Correctness.lean`)

The single invariant `Inv G s st` records that

| field | meaning |
|---|---|
| `src`, `src_visited`, `pred_src` | the source has distance `0`, is finalized, has no predecessor |
| `finite` | every finalized vertex has a finite tentative distance |
| `relaxed` | every arc out of a finalized vertex has been relaxed |
| `pred_eq` | every finite tentative distance came from relaxing an arc out of a finalized vertex |
| `pred_before` | a predecessor is finalized strictly before its successor (pointer graph acyclic) |
| `optimal` | no walk into a finalized vertex is lighter than its finalized distance |
| `nodup` | no vertex is finalized twice |

### A. Termination

| Theorem | Meaning |
|---|---|
| `Inv.preserve` | One step maps a state satisfying `Inv` to a state satisfying `Inv`, and grows `order` by exactly one new vertex. |
| `Inv.length_le_card` | `order.length ≤ Fintype.card V` (the well-founded measure: unfinalized vertices). |
| `loop_progress` | `n` units of fuel perform `k ≤ n` real steps, and `k < n\) ⟹ the loop had terminated. |
| `dijkstra_terminated` | `(finalState G s).select = none\) — after `Fintype.card V` iterations no reachable unvisited vertex is left. |
| `dijkstra_step_none`, `dijkstra_fixpoint`, `dijkstra_terminates` | `step\) of the final state is `none`; extra fuel is a no-op; some `n\) satisfies `loop n = loop (n+1)\). |

### B. Relaxation correctness

| Theorem | Meaning |
|---|---|
| `pathBound_spec` | Following predecessor pointers yields a genuine walk of the stored weight. |
| `Inv.realized` | **Every finite tentative distance is the weight of an actual walk** from the source. |
| `Inv.relax_le`, `Inv.stable` | Relaxing into a finalized vertex cannot change its (already optimal) distance. |
| `Inv.preserve` | Relaxation preserves `Inv`, hence preserves the "finite distance ⟹ actual path" interpretation. |

### C. Finalization correctness

| Theorem | Meaning |
|---|---|
| `walk_upper` | A walk whose intermediate vertices are finalized has weight at least the tentative distance of its endpoint. |
| `Inv.cut_aux`, `Inv.cut` | **The cut lemma**: when `u` is selected, no walk from the source to `u` has weight below `dist u`. |

### D. Global optimality

| Theorem | Meaning |
|---|---|
| `Inv.complete` | Any terminated `Inv` state satisfies `dist v = ShortestDistance G s v\) for every `v`. |
| `dijkstra_correct` | `dijkstra G s v = ShortestDistance G s v\) for every finite graph, source and vertex. |
| `dijkstra_source` | `dijkstra G s s = 0`. |
| `dijkstra_visited_iff` | finalized ⟺ finite distance. |
| `dijkstra_reachable_iff` | reachable ⟺ finite distance. |
| `dijkstraOpt_none_iff_unreachable` | `dijkstraOpt G s v = none ⟺ v) is unreachable. |
| `dijkstraOpt_some_iff_shortest` | `dijkstraOpt G s v = some n ⟺ ShortestDistance G s v = n`. |
| `dijkstraOpt_is_minimum` | When the answer is `some n`: some walk has weight exactly `n`, and no walk is lighter. |

### E. Path reconstruction

| Theorem | Meaning |
|---|---|
| `reconstruct_spec` | `reconstruct\) is a valid walk, ends at `v`, and has weight `dijkstra G s v`. |
| `dijkstraPath_head` | The reconstructed path starts at the source. |
| `dijkstraPath_last` | It ends at the requested vertex. |
| `dijkstraPath_valid` | It uses only valid arcs of the graph. |
| `dijkstraPath_weight` | Its total weight equals the mathematical shortest distance. |
| `dijkstraPath_source` | The source reconstructs to `[s]` (zero-weight edges and the source case handled). |
| `dijkstra_reachable_of_finite` | Finite distance ⟹ reachable, with the reconstructed path as the witness. |

### F. Determinism

| Theorem | Meaning |
|---|---|
| `select_spec` | `select` returns the *least minimiser*: minimal tentative distance, and among ties the least vertex in the fixed `LinearOrder`. |
| `select_unique_of_spec` | Two vertices with those properties are **equal** — the tie-breaking rule is unambiguous. |
| `select_unique` | `select` is a function of the state. |
| `dijkstra_deterministic` | Equal graphs and equal sources give equal outputs (the code is pure: no `IO`, no `partial`, no randomness). |
| `dijkstra_result_unique` | **Any** terminated state satisfying `Inv) has `dist = dijkstra G s`: the answer is forced by the specification, so the tie-breaking rule (or any other legal relaxation order) cannot change the distances. |

## 5. Executable examples (`Dijkstra/Examples.lean`)

Every example is proved by `decide` — the kernel itself reduces the algorithm on the
concrete graph, so these are theorems, not comments.

| # | Graph | Checked facts |
|---|---|---|
| 1 | `0→1→2` plus a long direct arc `0→2` of weight 10 | distances `0, 2, 5`; the path is `[0,1,2]`, not the direct arc |
| 2 | competing routes `0→…→4` (direct arc costs 20) | distances `0,1,2,3,4`; path `[0,1,2,3,4]`; finalization order `[0,1,2,3,4]` |
| 3 | disconnected: `0→1`, separate `2→3`, isolated 4 | `2,3,4\) are `none`; only `[0,1]) is finalized; `dijkstraOpt g3 4 4 = some 0` |
| 4 | zero-weight edges `0→1→2` (weight 0) | distances `0,0,0`; path `[0,1,2]`; source path `[0]` |
| 5 | two equal-cost routes of 4 | distance 4; tie broken to `[0,1,3]`; `ShortestDistance = 4` proved via `dijkstra_correct` |
| 6 | cycle `0→1→2→0` plus a chord | distances `0,1,2`; all three vertices finalized |
| 7 | single vertex, no arcs | `some 0`, path `[0]`, `order = [0]`, `ShortestDistance = 0` |
| 8 | self-loop of weight 0 | source stays at 0 (no pointer cycle) |
| 9 | edgeless graph on 4 vertices | only the source is reachable |

Sample of `lake exe dijkstra`:

```text
3. disconnected graph (vertex 4 isolated)   [source 0]
  0 → 0   path: [0]
  1 → 5   path: [0, 1]
  2 → unreachable
  3 → unreachable
  4 → unreachable

4. zero-weight edges   [source 0]
  0 → 0   path: [0]
  1 → 0   path: [0, 1]
  2 → 0   path: [0, 1, 2]
```

## 6. Proof-architecture notes

* **Why the source is pre-finalized.**  `init` performs the first iteration eagerly
  (`order = [s]`, `dist s = 0`, `s`'s arcs relaxed).  This makes `s ∈ order` an unconditional
  invariant, which is what lets `walk_upper` and the cut lemma run their induction without a
  special case for "the source is not yet finalized".
* **Why pointers only move on strict improvement.**  With `0`-weight arcs, `dist v = dist u`
  is possible, so "distance decreases along a pointer" is false.  Acyclicity is instead
  guaranteed by `pred_before): the pointer of a vertex points at a vertex finalized
  *earlier*, which is what makes `pathBound) terminate and what `dijkstraPath_source)
  relies on.
* **`WithTop ℕ` everywhere.**  `⊤ = ∞) is the "unknown/unreachable" value; `x + ⊤ = ⊤`,
  `min`, and the fact that `0) is the least element (non-negativity) are the only order facts
  used.  `coe_nat_add) bridges `↑(a+b)` and `↑a + ↑b`.
* **Non-computability is confined to the specification.**  `ShortestDistance) is a
  `noncomputable) `iInf) over all walks; the algorithm, its termination, and the
  reconstruction lemmas are computable (`#eval dijkstraOpt Examples.g2 0 4) reduces to
  `some 4`).

## 7. Axiom audit

```sh
lake env lean Axioms.lean
```

prints, for each main theorem, something like

```text
'Dijkstra.dijkstra_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only Lean's three standard axioms (all of which Mathlib itself is built on) — no
`sorryAx`, no project-specific axioms.
