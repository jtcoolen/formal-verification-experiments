/-
# Finite directed weighted graphs

A graph is a vertex type equipped with a *partial* weight function
`edge : V → V → Option Nat`.  The `Option` is the explicit representation of a
*missing* edge: `edge u v = none` means "there is no arc from `u` to `v`", while
`edge u v = some w` means "there is an arc `u ⟶ v` of weight `w`".

Weights are natural numbers, so they are non-negative; `0` is allowed.  Nothing here
assumes connectivity, and self-loops and cycles are permitted.  Finiteness of the vertex
set is only needed for the *algorithm*, so it is not baked into the structure.
-/
import Mathlib

universe u

namespace Dijkstra

/-- A directed graph on the vertex type `V` with non-negative integer weights.

* `edge u v = some w` — there is an arc `u ⟶ v` of weight `w`;
* `edge u v = none`   — there is **no** arc from `u` to `v`.

A missing edge is therefore a first-class part of the representation, which is what makes
disconnected graphs and isolated vertices expressible. -/
structure Digraph (V : Type u) where
  edge : V → V → Option Nat

namespace Digraph

variable {V : Type u} (G : Digraph V) {u v : V}

/-- `G.HasEdge u v w` states that `G` contains the arc `u ⟶ v` with weight `w`. -/
def HasEdge (u v : V) (w : Nat) : Prop := G.edge u v = some w

/-- `G.Adj u v` states that `u ⟶ v` is an arc of `G` (with some weight). -/
def Adj (u v : V) : Prop := ∃ w, G.edge u v = some w

/-- The weight of the arc `u ⟶ v`, defined as `0` when the arc is missing. -/
def weightOf (u v : V) : Nat := (G.edge u v).getD 0

/-- The weight of the arc `u ⟶ v` as an element of `WithTop Nat = ℕ ∪ {∞}`, where a
missing arc has weight `∞`.  This is the form used by the relaxation step. -/
def extendedWeight (u v : V) : WithTop Nat :=
  match G.edge u v with
  | some w => w
  | none => ⊤

@[simp] theorem adj_iff_edge_isSome : G.Adj u v ↔ (G.edge u v).isSome := by
  cases e : G.edge u v with
  | none => simp [Adj, HasEdge, e]
  | some w => simp [Adj, HasEdge, e]

@[simp] theorem adj_iff_not_none : G.Adj u v ↔ ¬ (G.edge u v = none) := by
  cases e : G.edge u v <;> simp [Adj, HasEdge, e]

theorem hasEdge_iff_edge : G.HasEdge u v w ↔ G.edge u v = some w := Iff.rfl

theorem adj_iff_hasEdge : G.Adj u v ↔ ∃ w, G.HasEdge u v w := ⟨fun ⟨w, hw⟩ => ⟨w, hw⟩, fun ⟨w, hw⟩ => ⟨w, hw⟩⟩

theorem extendedWeight_eq_coe (h : G.edge u v = some w) :
    G.extendedWeight u v = (w : WithTop Nat) := by
  simp [extendedWeight, h]

theorem extendedWeight_eq_top (h : G.edge u v = none) :
    G.extendedWeight u v = (⊤ : WithTop Nat) := by
  simp [extendedWeight, h]

theorem extendedWeight_ne_top (h : G.Adj u v) : G.extendedWeight u v ≠ (⊤ : WithTop Nat) := by
  obtain ⟨w, hw⟩ := h
  rw [extendedWeight_eq_coe G hw]
  exact WithTop.coe_ne_top

theorem exists_edge_of_extendedWeight_ne_top
    (h : G.extendedWeight u v ≠ (⊤ : WithTop Nat)) : ∃ w, G.edge u v = some w := by
  cases e : G.edge u v with
  | none => exact absurd (extendedWeight_eq_top G e) h
  | some w => exact ⟨w, rfl⟩

theorem weightOf_eq_of_hasEdge (h : G.HasEdge u v w) : G.weightOf u v = w := by
  cases e : G.edge u v <;> simp_all [weightOf, HasEdge]

/-- The edgeless graph on `V`: every pair of vertices is disconnected. -/
def edgeless : Digraph V where
  edge _ _ := none

@[simp] theorem edgeless_edge (u v : V) : (edgeless : Digraph V).edge u v = none := rfl

/-- Build a graph from an explicit list of arcs `(u, v, w)`.  Any pair of vertices not
listed is *not* joined by an arc. -/
def fromEdges [DecidableEq V] (es : List (V × V × Nat)) : Digraph V where
  edge u v := (es.find? (fun ⟨a, b, _⟩ => a = u && b = v)).map (·.2.2)

variable [DecidableEq V]

@[simp] theorem fromEdges_edge (es : List (V × V × Nat)) (u v : V) :
    (fromEdges es : Digraph V).edge u v =
      (es.find? (fun ⟨a, b, _⟩ => a = u && b = v)).map (·.2.2) := rfl

end Digraph

end Dijkstra