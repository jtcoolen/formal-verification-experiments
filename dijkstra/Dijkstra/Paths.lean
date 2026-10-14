/-
# Paths, reachability, and the mathematical specification of distance

This file defines the *mathematics* that the algorithm is later proved to compute:

* `Walk G s vs` — `vs` is a sequence of vertices entered after starting at `s`, each
  step following an arc of `G` (the brief's `ValidPath`);
* `walkWeight G s vs` — the total weight of such a walk (the brief's `PathWeight`);
* `Reachable G s t` — some walk leads from `s` to `t`;
* `ShortestDistance G s t` — the infimum of the weights of all walks from `s` to `t`,
  taken in `WithTop ℕ = ℕ ∪ {∞}`; it is `⊤ = ∞` exactly when `t` is unreachable.

Nothing in this file mentions the algorithm: the specification is independent of the
implementation, as required.
-/
import Mathlib
import Dijkstra.Graph

universe u

namespace Dijkstra

variable {V : Type u} {s t x y : V} {vs ws : List V}

/-! ### Order facts for `WithTop ℕ` -/

/-- Zero is the least element of `WithTop ℕ`; this is where non-negativity of weights is
used. -/
theorem zero_le_withTop_nat (x : WithTop Nat) : (0 : WithTop Nat) ≤ x := by
  by_cases hx : x = ⊤
  · rw [hx]
    exact le_top
  · obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
    exact WithTop.coe_le_coe.mpr (Nat.zero_le n)

/-- Adding a non-negative weight never decreases a distance. -/
theorem withTop_nat_self_le_add (a b : WithTop Nat) : a ≤ a + b := by
  by_cases hb : b = ⊤
  · subst hb
    rw [add_top]
    exact le_top
  · obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hb
    by_cases ha : a = ⊤
    · subst ha
      rw [top_add]
    · obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr (Nat.le_add_right m n)

/-! ### Endpoints and walks -/

/-- `endpoint s vs` is the vertex reached when starting at `s` and entering the vertices
of `vs` one after the other. -/
def endpoint (s : V) (vs : List V) : V := vs.getLastD s

@[simp] theorem endpoint_nil (s : V) : endpoint s [] = s := rfl

@[simp] theorem endpoint_cons (s x : V) (vs : List V) :
    endpoint s (x :: vs) = endpoint x vs := List.getLastD_cons

theorem endpoint_singleton (s x : V) : endpoint s [x] = x := endpoint_cons s x []

/-- `Walk G s vs` says that `vs` is a valid sequence of steps away from `s`: each
element is joined to the previous vertex by an arc of `G`.  The empty list is the trivial
walk that stays at `s`. -/
inductive Walk {V : Type u} (G : Digraph V) : V → List V → Prop where
  | nil {s : V} : Walk G s []
  | step {a b : V} {w : Nat} {vs : List V} :
      G.edge a b = some w → Walk G b vs → Walk G a (b :: vs)

namespace Digraph
variable {V : Type u} (G : Digraph V) {s t x y : V} {vs ws : List V}

/-- `Reachable G s t` — `t` can be reached from `s` by a walk in `G`. -/
def Reachable (s t : V) : Prop := ∃ vs, Walk G s vs ∧ endpoint s vs = t

/-- The trivial walk shows every vertex is reachable from itself. -/
theorem reachable_refl (s : V) : G.Reachable s s := ⟨[], Walk.nil, rfl⟩

/-- The total weight `PathWeight` of the walk `vs` started at `s`.  Missing arcs
contribute `0`; the value is only used under the hypothesis `Walk G s vs`, which
guarantees that every step exists. -/
def walkWeight (G : Digraph V) : V → List V → Nat
  | _, [] => 0
  | s, x :: vs => match G.edge s x with
    | none => 0
    | some w => w + walkWeight G x vs

@[simp] theorem walkWeight_nil (s : V) : G.walkWeight s [] = 0 := rfl

theorem walkWeight_cons (h : G.edge s x = some w) :
    G.walkWeight s (x :: vs) = w + G.walkWeight x vs := by
  simp [Digraph.walkWeight, h]

theorem walkWeight_singleton (h : G.edge s x = some w) : G.walkWeight s [x] = w := by
  rw [walkWeight_cons G h, walkWeight_nil G x, Nat.add_zero]

/-- The weight of a walk is always a finite number. -/
theorem coe_walkWeight_ne_top (s : V) (vs : List V) :
    (G.walkWeight s vs : WithTop Nat) ≠ ⊤ := by
  intro h
  exact absurd h WithTop.coe_ne_top

@[simp] theorem endpoint_append (s : V) (vs ws : List V) :
    endpoint s (vs ++ ws) = endpoint (endpoint s vs) ws := by
  induction vs generalizing s with
  | nil => rfl
  | cons x vs ih => simpa using ih x

theorem walkWeight_append (hvs : Walk G s vs) :
    G.walkWeight s (vs ++ ws) = G.walkWeight s vs + G.walkWeight (endpoint s vs) ws := by
  induction hvs with
  | nil => simp
  | @step a b w rest he hrest ih =>
    have h1 : G.walkWeight a ((b :: rest) ++ ws) = G.walkWeight a (b :: (rest ++ ws)) := rfl
    rw [h1, walkWeight_cons G he, ih, ← add_assoc, ← walkWeight_cons G he, endpoint_cons]

/-- Initial segments of a walk have no larger weight. -/
theorem walkWeight_le_of_prefix (hvs : Walk G s vs) (hpfx : vs <+: ws) :
    (G.walkWeight s vs : WithTop Nat) ≤ G.walkWeight s ws := by
  obtain ⟨l, hl⟩ := hpfx
  subst hl
  rw [walkWeight_append G hvs]
  rw [show ((G.walkWeight s vs + G.walkWeight (endpoint s vs) l : Nat) : WithTop Nat)
        = (G.walkWeight s vs : WithTop Nat) + (G.walkWeight (endpoint s vs) l : WithTop Nat)
      from WithTop.coe_add _ _]
  exact withTop_nat_self_le_add _ _

end Digraph

/-! ### More walk facts -/

theorem Walk.cons_inv {G : Digraph V} {x : V} {rest : List V} (h : Walk G s (x :: rest)) :
    ∃ w, G.edge s x = some w ∧ Walk G x rest := by
  cases h with
  | step he hrest => exact ⟨_, he, hrest⟩

/-- A concatenation of two composable walks is a walk. -/
theorem Walk.append {G : Digraph V} {vs ws : List V} (h1 : Walk G s vs)
    (h2 : Walk G (endpoint s vs) ws) : Walk G s (vs ++ ws) := by
  induction h1 with
  | nil => exact h2
  | step he hrest ih =>
    refine Walk.step he (ih ?_)
    rw [endpoint_cons] at h2
    exact h2

/-- A prefix of a walk is a walk. -/
theorem Walk.of_append {G : Digraph V} {vs ws : List V} (h : Walk G s (vs ++ ws)) :
    Walk G s vs := by
  induction vs generalizing s with
  | nil => exact Walk.nil
  | cons x rest ih =>
    obtain ⟨w, he, hrest⟩ := Walk.cons_inv h
    exact Walk.step he (ih hrest)

theorem Walk.single {G : Digraph V} (h : Walk G s [x]) : G.Adj s x := by
  obtain ⟨w, he, -⟩ := Walk.cons_inv h
  exact ⟨w, he⟩

theorem walk_singleton {G : Digraph V} (h : G.Adj s x) : Walk G s [x] := by
  obtain ⟨w, hw⟩ := h
  exact Walk.step hw Walk.nil

theorem walk_cons {G : Digraph V} {rest : List V} (he : G.edge s x = some w)
    (hrest : Walk G x rest) : Walk G s (x :: rest) := Walk.step he hrest

theorem walk_nil {G : Digraph V} (s : V) : Walk G s [] := Walk.nil

/-- Appending one step at the end of a walk. -/
theorem Walk.snoc {G : Digraph V} (h : Walk G s vs)
    (he : G.edge (endpoint s vs) x = some w) : Walk G s (vs ++ [x]) :=
  h.append (Walk.step he Walk.nil)

/-! ### The mathematical distance -/

/-- The type of walks from `s` to `t`. -/
def WalkTo (G : Digraph V) (s t : V) : Type u :=
  { vs : List V // Walk G s vs ∧ endpoint s vs = t }

/-- The **shortest-path distance** from `s` to `t`: the infimum of the total weights of
all walks from `s` to `t`, taken in `WithTop ℕ = ℕ ∪ {∞}`.

This is a purely mathematical definition: it never mentions the algorithm.  Because
`WithTop ℕ` is a complete lattice, the infimum of the empty family (no walk at all) is
`⊤ = ∞`, so unreachable vertices are distinguished from reachable ones exactly as
required.

The definition is `noncomputable\) only because an infimum over an a-priori infinite family
of walks is involved; the algorithm in `Dijkstra/Algorithm.lean` is fully computable and
its specification is this function. -/
noncomputable def ShortestDistance (G : Digraph V) (s t : V) : WithTop Nat :=
  ⨅ (p : WalkTo G s t), (G.walkWeight s p.val : WithTop Nat)

/-- Any concrete walk bounds the shortest distance from above. -/
theorem ShortestDistance_le_walk {G : Digraph V} (h : Walk G s vs)
    (hve : endpoint s vs = t) :
    ShortestDistance G s t ≤ (G.walkWeight s vs : WithTop Nat) :=
  iInf_le _ (⟨vs, h, hve⟩ : WalkTo G s t)

/-- Any common lower bound of the weights of walks to `t` is at most the shortest
distance. -/
theorem le_ShortestDistance {G : Digraph V} {s t : V} {d : WithTop Nat}
    (h : ∀ vs, Walk G s vs → endpoint s vs = t → d ≤ (G.walkWeight s vs : WithTop Nat)) :
    d ≤ ShortestDistance G s t :=
  le_iInf fun p => h p.val p.property.1 p.property.2

/-- `t` is unreachable exactly when its distance is `∞`. -/
theorem ShortestDistance_eq_top_of_not_reachable {G : Digraph V}
    (h : ¬ G.Reachable s t) : ShortestDistance G s t = (⊤ : WithTop Nat) :=
  le_antisymm le_top
    (le_iInf fun p => False.elim (h (Exists.intro p.val p.property)))

theorem ShortestDistance_ne_top_of_reachable {G : Digraph V} (h : G.Reachable s t) :
    ShortestDistance G s t ≠ (⊤ : WithTop Nat) := by
  obtain ⟨vs, hw, he⟩ := h
  intro htop
  have hle : (⊤ : WithTop Nat) ≤ (G.walkWeight s vs : WithTop Nat) := by
    rw [← htop]
    exact ShortestDistance_le_walk hw he
  exact Digraph.coe_walkWeight_ne_top G s vs (le_antisymm le_top hle)

theorem reachable_iff_ShortestDistance_ne_top (G : Digraph V) (s t : V) :
    G.Reachable s t ↔ ShortestDistance G s t ≠ ⊤ :=
  ⟨ShortestDistance_ne_top_of_reachable,
   fun h => by
     by_contra hnr
     exact h (ShortestDistance_eq_top_of_not_reachable hnr)⟩

/-- The distance from the source to itself is `0`: the empty walk attains it and all
weights are non-negative. -/
theorem ShortestDistance_src (G : Digraph V) (s : V) :
    ShortestDistance G s s = (0 : WithTop Nat) :=
  le_antisymm (ShortestDistance_le_walk Walk.nil rfl)
    (le_ShortestDistance fun _ _ _ => zero_le_withTop_nat _)

/-- A walk of weight `n` from `s` to `t` forces the distance to be at most `n`. -/
theorem ShortestDistance_le_of_reachable_walk {G : Digraph V} (h : Walk G s vs)
    (he : endpoint s vs = t) (n : Nat) (hn : G.walkWeight s vs = n) :
    ShortestDistance G s t ≤ (n : WithTop Nat) := by
  rw [← hn]
  exact ShortestDistance_le_walk h he

end Dijkstra
