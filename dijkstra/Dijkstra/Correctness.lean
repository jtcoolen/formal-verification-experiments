/-
# Correctness of Dijkstra's algorithm

For *every* finite directed graph with `ℕ` weights (zero weights allowed, disconnected
graphs allowed) we prove that the implementation in `Dijkstra/Algorithm.lean`

  * **terminates** (`dijkstra_terminated`, `dijkstra_fixpoint`) — requirement A;
  * **relaxes correctly**: a finite tentative distance is always the weight of an actual
    walk, and this is preserved by relaxation (`Inv.realized`, `Inv.preserve`) — B;
  * **finalizes correctly**: when a vertex is extracted no walk from the source is lighter
    (`Inv.cut`) — C;
  * **computes the mathematical shortest-path distance** of every vertex
    (`dijkstra_correct`, `dijkstraOpt_some_iff_shortest`,
    `dijkstraOpt_none_iff_unreachable`, `dijkstra_source`) — D;
  * **reconstructs genuine shortest paths** from the predecessor pointers
    (`reconstruct_spec`, `dijkstraPath_head`, `dijkstraPath_last`, `dijkstraPath_valid`,
    `dijkstraPath_weight`) — E;
  * is **deterministic**: the selection rule has a unique solution and the final answer is
    forced by the specification alone (`select_spec`, `select_unique_of_spec`,
    `dijkstra_result_unique`) — F.

The proof is the textbook invariant proof.  `Inv` says that (i) every finite tentative
distance is realised by a walk, (ii) every finalized vertex is optimal, and (iii) all arcs
out of a finalized vertex have been relaxed.  The key step is the *cut* argument: any walk
to the extracted vertex must pass through an unvisited vertex; the tentative distance of the
first such vertex bounds a prefix of that walk, and it is at least the extracted distance by
minimality of the selection.
-/
import Mathlib
import Dijkstra.Algorithm

set_option linter.unusedSectionVars false

universe u

namespace Dijkstra

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V] {G : Digraph V} {s : V}

/-- Casting preserves addition (stated so that it can be used as a rewrite rule). -/
theorem coe_nat_add (a b : Nat) :
    ((a + b : Nat) : WithTop Nat) = (a : WithTop Nat) + (b : WithTop Nat) :=
  WithTop.coe_add a b

/-! ### Two small `idxOf` lemmas -/

theorem idxOf_lt_length_of_mem {l : List V} {a : V} (h : a ∈ l) : l.idxOf a < l.length := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x rest ih =>
    rw [_root_.List.idxOf_cons]
    by_cases hx : (x == a) = true
    · rw [if_pos hx]
      simp
    · rw [if_neg hx]
      have hmem : a ∈ rest := by
        rcases List.mem_cons.mp h with heq | hrest
        · exact absurd (by rw [← heq]; simp) hx
        · exact hrest
      have := ih hmem
      simp only [List.length_cons]
      omega

theorem idxOf_append_last {l : List V} {a : V} (h : a ∉ l) : (l ++ [a]).idxOf a = l.length := by
  induction l with
  | nil =>
    show List.idxOf a [a] = 0
    rw [_root_.List.idxOf_cons]
    split <;> simp_all
  | cons x rest ih =>
    have hx : ¬ ((x == a) = true) := fun hh =>
      h (List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hh).symm))
    have hnot : a ∉ rest := fun hh => h (List.mem_cons.mpr (Or.inr hh))
    rw [show (x :: rest) ++ [a] = x :: (rest ++ [a]) from rfl, _root_.List.idxOf_cons,
      if_neg hx, ih hnot]
    simp

/-! ### The loop invariant -/

/-- `AllButLastVisited st vs`: every vertex entered by `vs` except possibly the last one
has been finalized. -/
def AllButLastVisited (st : State V) : List V → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => st.visited x ∧ AllButLastVisited st (y :: rest)

/-- The loop invariant of Dijkstra's algorithm; `s` is the source and `st` the state.

* `src`, `src_visited`, `pred_src`: the source sits at distance `0`, is finalized, and has no
  predecessor.
* `finite`: every finalized vertex has a finite tentative distance.
* `relaxed`: every arc out of a finalized vertex has been relaxed.
* `pred_eq`: every finite tentative distance was obtained by relaxing an arc out of a
  finalized vertex — the "tentative distances are weights of actual paths" content, which
  also drives path reconstruction.
* `pred_before`: a predecessor is finalized strictly before its successor, so the pointer
  graph is acyclic.  (This is where updating the pointer only on a *strict* improvement
  matters: with zero-weight arcs the distance need not decrease along a pointer edge.)
* `optimal`: no walk into a finalized vertex is lighter than its finalized distance. -/
structure Inv (G : Digraph V) (s : V) (st : State V) : Prop where
  src : st.dist s = 0
  src_visited : s ∈ st.order
  pred_src : st.pred s = none
  finite : ∀ v ∈ st.order, st.dist v ≠ ⊤
  nodup : st.order.Nodup
  relaxed : ∀ u ∈ st.order, ∀ v w, G.edge u v = some w → st.dist v ≤ st.dist u + w
  pred_eq : ∀ v, v ≠ s → st.dist v ≠ ⊤ →
    ∃ u ∈ st.order, ∃ w, G.edge u v = some w ∧ st.pred v = some u ∧ st.dist v = st.dist u + w
  pred_before : ∀ x ∈ st.order, ∀ y, st.pred x = some y →
    st.order.idxOf y < st.order.idxOf x
  optimal : ∀ v ∈ st.order, ∀ vs, Walk G s vs → endpoint s vs = v →
    st.dist v ≤ (G.walkWeight s vs : WithTop Nat)

/-! ### Walking inside the finalized set -/

/-- **Tentative distances bound walks that stay inside the finalized set.** -/
theorem walk_upper {st : State V} (hst : Inv G s st) :
    ∀ (vs : List V) (t : V), t ∈ st.order → Walk G t vs → AllButLastVisited st vs →
      st.dist (endpoint t vs) ≤ st.dist t + G.walkWeight t vs := by
  intro vs
  induction vs with
  | nil => intro t ht _ _; simpa using withTop_nat_self_le_add (st.dist t) 0
  | cons x rest ih =>
    intro t ht hvs hint
    obtain ⟨w, he, hwalk⟩ := Walk.cons_inv hvs
    have hx : st.dist x ≤ st.dist t + w := hst.relaxed t ht x w he
    cases rest with
    | nil =>
      simpa [endpoint_singleton, Digraph.walkWeight_singleton G he] using hx
    | cons y rest' =>
      have hih := ih x hint.1 hwalk hint.2
      rw [endpoint_cons, Digraph.walkWeight_cons G he]
      refine le_trans hih ?_
      have h2 : st.dist x + G.walkWeight x (y :: rest') ≤
          (st.dist t + w) + G.walkWeight x (y :: rest') := add_le_add_left hx _
      rwa [add_assoc] at h2

/-- `pathBound` unfolds on a successor fuel. -/
theorem pathBound_succ (st : State V) (n : Nat) (v : V) :
    pathBound st (n + 1) v =
      match st.pred v with
      | some y => pathBound st n y ++ [v]
      | none => [] := rfl

/-- The predecessor pointers reconstruct genuine walks: if `v` is finalized within the
first `n` positions then `pathBound st n v` is a walk from `s` to `v` whose weight is
exactly `st.dist v`. -/
theorem pathBound_spec {st : State V} (hst : Inv G s st) :
    ∀ n (v : V), v ∈ st.order → st.order.idxOf v < n →
      Walk G s (pathBound st n v) ∧ endpoint s (pathBound st n v) = v ∧
        (G.walkWeight s (pathBound st n v) : WithTop Nat) = st.dist v := by
  intro n
  induction n with
  | zero => intro v _ hvx; exact absurd hvx (Nat.not_lt_zero _)
  | succ n ih =>
    intro v hvm hidx
    by_cases hv : v = s
    · have h0 : pathBound st (n + 1) v = [] := by
        rw [pathBound_succ, hv, hst.pred_src]
      rw [h0]
      exact ⟨Walk.nil, hv ▸ rfl, hv ▸ hst.src.symm⟩
    · obtain ⟨u, hu, w, he, hpu, hd⟩ := hst.pred_eq v hv (hst.finite v hvm)
      have hy_lt : st.order.idxOf u < st.order.idxOf v := hst.pred_before v hvm u hpu
      have hrec := ih u hu (by omega)
      have hdef : pathBound st (n + 1) v = pathBound st n u ++ [v] := by
        rw [pathBound_succ, hpu]
      refine ⟨by rw [hdef]; exact hrec.1.snoc (by simpa [hrec.2.1] using he), ?_, ?_⟩
      · rw [hdef, Digraph.endpoint_append, hrec.2.1, endpoint_singleton]
      · rw [hdef, Digraph.walkWeight_append G hrec.1, hrec.2.1,
          Digraph.walkWeight_singleton G he, hd, ← hrec.2.2]
        exact coe_nat_add _ _

/-- **Relaxation preserves the interpretation of finite tentative distances as weights of
actual paths** (brief, requirement B). -/
theorem Inv.realized {st : State V} (hst : Inv G s st) {v : V} (hv : st.dist v ≠ ⊤) :
    ∃ vs, Walk G s vs ∧ endpoint s vs = v ∧ (G.walkWeight s vs : WithTop Nat) = st.dist v := by
  by_cases hvs : v = s
  · subst hvs
    exact ⟨[], Walk.nil, rfl, hst.src.symm⟩
  · obtain ⟨u, hu, w, he, hpu, hd⟩ := hst.pred_eq v hvs hv
    have hidx : st.order.idxOf u < st.order.length := idxOf_lt_length_of_mem hu
    have hrec := pathBound_spec hst _ u hu (Nat.lt_succ_of_lt hidx)
    refine ⟨pathBound st _ u ++ [v], hrec.1.snoc (by simpa [hrec.2.1] using he), ?_, ?_⟩
    · rw [Digraph.endpoint_append, hrec.2.1, endpoint_singleton]
    · rw [Digraph.walkWeight_append G hrec.1, hrec.2.1, Digraph.walkWeight_singleton G he,
        hd, ← hrec.2.2]
      exact coe_nat_add _ _


/-! ### Finalization correctness -/

/-- **Cut lemma.**  If `u` is the selected vertex, then for every walk starting at a
finalized vertex and ending at `u`, `dist u ≤ dist t + weight`. -/
theorem Inv.cut_aux {st : State V} (hst : Inv G s st) {u : V} (hsel : st.select = some u) :
    ∀ (vs : List V) (t : V), t ∈ st.order → Walk G t vs → endpoint t vs = u →
      st.dist u ≤ st.dist t + G.walkWeight t vs := by
  intro vs
  induction vs with
  | nil =>
    intro t ht _ hve
    rw [endpoint_nil] at hve
    subst hve
    rw [Digraph.walkWeight_nil G t]
    exact withTop_nat_self_le_add _ _
  | cons x rest ih =>
    intro t ht hvs hve
    obtain ⟨w, he, hwalk⟩ := Walk.cons_inv hvs
    by_cases hx : st.visited x
    · have hih := ih x hx hwalk (by simpa [endpoint_cons] using hve)
      have hx' : st.dist x ≤ st.dist t + w := hst.relaxed t ht x w he
      rw [Digraph.walkWeight_cons G he]
      refine le_trans hih ?_
      have h2 : st.dist x + G.walkWeight x rest ≤ (st.dist t + w) + G.walkWeight x rest :=
        add_le_add_left hx' _
      rwa [add_assoc] at h2
    · have hux : st.dist x ≤ st.dist t + w := hst.relaxed t ht x w he
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hst.finite t ht)
      have hfin : (↑m : WithTop Nat) + ↑w = (↑(m + w) : WithTop Nat) := coe_nat_add m w
      have hx' : st.dist x ≠ ⊤ := by
        intro hh
        have h1 : st.dist x ≤ (↑(m + w) : WithTop Nat) := by
          rw [← hfin]
          exact le_trans hux (add_le_add_left (le_of_eq hm.symm) (w : WithTop Nat))
        rw [hh] at h1
        exact WithTop.coe_ne_top (le_antisymm le_top h1)
      have hle := (State.select_some hsel).2.2 x hx hx'
      rw [Digraph.walkWeight_cons G he]
      calc st.dist u ≤ st.dist x := hle
        _ ≤ st.dist t + w := hux
        _ ≤ st.dist t + (w + G.walkWeight x rest) :=
            add_le_add_right (withTop_nat_self_le_add _ _) _

/-- **Finalization correctness** (brief, requirement C): when the algorithm finalizes `u`
with a finite distance, no valid path from the source has smaller weight. -/
theorem Inv.cut {st : State V} (hst : Inv G s st) {u : V} (hsel : st.select = some u)
    (vs : List V) (hvs : Walk G s vs) (hve : endpoint s vs = u) :
    st.dist u ≤ (G.walkWeight s vs : WithTop Nat) := by
  have := hst.cut_aux hsel vs s hst.src_visited hvs hve
  rwa [hst.src, zero_add] at this

/-! ### Stability of finalized distances -/

/-- Relaxing an arc into a finalized vertex cannot improve its distance: the finalized
distance is already optimal. -/
theorem Inv.relax_le {st : State V} (hst : Inv G s st) {u v : V} (hu : st.dist u ≠ ⊤)
    (hv : v ∈ st.order) : st.dist v ≤ st.dist u + G.extendedWeight u v := by
  by_cases hu' : G.Adj u v
  · obtain ⟨w, hw⟩ := hu'
    obtain ⟨p, hpw, hpe, hpwt⟩ := hst.realized hu
    have hwalk : Walk G s (p ++ [v]) := hpw.snoc (by simpa [hpe] using hw)
    have hend : endpoint s (p ++ [v]) = v := by
      rw [Digraph.endpoint_append, hpe, endpoint_singleton]
    have hw' : (G.walkWeight s (p ++ [v]) : WithTop Nat) = st.dist u + w := by
      rw [Digraph.walkWeight_append G hpw, hpe, Digraph.walkWeight_singleton G hw, ← hpwt]
      exact coe_nat_add _ _
    have := hst.optimal v hv (p ++ [v]) hwalk hend
    rw [hw'] at this
    rwa [Digraph.extendedWeight_eq_coe G hw]
  · have htop : G.extendedWeight u v = (⊤ : WithTop Nat) := by
      cases e : G.edge u v with
      | none => exact Digraph.extendedWeight_eq_top G e
      | some w => exact absurd ⟨w, e⟩ hu'
    rw [htop, add_top]
    exact le_top

/-- Relaxing arcs into an already finalized vertex never changes its distance: a finalized
distance is already optimal. -/
theorem Inv.stable {st : State V} (hst : Inv G s st) {u : V} (hu : st.dist u ≠ ⊤) :
    ∀ v ∈ st.order, (relax G st u).dist v = st.dist v := by
  intro v hv
  rw [relax_dist, min_eq_left (hst.relax_le hu hv)]

/-! ### The invariant is preserved by one step -/

/-- **One iteration preserves the invariant.**  Together with `Inv_init` this is the
inductive core of the proof: relaxing the arcs out of the selected vertex keeps every finite
tentative distance the weight of an actual walk, keeps all previously finalized distances
optimal, and makes the selected vertex's distance optimal as well. -/
theorem Inv.preserve {st : State V} (hst : Inv G s st) {u : V} (hsel : st.select = some u) :
    Inv G s (relax G st u) := by
  obtain ⟨hunv, hud, hmin⟩ := State.select_some hsel
  have hunv' : ¬ (u ∈ st.order) := hunv
  have hus : (relax G st u).dist u = st.dist u := by
    rw [relax_dist, min_eq_left (withTop_nat_self_le_add _ _)]
  have hst' := hst.stable hud
  have hsrc : (relax G st u).dist s = 0 := by
    rw [relax_dist, hst.src, min_eq_left (zero_le_withTop_nat _)]
  have hsrc_vis : s ∈ (relax G st u).order := by
    rw [relax_order]
    exact List.mem_append.mpr (Or.inl hst.src_visited)
  have hnotlt : ¬ (st.dist u + G.extendedWeight u s < st.dist s) := by
    rw [hst.src]
    intro hh
    exact lt_irrefl _ (lt_of_lt_of_le hh (zero_le_withTop_nat _))
  have hpred_src : (relax G st u).pred s = none := by
    rw [relax_pred, if_neg hnotlt]
    exact hst.pred_src
  have hfinite : ∀ v ∈ (relax G st u).order, (relax G st u).dist v ≠ ⊤ := by
    intro v hv
    cases List.mem_append.mp hv with
    | inl h =>
      intro htop
      have h1 : (⊤ : WithTop Nat) ≤ st.dist v := by rw [← htop]; exact relax_dist_le G st u v
      exact hst.finite v h (le_antisymm le_top h1)
    | inr h =>
      rw [List.mem_singleton] at h
      rw [h, hus]
      exact hud
  have hnodup : (relax G st u).order.Nodup := by
    rw [relax_order, List.nodup_append]
    refine ⟨hst.nodup, List.nodup_singleton u, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    intro hh
    exact hunv' ((hh.trans hb) ▸ ha)
  have hrelaxed : ∀ x ∈ (relax G st u).order, ∀ v w, G.edge x v = some w →
      (relax G st u).dist v ≤ (relax G st u).dist x + w := by
    intro x hx v w hvw
    cases List.mem_append.mp hx with
    | inl h =>
      calc (relax G st u).dist v ≤ st.dist v := relax_dist_le G st u v
        _ ≤ st.dist x + w := hst.relaxed x h v w hvw
        _ = (relax G st u).dist x + w := by rw [hst' x h]
    | inr h =>
      rw [List.mem_singleton] at h
      subst h
      calc (relax G st x).dist v ≤ st.dist x + G.extendedWeight x v := min_le_right _ _
        _ = (relax G st x).dist x + G.extendedWeight x v := by rw [hus]
        _ = (relax G st x).dist x + w := by rw [Digraph.extendedWeight_eq_coe G hvw]
  have hpred_eq : ∀ v, v ≠ s → (relax G st u).dist v ≠ ⊤ →
      ∃ y ∈ (relax G st u).order, ∃ w, G.edge y v = some w ∧
        (relax G st u).pred v = some y ∧ (relax G st u).dist v = (relax G st u).dist y + w := by
    intro v hv hne
    by_cases hlt : st.dist u + G.extendedWeight u v < st.dist v
    · have hd' : (relax G st u).dist v = st.dist u + G.extendedWeight u v := by
        rw [relax_dist, min_eq_right (le_of_lt hlt)]
      have hp' : (relax G st u).pred v = some u := by
        rw [relax_pred, if_pos hlt]
      have hadj : ∃ w, G.edge u v = some w := by
        by_contra hc
        push_neg at hc
        have : G.extendedWeight u v = (⊤ : WithTop Nat) := by
          cases e : G.edge u v with
          | none => exact Digraph.extendedWeight_eq_top G e
          | some w => exact (hc w e).elim
        rw [this, add_top] at hd'
        exact hne hd'
      obtain ⟨w, hw⟩ := hadj
      have hin : u ∈ (relax G st u).order := by
        rw [relax_order]
        simp
      have hlast : (relax G st u).dist v = (relax G st u).dist u + w := by
        rw [hd', hus, Digraph.extendedWeight_eq_coe G hw]
      exact ⟨u, hin, w, hw, hp', hlast⟩
    · have hge : st.dist v ≤ st.dist u + G.extendedWeight u v := not_lt.mp hlt
      have hd' : (relax G st u).dist v = st.dist v := by
        rw [relax_dist, min_eq_left hge]
      have hp' : (relax G st u).pred v = st.pred v := by
        rw [relax_pred, if_neg hlt]
      obtain ⟨y, hy, w, hw, hpy, hdy⟩ := hst.pred_eq v hv (by rw [← hd']; exact hne)
      have hp'' : (relax G st u).pred v = some y := by rw [hp', hpy]
      have hlast : (relax G st u).dist v = (relax G st u).dist y + w := by
        rw [hd', hst' y hy, hdy]
      exact ⟨y, List.mem_append.mpr (Or.inl hy), w, hw, hp'', hlast⟩
  have hpred_before : ∀ x ∈ (relax G st u).order, ∀ y, (relax G st u).pred x = some y →
      (relax G st u).order.idxOf y < (relax G st u).order.idxOf x := by
    intro x hx y hxy
    rw [relax_order]
    cases List.mem_append.mp hx with
    | inl h =>
      have hpx : (relax G st u).pred x = st.pred x := by
        rw [relax_pred, if_neg (not_lt.mpr (hst.relax_le hud h))]
      rw [hpx] at hxy
      have hy : y ∈ st.order := by
        by_cases hys : y = s
        · rw [hys]
          exact hst.src_visited
        · have hx_ne_s : x ≠ s := by
            intro hh
            rw [hh, hst.pred_src] at hxy
            exact absurd hxy (by simp)
          obtain ⟨u', hu', w, hw, hpu', _⟩ := hst.pred_eq x hx_ne_s (hst.finite x h)
          have hyy : u' = y := Option.some.inj (hpu'.symm.trans hxy)
          rw [← hyy]
          exact hu'
      rw [_root_.List.idxOf_append_of_mem hy, _root_.List.idxOf_append_of_mem h]
      exact hst.pred_before x h y hxy
    | inr h =>
      rw [List.mem_singleton] at h
      subst h
      have hpu : (relax G st x).pred x = st.pred x := by
        rw [relax_pred, if_neg (not_lt.mpr (withTop_nat_self_le_add _ _))]
      rw [hpu] at hxy
      by_cases hu' : x = s
      · subst hu'
        rw [hst.pred_src] at hxy
        exact absurd hxy (by simp)
      · obtain ⟨y', hy', w, hw, hpy', _⟩ := hst.pred_eq x hu' hud
        have hyy : y' = y := Option.some.inj (hpy'.symm.trans hxy)
        subst hyy
        rw [idxOf_append_last (fun hh => hunv' hh)]
        rw [_root_.List.idxOf_append_of_mem hy']
        exact idxOf_lt_length_of_mem hy'
  have hoptimal : ∀ v ∈ (relax G st u).order, ∀ vs, Walk G s vs → endpoint s vs = v →
      (relax G st u).dist v ≤ (G.walkWeight s vs : WithTop Nat) := by
    intro v hv vs hvs hve
    cases List.mem_append.mp hv with
    | inl h =>
      exact le_trans (relax_dist_le G st u v) (hst.optimal v h vs hvs hve)
    | inr h =>
      rw [List.mem_singleton] at h
      subst h
      rw [hus]
      exact hst.cut hsel vs hvs hve
  exact ⟨hsrc, hsrc_vis, hpred_src, hfinite, hnodup, hrelaxed, hpred_eq, hpred_before,
    hoptimal⟩

/-! ### Termination (brief, requirement A) -/

/-- The initial state satisfies the invariant. -/
theorem Inv_init : Inv G s (init G s) := by
  refine ⟨init_src G s, List.mem_singleton_self s, init_pred_src G s, ?_,
    List.nodup_singleton s, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h1 : v = s := by simpa using hv
    rw [h1]
    rw [init_src G s]
    exact WithTop.coe_ne_top
  · intro u hu v w hvw
    have h1 : u = s := by simpa using hu
    rw [h1] at hvw ⊢
    by_cases hvv : v = s
    · rw [hvv]
      rw [init_src G s, zero_add]
      exact zero_le_withTop_nat _
    · rw [init_dist G s v hvv, init_src G s, zero_add, Digraph.extendedWeight_eq_coe G hvw]
  · intro v hv hne
    rw [init_dist G s v hv] at hne
    obtain ⟨w, hw⟩ := Digraph.exists_edge_of_extendedWeight_ne_top G hne
    refine ⟨s, List.mem_singleton_self s, w, hw, ?_, ?_⟩
    · exact init_pred_some hv hw
    · rw [init_dist G s v hv, Digraph.extendedWeight_eq_coe G hw, init_src G s, zero_add]
  · intro x hx y hxy
    have h1 : x = s := by simpa using hx
    rw [h1] at hxy
    rw [init_pred_src G s] at hxy
    exact absurd hxy (by simp)
  · intro v hv vs hvs hve
    have h1 : v = s := by simpa using hv
    rw [h1]
    rw [init_src G s]
    exact zero_le_withTop_nat _

/-- The finalized list can never contain more vertices than the graph has. -/
theorem Inv.length_le_card {st : State V} (hst : Inv G s st) :
    st.order.length ≤ Fintype.card V :=
  List.Nodup.length_le_card hst.nodup

@[simp] theorem init_order_length (G : Digraph V) (s : V) : (init G s).order.length = 1 := rfl

/-- **Progress of the fuelled loop.**  Running `loop` with `n` units of fuel performs
`k ≤ n` real steps; the invariant is maintained, the finalized list grows by exactly `k`,
and if `k < n` then the loop had already terminated. -/
theorem loop_progress (n : Nat) : ∀ st : State V, Inv G s st →
    ∃ k, k ≤ n ∧ Inv G s (loop G n st) ∧
      (loop G n st).order.length = st.order.length + k ∧
      (k < n → (loop G n st).select = none) := by
  induction n with
  | zero =>
    intro st hst
    exact ⟨0, Nat.le_refl 0, hst, by rw [loop_zero, Nat.add_zero],
      by intro hk; exact absurd hk (Nat.not_lt_zero 0)⟩
  | succ n ih =>
    intro st hst
    by_cases hsel : st.select = none
    · have hloop : loop G (n + 1) st = st := loop_succ_none (step_none hsel)
      refine ⟨0, Nat.zero_le _, ?_, ?_, ?_⟩
      · rw [hloop]; exact hst
      · rw [hloop]; omega
      · intro hk
        rw [hloop]
        exact hsel
    · obtain ⟨u, hu⟩ : ∃ u, st.select = some u := by
        cases h : st.select with
        | none => exact absurd h hsel
        | some v => exact ⟨v, rfl⟩
      have hstep : step G st = some (relax G st u) := step_some hu
      have hinv : Inv G s (relax G st u) := hst.preserve hu
      obtain ⟨k', hk', hinv', hlen, hterm⟩ := ih (relax G st u) hinv
      have hloop : loop G (n + 1) st = loop G n (relax G st u) := loop_succ_some hstep
      refine ⟨k' + 1, by omega, hloop.symm ▸ hinv', ?_, ?_⟩
      · rw [hloop, hlen, relax_order, List.length_append, List.length_singleton]
        omega
      · intro hk
        have : k' < n := by omega
        rw [loop_succ_some hstep]
        exact hterm this

/-- **Termination** (brief, requirement A).  On every finite graph the loop reaches a state
in which no reachable unvisited vertex remains, so no further step is possible.  The measure
that decreases is the number of unfinalized vertices: each step finalizes one new vertex and
there are only `Fintype.card V` of them, so `Fintype.card V` units of fuel always suffice. -/
theorem dijkstra_terminated : (finalState G s).select = none := by
  obtain ⟨k, hkn, hinv, hlen, hterm⟩ :=
    loop_progress (Fintype.card V) (init G s) Inv_init
  have hle : 1 + k ≤ Fintype.card V := by
    have := hinv.length_le_card
    rwa [hlen] at this
  by_contra hc
  have hlt : k < Fintype.card V := by omega
  exact hc (hterm hlt)

/-- No step is possible after termination. -/
theorem dijkstra_step_none : step G (finalState G s) = none :=
  step_none dijkstra_terminated

/-- Running the loop with one more unit of fuel after termination changes nothing. -/
theorem dijkstra_fixpoint : loop G 1 (finalState G s) = finalState G s :=
  loop_succ_none dijkstra_step_none

/-- If the loop has terminated within its fuel, one more unit of fuel is a no-op. -/
theorem loop_stable (n : Nat) : ∀ st : State V,
    (loop G n st).select = none → loop G (n + 1) st = loop G n st := by
  induction n with
  | zero =>
    intro st h
    have h1 : loop G 1 st = st := loop_succ_none (step_none h)
    rw [h1, loop_zero]
  | succ n ih =>
    intro st h
    by_cases hsel : st.select = none
    · have h1 : loop G (n + 1 + 1) st = st := loop_succ_none (step_none hsel)
      have h2 : loop G (n + 1) st = st := loop_succ_none (step_none hsel)
      rw [h1, h2]
    · obtain ⟨u, hu⟩ : ∃ u, st.select = some u := by
        cases h' : st.select with
        | none => exact absurd h' hsel
        | some v => exact ⟨v, rfl⟩
      have hstep : step G st = some (relax G st u) := step_some hu
      have h1 : loop G (n + 1 + 1) st = loop G (n + 1) (relax G st u) := loop_succ_some hstep
      have h2 : loop G (n + 1) st = loop G n (relax G st u) := loop_succ_some hstep
      have hsel' : (loop G n (relax G st u)).select = none := by rw [← h2]; exact h
      rw [h1, h2, ih (relax G st u) hsel']

/-- Some number of iterations suffices to reach a fixed point: the algorithm terminates. -/
theorem dijkstra_terminates : ∃ n, loop G n (init G s) = loop G (n + 1) (init G s) :=
  ⟨Fintype.card V, (loop_stable (Fintype.card V) (init G s) dijkstra_terminated).symm⟩

theorem finalState_inv : Inv G s (finalState G s) := by
  obtain ⟨_, _, hinv, _, _⟩ := loop_progress (Fintype.card V) (init G s) Inv_init
  exact hinv

/-! ### Global optimality (brief, requirement D) -/

/-- If no reachable unvisited vertex is left, the endpoint of any walk out of the finalized
set still has a finite tentative distance. -/
theorem Inv.walk_ne_top {st : State V} (hst : Inv G s st) (hsel : st.select = none) :
    ∀ (vs : List V) (t : V), t ∈ st.order → Walk G t vs → st.dist (endpoint t vs) ≠ ⊤ := by
  intro vs
  induction vs with
  | nil => intro t ht _; exact hst.finite t ht
  | cons x rest ih =>
    intro t ht hvs
    obtain ⟨w, he, hwalk⟩ := Walk.cons_inv hvs
    by_cases hx : st.visited x
    · rw [endpoint_cons]
      exact ih x hx hwalk
    · exfalso
      have hux : st.dist x ≤ st.dist t + w := hst.relaxed t ht x w he
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hst.finite t ht)
      have hfin : (↑m : WithTop Nat) + ↑w = (↑(m + w) : WithTop Nat) := coe_nat_add m w
      have h1 : st.dist x ≤ (↑(m + w) : WithTop Nat) := by
        rw [← hfin]
        exact le_trans hux (add_le_add_left (le_of_eq hm.symm) (w : WithTop Nat))
      have htop : st.dist x = ⊤ := State.select_none hsel x hx
      rw [htop] at h1
      exact WithTop.coe_ne_top (le_antisymm le_top h1)

/-- **Global optimality** (brief, requirement D).  Any terminated state satisfying the
invariant computes the mathematical shortest-path distance of every vertex.  This is the
sense in which the answer is *forced* by the specification. -/
theorem Inv.complete {st : State V} (hst : Inv G s st) (hsel : st.select = none) (v : V) :
    st.dist v = ShortestDistance G s v := by
  by_cases hv : st.dist v = ⊤
  · have hunr : ¬ G.Reachable s v := by
      intro ⟨vs, hvs, he⟩
      have h2 : st.dist (endpoint s vs) ≠ ⊤ := hst.walk_ne_top hsel vs s hst.src_visited hvs
      rw [he] at h2
      exact h2 hv
    rw [hv, ShortestDistance_eq_top_of_not_reachable hunr]
  · have hv' : v ∈ st.order := by
      by_contra hc
      exact hv (State.select_none hsel v (by simpa [State.visited] using hc))
    refine le_antisymm (le_ShortestDistance fun vs hvs he => hst.optimal v hv' vs hvs he) ?_
    obtain ⟨p, hpw, hpe, hpwt⟩ := hst.realized hv
    have hle := ShortestDistance_le_walk hpw hpe
    rwa [hpwt] at hle

/-- The distance computed by Dijkstra equals the mathematical shortest-path distance, for
every vertex of every finite graph. -/
theorem dijkstra_correct (v : V) : dijkstra G s v = ShortestDistance G s v :=
  finalState_inv.complete dijkstra_terminated v

/-- The source has distance 0. -/
theorem dijkstra_source : dijkstra G s s = (0 : WithTop Nat) := finalState_inv.src

/-- A vertex is finalized exactly when its computed distance is finite. -/
theorem dijkstra_visited_iff (v : V) :
    v ∈ (finalState G s).order ↔ dijkstra G s v ≠ ⊤ := by
  constructor
  · intro hv; exact finalState_inv.finite v hv
  · intro hv
    by_contra hc
    exact hv (State.select_none dijkstra_terminated v (by simpa [State.visited] using hc))

/-- A vertex is reachable exactly when Dijkstra returns a finite distance. -/
theorem dijkstra_reachable_iff (v : V) : G.Reachable s v ↔ dijkstra G s v ≠ ⊤ := by
  rw [dijkstra_correct, reachable_iff_ShortestDistance_ne_top]

/-- **Unreachable vertices return `none`** (brief, requirement D). -/
theorem dijkstraOpt_none_iff_unreachable (v : V) :
    dijkstraOpt G s v = none ↔ ¬ G.Reachable s v := by
  rw [dijkstraOpt_none_iff]
  exact (((dijkstra_reachable_iff v).not).trans not_ne_iff).symm

/-- **Reachable vertices return their minimum possible path weight** (brief, requirement D). -/
theorem dijkstraOpt_some_iff_shortest (v : V) (n : Nat) :
    dijkstraOpt G s v = some n ↔ ShortestDistance G s v = (n : WithTop Nat) := by
  rw [dijkstraOpt_some_iff, ← dijkstra_correct]

/-- The returned number really is a minimum: it is attained by some walk, and no walk is
lighter. -/
theorem dijkstraOpt_is_minimum (v : V) (n : Nat) (h : dijkstraOpt G s v = some n) :
    (∃ vs, Walk G s vs ∧ endpoint s vs = v ∧ G.walkWeight s vs = n) ∧
      (∀ vs, Walk G s vs → endpoint s vs = v → (n : WithTop Nat) ≤ G.walkWeight s vs) := by
  have hd : dijkstra G s v = (n : WithTop Nat) := (dijkstraOpt_some_iff (v := v)).mp h
  have hv : dijkstra G s v ≠ ⊤ := by rw [hd]; exact WithTop.coe_ne_top
  have hv' : v ∈ (finalState G s).order := (dijkstra_visited_iff v).mpr hv
  refine ⟨?_, fun vs hvs he => by rw [← hd]; exact finalState_inv.optimal v hv' vs hvs he⟩
  obtain ⟨p, hpw, hpe, hpwt⟩ := finalState_inv.realized hv
  have hd2 : (finalState G s).dist v = (n : WithTop Nat) := hd
  have hpwt' : (G.walkWeight s p : WithTop Nat) = (n : WithTop Nat) := by rw [hpwt, hd2]
  exact ⟨p, hpw, hpe, WithTop.coe_inj.mp hpwt'⟩

/-! ### Path reconstruction (brief, requirement E) -/

/-- The reconstructed pointer chain is a genuine walk whose weight is the computed distance. -/
theorem reconstruct_spec (v : V) (hv : dijkstra G s v ≠ ⊤) :
    Walk G s (reconstruct (finalState G s) v) ∧
      endpoint s (reconstruct (finalState G s) v) = v ∧
      (G.walkWeight s (reconstruct (finalState G s) v) : WithTop Nat) = dijkstra G s v := by
  have hv' : v ∈ (finalState G s).order := (dijkstra_visited_iff v).mpr hv
  have hidx : (finalState G s).order.idxOf v < (finalState G s).order.length :=
    idxOf_lt_length_of_mem hv'
  exact pathBound_spec finalState_inv _ v hv' hidx

/-- The reconstructed path starts at the source. -/
theorem dijkstraPath_head (v : V) (hv : dijkstra G s v ≠ ⊤) :
    (dijkstraPath G s v).head? = some s := by
  show (s :: reconstruct (finalState G s) v).head? = some s
  simp

/-- The reconstructed path ends at the requested vertex. -/
theorem dijkstraPath_last (v : V) (hv : dijkstra G s v ≠ ⊤) :
    (dijkstraPath G s v).getLastD s = v := by
  obtain ⟨_, hpe, _⟩ := reconstruct_spec v hv
  show ((s :: reconstruct (finalState G s) v)).getLastD s = v
  rw [List.getLastD_cons]
  exact hpe

/-- The reconstructed path uses only valid arcs of the graph. -/
theorem dijkstraPath_valid (v : V) (hv : dijkstra G s v ≠ ⊤) :
    Walk G s (reconstruct (finalState G s) v) := (reconstruct_spec v hv).1

/-- The reconstructed path has total weight equal to the computed shortest distance. -/
theorem dijkstraPath_weight (v : V) (hv : dijkstra G s v ≠ ⊤) :
    (G.walkWeight s (reconstruct (finalState G s) v) : WithTop Nat) = ShortestDistance G s v := by
  rw [← dijkstra_correct, (reconstruct_spec v hv).2.2]

/-- The source reconstructs to the trivial path `[s]`: its pointer is `none`, and
zero-weight arcs do not create pointer cycles. -/
theorem dijkstraPath_source : dijkstraPath G s s = [s] := by
  have hp : (finalState G s).pred s = none := finalState_inv.pred_src
  have hpos : 0 < (finalState G s).order.length :=
    List.length_pos_of_mem finalState_inv.src_visited
  have hlen : (finalState G s).order.length = (finalState G s).order.length - 1 + 1 := by omega
  show s :: pathBound (finalState G s) ((finalState G s).order.length) s = [s]
  rw [hlen, pathBound_succ, hp]

/-- Every vertex with a finite computed distance is reachable, witnessed by the reconstructed
path. -/
theorem dijkstra_reachable_of_finite (v : V) (hv : dijkstra G s v ≠ ⊤) : G.Reachable s v :=
  ⟨reconstruct (finalState G s) v, (reconstruct_spec v hv).1, (reconstruct_spec v hv).2.1⟩

/-! ### Determinism (brief, requirement F) -/

/-- The selection rule picks the *least minimiser*: it is a candidate, no candidate has a
smaller tentative distance, and among the candidates tied at that distance it is the least in
the fixed `LinearOrder` on `V`. -/
theorem select_spec {st : State V} {u : V} (h : st.select = some u) :
    u ∈ st.candidates ∧ (∀ x ∈ st.candidates, st.dist u ≤ st.dist x) ∧
      (∀ x ∈ st.candidates, st.dist x = st.dist u → u ≤ x) := by
  obtain ⟨hu1, hu2, hu3⟩ := State.select_some h
  by_cases hc : st.candidates.Nonempty
  · have hsel : st.select = some (st.selectFrom hc) := by simp [State.select, hc]
    rw [hsel] at h
    obtain ⟨rfl⟩ := Option.some.inj h
    refine ⟨State.selectFrom_mem st hc, ?_, ?_⟩
    · intro x hx
      rw [State.selectFrom_dist st hc]
      exact State.minCandidateDist_le st hc x hx
    · intro x hx hd
      have : st.dist x = st.minCandidateDist hc := by rw [hd, State.selectFrom_dist st hc]
      exact State.selectFrom_least st hc x hx this
  · exfalso
    have hsel : st.select = none := by simp [State.select, hc]
    rw [hsel] at h
    exact absurd h (by simp)

/-- **The tie-breaking rule is deterministic:** two vertices satisfying the characterising
properties of `select` are equal. -/
theorem select_unique_of_spec {st : State V} {u u' : V}
    (hu : u ∈ st.candidates ∧ (∀ x ∈ st.candidates, st.dist u ≤ st.dist x) ∧
      (∀ x ∈ st.candidates, st.dist x = st.dist u → u ≤ x))
    (hu' : u' ∈ st.candidates ∧ (∀ x ∈ st.candidates, st.dist u' ≤ st.dist x) ∧
      (∀ x ∈ st.candidates, st.dist x = st.dist u' → u' ≤ x)) : u = u' := by
  obtain ⟨m1, l1, t1⟩ := hu
  obtain ⟨m2, l2, t2⟩ := hu'
  have heq : st.dist u = st.dist u' := le_antisymm (l1 u' m2) (l2 u m1)
  exact le_antisymm (t1 u' m2 heq.symm) (t2 u m1 heq)

/-- The selection is a function: the same state cannot select two different vertices. -/
theorem select_unique {st : State V} {u u' : V} (h : st.select = some u)
    (h' : st.select = some u') : u = u' := by
  have h2 : some u = some u' := by rw [← h, ← h']
  exact Option.some.inj h2

/-- The whole computation is a pure function of the graph and the source: equal inputs give
equal outputs, with no hidden state, randomness or `IO`. -/
theorem dijkstra_deterministic (G' : Digraph V) (s' : V) (hG : G = G') (hs : s = s') :
    dijkstra G s = dijkstra G' s' := by
  subst hG
  subst hs
  rfl

/-- **The answer is unique:** any terminated state satisfying the invariant returns exactly
the distance computed by the algorithm, so neither the tie-breaking rule nor the order in
which arcs are relaxed can change the result. -/
theorem dijkstra_result_unique {st : State V} (hst : Inv G s st) (hsel : st.select = none) :
    st.dist = dijkstra G s := by
  funext v
  exact (hst.complete hsel v).trans (dijkstra_correct v).symm

end Dijkstra
