/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.AgreesBase

/-!
# Completeness for the unordered agreement goal

The agreement encoding uses freely chosen violation selectors. Selecting a commit requires its
occurrence and excludes every matching claim. A matched commit may occur in the same run with its
selector false. This is the existential reading of `ProtSat.AuthBreak`.

`Complete.assignOf` does not allocate the agreement block: it sets every variable at or above
`bsAuth` false. The proof therefore extends the characteristic assignment while preserving every
semantic variable. The `below_*` lemmas justify transport of the ten semantic clause groups.

Two constructions are retained:

* `assignOfAg` selects every realized commit. It suffices for the special case where every committed
  triple is unclaimed (`encoding_complete_agreement_of`).
* `assignOfSelected` selects one unclaimed commit. `encoding_complete_agreement` proves completeness
  from an arbitrary bounded agreement break, without the former all-unclaimed restriction.

`encoding_correct_agreement` combines the corrected completeness theorem with `AgreesBase` soundness:

    Satisfiable (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) ↔
      boundedAttackGoals (Query.mk P B [Goal.agreement])

Its hypotheses are explicit: `univClosed`, nameable authentication annotations, and a gap-free
expression domain. Completeness itself needs only the latter two plus the bounded attack run.

This theorem concerns the unordered `ProtSat.AuthBreak` predicate used by `Query`. The ordered
reference monitor, mixed-goal conjunction, and injective agreement are separate specifications;
no equivalence to those predicates is asserted here. The AuthGap instance is obtained from the
general construction, and `AuthSelectors` checks a run containing both matched and unmatched commits.
-/

namespace ProtSat.AgreesBaseComplete
open Certificate

variable {sh : Shape}

open ProtSat Term OneHot Bounded Attacker Encode Protocol Complete Encoding AuthClauses GoalEncode AgreesBase Query BoundedExec Represent



/-- A clause list mentions only variables below N. -/
def below (N : Nat) (L : List (List Lit)) : Prop :=
  ∀ cl ∈ L, ∀ l ∈ cl, l.var < N

theorem below_nil (N : Nat) : below N [] := by
  intro cl h
  exact absurd h (by simp)

theorem below_append {N : Nat} {a b : List (List Lit)}
    (ha : below N a) (hb : below N b) : below N (a ++ b) := by
  intro cl hcl
  rw [List.mem_append] at hcl
  rcases hcl with h | h
  · exact ha cl h
  · exact hb cl h

theorem below_cons {N : Nat} (cl : List Lit) (rest : List (List Lit))
    (h1 : ∀ l ∈ cl, l.var < N) (h2 : below N rest) : below N (cl :: rest) := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact h1
  · exact h2 c hc

theorem below_flatMap_range {N : Nat} {K : Nat} {f : Nat -> List (List Lit)}
    (h : ∀ i, i < K -> below N (f i)) : below N ((List.range K).flatMap f) := by
  intro cl hcl
  rw [List.mem_flatMap] at hcl
  obtain ⟨i, hi, hcl⟩ := hcl
  exact h i (List.mem_range.mp hi) cl hcl

theorem below_map_range {N : Nat} {K : Nat} {f : Nat -> List Lit}
    (h : ∀ i, i < K -> ∀ l ∈ f i, l.var < N) : below N ((List.range K).map f) := by
  intro cl hcl
  rw [List.mem_map] at hcl
  obtain ⟨i, hi, rfl⟩ := hcl
  exact h i (List.mem_range.mp hi)

theorem below_map_list {N : Nat} {α : Type} {L : List α} {f : α -> List Lit}
    (h : ∀ x ∈ L, ∀ l ∈ f x, l.var < N) : below N (L.map f) := by
  intro cl hcl
  rw [List.mem_map] at hcl
  obtain ⟨x, hx, rfl⟩ := hcl
  exact h x hx

theorem below_flatMap_id {N : Nat} {L : List (List (List Lit))}
    (h : ∀ l ∈ L, below N l) : below N (L.flatMap id) := by
  intro cl hcl
  rw [List.mem_flatMap] at hcl
  obtain ⟨l, hl, hcl⟩ := hcl
  exact h l hl cl hcl

theorem below_cnfOf {N : Nat} {L : List (List Lit)} (h : below N L) : below N (cnfOf L).clauses := h

theorem below_filterMap {N : Nat} {K : Nat} {f : Nat -> Option (List Lit)}
    (h : ∀ i, i < K -> ∀ cl, f i = some cl -> below N [cl]) :
    below N ((List.range K).filterMap f) := by
  intro cl hcl
  rw [List.mem_filterMap] at hcl
  obtain ⟨i, hi, hf⟩ := hcl
  exact (h i (List.mem_range.mp hi) cl hf) cl (List.Mem.head _)

/-! ### index arithmetic -/

theorem hu_of_len (h : u < sh.U.length) : u < shVal sh := by
  have : shVal sh = sh.U.length + 1 := rfl
  omega
theorem hd_of_len (h : d < sh.D.length) : d < shD sh := by
  have : shD sh = sh.D.length + 1 := rfl
  omega
theorem hU1 : 1 ≤ shVal sh := by
  have : shVal sh = sh.U.length + 1 := rfl
  omega

/-! ### block chain -/

theorem bsSt_le_nVars : bsSt sh ≤ nVarsAll sh := by
  show bsSt sh ≤ bsSt sh + szSt sh + szKn sh + szEv sh + szDl sh + szFr sh + szXe sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsKn_le_nVars : bsKn sh ≤ nVarsAll sh := by
  show bsKn sh ≤ bsKn sh + szKn sh + szEv sh + szDl sh + szFr sh + szXe sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsEv_le_nVars : bsEv sh ≤ nVarsAll sh := by
  show bsEv sh ≤ bsEv sh + szEv sh + szDl sh + szFr sh + szXe sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsDl_le_nVars : bsDl sh ≤ nVarsAll sh := by
  show bsDl sh ≤ bsDl sh + szDl sh + szFr sh + szXe sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsFr_le_nVars : bsFr sh ≤ nVarsAll sh := by
  show bsFr sh ≤ bsFr sh + szFr sh + szXe sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsXe_le_nVars : bsXe sh ≤ nVarsAll sh := by
  show bsXe sh ≤ bsXe sh + szXe sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsTotal_le_nVars : bsTotal sh ≤ nVarsAll sh := by
  show bsTotal sh ≤ bsTotal sh + szApc sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsAst_le_nVars : bsAst sh ≤ nVarsAll sh := by
  show bsAst sh ≤ bsAst sh + szAst sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsAxe_le_nVars : bsAxe sh ≤ nVarsAll sh := by
  show bsAxe sh ≤ bsAxe sh + szAxe sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsAev_le_nVars : bsAev sh ≤ nVarsAll sh := by
  show bsAev sh ≤ bsAev sh + szAev sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsAdl_le_nVars : bsAdl sh ≤ nVarsAll sh := by
  show bsAdl sh ≤ bsAdl sh + szAdl sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsAfr_le_nVars : bsAfr sh ≤ nVarsAll sh := by
  show bsAfr sh ≤ bsAfr sh + szAfr sh + szPb sh + szAu sh
  omega
theorem bsAfterAux_le_nVars : bsAfterAux sh ≤ nVarsAll sh := by
  show bsAfterAux sh ≤ bsAfterAux sh + szPb sh + szAu sh
  omega
theorem bsAu_le_nVars : bsAu sh ≤ nVarsAll sh := by
  show bsAu sh ≤ bsAu sh + szAu sh
  omega
theorem bsAu_le_nVars2 : bsAu sh ≤ nVarsAll sh := Nat.le_add_right _ _

theorem vpc_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (hc : c < shPc sh) :
    vpc sh i q c < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vpc_lt_bsSt sh i q c hi hq hc) bsSt_le_nVars
theorem vst_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hu : u < shVal sh) :
    vst sh i q x u < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vst_lt_bsKn sh i q x u hi hq hx hu) bsKn_le_nVars
theorem vkn_lt_nVars (hi : i ≤ sh.steps) (hu : u < shVal sh) : vkn sh i u < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vkn_lt_bsEv sh i u hi hu) bsEv_le_nVars
theorem vev_lt_nVars (hi : i < sh.steps) (hk : k < shEv sh) : vev sh i k < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vev_lt_bsDl sh i k hi hk) bsDl_le_nVars
theorem vdl_lt_nVars (hi : i < sh.steps) (hq : q < shS sh) (hu : u < shVal sh) :
    vdl sh i q u < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vdl_lt_bsFr sh i q u hi hq hu) bsFr_le_nVars
theorem vfr_lt_nVars (hi : i < sh.steps) (hq : q < shS sh) (hd : d < shD sh) :
    vfr sh i q d < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vfr_lt_bsXe sh i q d hi hq hd) bsXe_le_nVars
theorem vxe_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hu : u < shVal sh) :
    vxe sh i q e u < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vxe_lt_bsTotal sh i q e u hi hq he hu) bsTotal_le_nVars
theorem vpb_lt_nVars (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh) (hu : u < shVal sh) :
    vpb sh i q c u < nVarsAll sh :=
  Nat.lt_of_lt_of_le (vpb_lt_bsAu sh i q c u hi hq hc hu) bsAu_le_nVars
theorem vau_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hu : u < shVal sh) :
    vau sh i q x u < nVarsAll sh := vau_lt_nVarsAll sh i q x u hi hq hx hu
theorem apc_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (hj : j < shPc sh) :
    apc sh i q j < nVarsAll sh :=
  Nat.lt_of_lt_of_le (apc_lt_bsAst sh i q j hi hq hj) bsAst_le_nVars
theorem ast_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (hx : x < shV sh) (hj : j < shVal sh) :
    ast sh i q x j < nVarsAll sh :=
  Nat.lt_of_lt_of_le (ast_lt_bsAxe sh i q x j hi hq hx hj) bsAxe_le_nVars
theorem axe_lt_nVars (hi : i ≤ sh.steps) (hq : q < shS sh) (he : e < shE sh) (hj : j < shVal sh) :
    axe sh i q e j < nVarsAll sh :=
  Nat.lt_of_lt_of_le (axe_lt_bsAev sh i q e j hi hq he hj) bsAev_le_nVars
theorem aev_lt_nVars (hi : i < sh.steps) (hj : j < shEv sh) : aev sh i j < nVarsAll sh :=
  Nat.lt_of_lt_of_le (aev_lt_bsAdl sh i j hi hj) bsAdl_le_nVars
theorem adl_lt_nVars (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shVal sh) :
    adl sh i q j < nVarsAll sh :=
  Nat.lt_of_lt_of_le (adl_lt_bsAfr sh i q j hi hq hj) bsAfr_le_nVars
theorem afr_lt_nVars (hi : i < sh.steps) (hq : q < shS sh) (hj : j < shD sh) :
    afr sh i q j < nVarsAll sh :=
  Nat.lt_of_lt_of_le (afr_lt_bsAfterAux sh i q j hi hq hj) bsAfterAux_le_nVars
theorem evAct_lt_nVars (hi : i < sh.steps) (hq : q < shS sh) : evAct sh i q < nVarsAll sh := by
  show vev sh i (1 + q) < nVarsAll sh
  exact vev_lt_nVars hi (by
    have h : shEv sh = 1 + shS sh + nInst sh := rfl
    omega)
theorem evDed_lt_nVars (hi : i < sh.steps) (hn : n < nInst sh) : evDed sh i n < nVarsAll sh := by
  show vev sh i (1 + shS sh + n) < nVarsAll sh
  exact vev_lt_nVars hi (by
    have h : shEv sh = 1 + shS sh + nInst sh := rfl
    omega)

/-! ### The transfer -/

theorem clause_eval_congr {a a' : Assignment} (N : Nat) : ∀ (cl : List Lit),
    (∀ l ∈ cl, l.var < N) -> (∀ v, v < N -> a v = a' v) -> Clause.eval a cl = Clause.eval a' cl := by
  intro cl
  induction cl with
  | nil => intro _ _; rfl
  | cons l rest ih =>
      intro h1 h2
      have hv : l.var < N := h1 l (List.Mem.head _)
      have hl : l.eval a = l.eval a' := by
        cases l with
        | mk v n =>
            have h := h2 v hv
            cases n <;> simp [Lit.eval, h]
      have ha : Clause.eval a (l :: rest) = (l.eval a || Clause.eval a rest) := rfl
      have ha' : Clause.eval a' (l :: rest) = (l.eval a' || Clause.eval a' rest) := rfl
      rw [ha, ha', hl, ih (fun l' hl' => h1 l' (List.Mem.tail _ hl')) h2]

theorem sat_congr {f : CNF} {a a' : Assignment} (N : Nat)
    (hb : below N f.clauses) (h : ∀ v, v < N -> a v = a' v) :
    Sat a f -> Sat a' f := by
  intro hsa cl hcl
  have hEq := clause_eval_congr N cl (hb cl hcl) h
  rw [← hEq]
  exact hsa cl hcl

/-! ### one-hot groups -/

theorem atMostOneSeq_below : ∀ (vs : List BVar) (s : Nat -> BVar) (N : Nat),
    (∀ v ∈ vs, v < N) -> (∀ j, j < vs.length -> s j < N) -> below N (atMostOneSeq vs s) := by
  intro vs
  induction vs with
  | nil => intro s N _ _; exact below_nil N
  | cons x rest ih =>
      intro s N hx hN
      cases rest with
      | nil => exact below_nil N
      | cons y rest2 =>
          cases rest2 with
          | nil =>
              have h0 : 0 < (x :: y :: []).length := by
                have : (x :: y :: []).length = 2 := rfl
                omega
              intro cl hcl
              rw [atMostOneSeq_two] at hcl
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
              rcases hcl with rfl | rfl
              · intro l hl
                rw [List.mem_cons, List.mem_singleton] at hl
                rcases hl with rfl | rfl
                · exact hx x (List.Mem.head _)
                · exact hN 0 h0
              · intro l hl
                rw [List.mem_cons, List.mem_singleton] at hl
                rcases hl with rfl | rfl
                · exact hx y (List.Mem.tail _ (List.Mem.head _))
                · exact hN 0 h0
          | cons w rest3 =>
              have hlen : (x :: y :: w :: rest3).length = rest3.length + 3 := rfl
              have hlen2 : (y :: w :: rest3).length = rest3.length + 2 := rfl
              have h0 : 0 < (x :: y :: w :: rest3).length := by rw [hlen]; omega
              have h1 : 1 < (x :: y :: w :: rest3).length := by rw [hlen]; omega
              intro cl hcl
              rw [atMostOneSeq_three] at hcl
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
              rcases hcl with rfl | rfl | rfl | hcl
              · intro l hl
                rw [List.mem_cons, List.mem_singleton] at hl
                rcases hl with rfl | rfl
                · exact hx x (List.Mem.head _)
                · exact hN 0 h0
              · intro l hl
                rw [List.mem_cons, List.mem_singleton] at hl
                rcases hl with rfl | rfl
                · exact hx y (List.Mem.tail _ (List.Mem.head _))
                · exact hN 0 h0
              · intro l hl
                rw [List.mem_cons, List.mem_singleton] at hl
                rcases hl with rfl | rfl
                · exact hN 0 h0
                · exact hN 1 h1
              · exact (ih (fun j => s (j + 1)) N
                    (fun v hv => hx v (List.mem_cons.mpr (Or.inr hv)))
                    (fun j hj => hN (j + 1) (by rw [hlen]; omega))) cl hcl

theorem ohOf_below {N : Nat} (f : Nat -> Nat) (K : Nat) (hK : 0 < K)
    (inj : ∀ x y, x < K -> y < K -> f x = f y -> x = y) (aux : Nat -> Nat)
    (hf : ∀ c, c < K -> f c < N) (haux : ∀ j, j < K -> aux j < N) :
    below N ((ohOf f K hK inj aux).clauses.clauses) := by
  have hlen : ((List.range K).map f).length = K := by
    rw [List.length_map, List.length_range]
  have h1 : (ohOf f K hK inj aux).clauses.clauses =
      (atLeastOne ((List.range K).map f)).clauses ++ atMostOneSeq ((List.range K).map f) aux := rfl
  rw [h1]
  refine below_append ?_ ?_
  · intro cl hcl
    have h2 : (atLeastOne ((List.range K).map f)).clauses = [((List.range K).map f).map pos] := rfl
    rw [h2] at hcl
    rw [List.mem_singleton] at hcl
    subst hcl
    intro l hl
    rw [List.mem_map] at hl
    obtain ⟨y, hy, rfl⟩ := hl
    rw [List.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact hf c (List.mem_range.mp hc)
  · refine atMostOneSeq_below ((List.range K).map f) aux N ?_ ?_
    · intro v hv
      rw [List.mem_map] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      exact hf c (List.mem_range.mp hc)
    · intro j hj
      refine haux j ?_
      rw [← hlen]
      exact hj

theorem ohPc_below : below (nVarsAll sh) (ohPcClauses sh) := by
  unfold ohPcClauses
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  show below (nVarsAll sh) ((pcOh sh i q).clauses.clauses)
  exact ohOf_below (fun c => vpc sh i q c) (shPc sh) (shPc_pos sh)
    (fun x y hx hy h => vpc_inj hx hy h) (fun j => apc sh i q j)
    (fun c hc => vpc_lt_nVars (by omega : i ≤ sh.steps)
      hq hc)
    (fun j hj => apc_lt_nVars (by omega : i ≤ sh.steps)
      hq hj)

theorem ohSt_below : below (nVarsAll sh) (ohStClauses sh) := by
  unfold ohStClauses
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  refine below_flatMap_range (fun x hx => ?_)
  show below (nVarsAll sh) ((stOh sh i q x).clauses.clauses)
  exact ohOf_below (fun u => vst sh i q x u) (shVal sh) (shVal_pos sh)
    (fun a b ha hb h => vst_inj ha hb h) (fun j => ast sh i q x j)
    (fun u hu => vst_lt_nVars (by omega : i ≤ sh.steps)
      hq hx hu)
    (fun j hj => ast_lt_nVars (by omega : i ≤ sh.steps)
      hq hx hj)

theorem ohXe_below : below (nVarsAll sh) (ohXeClauses sh) := by
  unfold ohXeClauses
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  refine below_flatMap_range (fun e he => ?_)
  show below (nVarsAll sh) ((xeOh sh i q e).clauses.clauses)
  exact ohOf_below (fun u => vxe sh i q e u) (shVal sh) (shVal_pos sh)
    (fun a b ha hb h => vxe_inj ha hb h) (fun j => axe sh i q e j)
    (fun u hu => vxe_lt_nVars (by omega : i ≤ sh.steps)
      hq he hu)
    (fun j hj => axe_lt_nVars (by omega : i ≤ sh.steps)
      hq he hj)

theorem ohEv_below : below (nVarsAll sh) (ohEvClauses sh) := by
  unfold ohEvClauses
  refine below_flatMap_range (fun i hi => ?_)
  show below (nVarsAll sh) ((evOh sh i).clauses.clauses)
  exact ohOf_below (fun k => vev sh i k) (shEv sh) (shEv_pos sh)
    (fun x y hx hy h => vev_inj hx hy h) (fun j => aev sh i j)
    (fun k hk => vev_lt_nVars (by omega : i < sh.steps) hk)
    (fun j hj => aev_lt_nVars (by omega : i < sh.steps) hj)

theorem ohDl_below : below (nVarsAll sh) (ohDlClauses sh) := by
  unfold ohDlClauses
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  show below (nVarsAll sh) ((dlOh sh i q).clauses.clauses)
  exact ohOf_below (fun u => vdl sh i q u) (shVal sh) (shVal_pos sh)
    (fun a b ha hb h => vdl_inj ha hb h) (fun j => adl sh i q j)
    (fun u hu => vdl_lt_nVars (by omega : i < sh.steps)
      hq hu)
    (fun j hj => adl_lt_nVars (by omega : i < sh.steps)
      hq hj)

theorem ohFr_below : below (nVarsAll sh) (ohFrClauses sh) := by
  unfold ohFrClauses
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  show below (nVarsAll sh) ((frOh sh i q).clauses.clauses)
  exact ohOf_below (fun d => vfr sh i q d) (shD sh) (shD_pos sh)
    (fun a b ha hb h => vfr_inj ha hb h) (fun j => afr sh i q j)
    (fun d hd => vfr_lt_nVars (by omega : i < sh.steps)
      hq hd)
    (fun j hj => afr_lt_nVars (by omega : i < sh.steps)
      hq hj)

theorem below_oneHot {P : Protocol} : below (nVarsAll sh) (oneHotClauses sh P).clauses := by
  unfold oneHotClauses
  refine below_cnfOf (below_flatMap_id ?_)
  intro l hl
  rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons,
    List.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ohPc_below
  · exact ohSt_below
  · exact ohXe_below
  · exact ohEv_below
  · exact ohDl_below
  · exact ohFr_below


/-! ### The agreement auxiliaries are out of reach of assignOf -/

theorem asgAu_ge {sh : Shape} {P : Protocol} {cfg : Nat -> Cfg} {ev : Nat -> Ev} {v : BVar}
    (h : nVarsAll sh ≤ v) : asgAu sh P cfg ev v = false := by
  unfold asgAu
  refine Bool.eq_false_of_ne_true ?_
  intro htrue
  rw [List.any_eq_true] at htrue
  obtain ⟨i, hi, htrue⟩ := htrue
  rw [List.any_eq_true] at htrue
  obtain ⟨q, hq, htrue⟩ := htrue
  rw [List.any_eq_true] at htrue
  obtain ⟨x, hx, htrue⟩ := htrue
  rw [List.any_eq_true] at htrue
  obtain ⟨u, hu, htrue⟩ := htrue
  rw [Bool.and_eq_true] at htrue
  obtain ⟨hveq, _⟩ := htrue
  have h2 : v = vau sh i q x u := decide_eq_true_eq.mp hveq
  have hi' : i ≤ sh.steps := by
    have := List.mem_range.mp hi
    omega
  have hlt := vau_lt_nVarsAll sh i q x u hi' (List.mem_range.mp hq)
      (List.mem_range.mp hx) (List.mem_range.mp hu)
  have hlt' : v < nVarsAll sh := by rw [h2]; exact hlt
  exact absurd hlt' (Nat.not_lt_of_le h)

theorem bsSt_le_bsAuth : bsSt sh ≤ bsAuth sh := bsSt_le_nVars
theorem bsKn_le_bsAuth : bsKn sh ≤ bsAuth sh := bsKn_le_nVars
theorem bsEv_le_bsAuth : bsEv sh ≤ bsAuth sh := bsEv_le_nVars
theorem bsDl_le_bsAuth : bsDl sh ≤ bsAuth sh := bsDl_le_nVars
theorem bsFr_le_bsAuth : bsFr sh ≤ bsAuth sh := bsFr_le_nVars
theorem bsXe_le_bsAuth : bsXe sh ≤ bsAuth sh := bsXe_le_nVars
theorem bsTotal_le_bsAuth : bsTotal sh ≤ bsAuth sh := bsTotal_le_nVars
theorem bsAst_le_bsAuth : bsAst sh ≤ bsAuth sh := bsAst_le_nVars
theorem bsAxe_le_bsAuth : bsAxe sh ≤ bsAuth sh := bsAxe_le_nVars
theorem bsAev_le_bsAuth : bsAev sh ≤ bsAuth sh := bsAev_le_nVars
theorem bsAdl_le_bsAuth : bsAdl sh ≤ bsAuth sh := bsAdl_le_nVars
theorem bsAfr_le_bsAuth : bsAfr sh ≤ bsAuth sh := bsAfr_le_nVars
theorem bsAfterAux_le_bsAuth : bsAfterAux sh ≤ bsAuth sh := bsAfterAux_le_nVars
theorem bsAu_le_bsAuth : bsAu sh ≤ bsAuth sh := bsAu_le_nVars

/-- **The finding the task's route runs into.** The agreement auxiliaries live strictly above every
block the characteristic assignment knows about, so \textsf{assignOf} itself sets every one of them
false: the completeness witness cannot be \textsf{assignOf}, it has to be an extension of it. -/
theorem not_lt_bsAuth {sh : Shape} {v X : Nat} (hX : X ≤ bsAuth sh) (h : bsAuth sh ≤ v) :
    ¬ (v < X) := by
  intro hlt
  omega

theorem assignOf_ge_bsAuth {sh : Shape} {P : Protocol} {cfg : Nat -> Cfg} {ev : Nat -> Ev}
    {v : BVar} (h : bsAuth sh ≤ v) : assignOf sh P cfg ev v = false := by
  rw [assignOf,
    ite_eq_right (not_lt_bsAuth bsSt_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsKn_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsEv_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsDl_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsFr_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsXe_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsTotal_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAst_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAxe_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAev_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAdl_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAfr_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAfterAux_le_bsAuth h),
    ite_eq_right (not_lt_bsAuth bsAu_le_bsAuth h)]
  exact asgAu_ge h

/-! ### The witness assignment -/

/-- The Tseitin value of the commit conjunction named by a variable of the agreement block. -/
def authAux (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) (v : BVar) : Bool :=
  match rget (authOccs sh P true) (v - bsAuth sh) with
  | some o => (authOccLits sh P o).all (fun l => l.eval (assignOf sh P cfg ev) = true)
  | none => false

/-- **The completeness witness for the agreement encoding.** -/
def assignOfAg (sh : Shape) (P : Protocol) (cfg : Nat -> Cfg) (ev : Nat -> Ev) : Assignment :=
  fun v => if v < bsAuth sh then assignOf sh P cfg ev v else authAux sh P cfg ev v

theorem assignOfAg_below {sh : Shape} {P : Protocol} {cfg : Nat -> Cfg} {ev : Nat -> Ev}
    {v : BVar} (hv : v < bsAuth sh) :
    assignOfAg sh P cfg ev v = assignOf sh P cfg ev v := by
  simp [assignOfAg, hv]

theorem assignOfAg_aux {sh : Shape} {P : Protocol} {cfg : Nat -> Cfg} {ev : Nat -> Ev}
    {v : BVar} (hv : bsAuth sh ≤ v) :
    assignOfAg sh P cfg ev v = authAux sh P cfg ev v := by
  simp [assignOfAg, hv]

theorem authAux_authOccVar {sh : Shape} {P : Protocol} {cfg : Nat -> Cfg} {ev : Nat -> Ev}
    {o : AuthOcc} (ho : o ∈ authOccs sh P true) :
    authAux sh P cfg ev (authOccVar sh P o) =
      (authOccLits sh P o).all (fun l => l.eval (assignOf sh P cfg ev) = true) := by
  unfold authAux
  have h2 : authOccVar sh P o - bsAuth sh = ixOf o (authOccs sh P true) :=
    Nat.add_sub_cancel_left (bsAuth sh) (ixOf o (authOccs sh P true))
  rw [h2, rget_ixOf _ _ ho]

theorem assignOfAg_aux_iff {sh : Shape} {P : Protocol} {cfg : Nat -> Cfg} {ev : Nat -> Ev}
    {o : AuthOcc} (ho : o ∈ authOccs sh P true) :
    (assignOfAg sh P cfg ev (authOccVar sh P o) = true) <->
      (∀ l ∈ authOccLits sh P o, l.eval (assignOf sh P cfg ev) = true) := by
  have hle : bsAuth sh ≤ authOccVar sh P o := by
    show bsAuth sh ≤ bsAuth sh + ixOf o (authOccs sh P true)
    exact Nat.le_add_right _ _
  rw [assignOfAg_aux hle, authAux_authOccVar ho]
  constructor
  · intro h l hl
    have h2 := h
    simp only [List.all_eq_true, decide_eq_true_eq] at h2 ⊢
    exact h2 l hl
  · intro h
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact h

/-! ### Literal evaluation is local -/

theorem lit_eval_congr {a a' : Assignment} {l : Lit} (h : a l.var = a' l.var) :
    l.eval a = l.eval a' := by
  cases l with
  | mk v n =>
      have hv := h
      cases n <;> simp [Lit.eval, hv]

/-! ### Reading a run by position -/

theorem rget_cfgAt : ∀ (Cs : List Cfg) (i : Nat), i < Cs.length ->
    rget Cs i = some (cfgAt Cs i) := by
  intro Cs
  induction Cs with
  | nil => intro i h; exact absurd h (by simp)
  | cons C rest ih =>
      intro i hi
      cases i with
      | zero =>
          have hlen : (C :: rest).length = rest.length + 1 := rfl
          rw [cfgAt_head]
          exact rget_zero C rest
      | succ k =>
          by_cases hne : rest = []
          · subst hne
            simp at hi
          · rw [cfgAt_cons_succ hne k, rget_succ]
            exact ih k (by
              have hlen : (C :: rest).length = rest.length + 1 := rfl
              omega)

theorem evAt_eq_of_rget : ∀ (tr : List Ev) (i : Nat) (e : Ev), rget tr i = some e ->
    evAt tr i = e := by
  intro tr
  induction tr with
  | nil => intro i e h; exact absurd h (by simp [rget])
  | cons x rest ih =>
      intro i e h
      cases i with
      | zero =>
          have hx : x = e := Option.some.inj h
          rw [← hx]
          exact evAt_head
      | succ k =>
          rw [evAt_cons_succ]
          exact ih k e (by simpa [rget] using h)

theorem rget_zip_cfgAt_evAt {Cs : List Cfg} {tr : List Ev} {i : Nat}
    (hi : i < tr.length) (hlen : Cs.length = tr.length + 1) :
    rget (Cs.zip tr) i = some (cfgAt Cs i, evAt tr i) := by
  rw [AgreesBase.rget_zip]
  refine ⟨?_, ?_⟩
  · rw [rget_cfgAt Cs i (by omega)]
  · obtain ⟨e, he⟩ := rget_lt tr i hi
    rw [evAt_eq_of_rget tr i e he]
    exact he

/-! ### The construction reflects the clauses -/

/-- The four literals of an authentication occurrence name variables of the semantic blocks, so the
extension below 	extsf{assignOf} does not disturb them. -/
theorem authOccLits_below {P : Protocol} {B : Bounds} {commit : Bool} {o : AuthOcc}
    (ho : o ∈ authOccs (shapeOf P B) P commit)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B)) :
    ∀ l ∈ authOccLits (shapeOf P B) P o, l.var < bsAuth (shapeOf P B) := by
  intro l hl
  obtain ⟨hpos, hcommit, hstep, hidx⟩ := AgreesBase.authOccs_elim ho
  obtain ⟨hlt, hpc, hact⟩ := AgreesBase.mem_authPositions hpos
  have hnS1 : o.pos.sess < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hlt
  have hshS : o.pos.sess < shS (shapeOf P B) := lt_shS hnS1
  have hshPc : o.pos.pc < shPc (shapeOf P B) := by
    have hle := roleLen_le_nPc1 hnS1
    show o.pos.pc < (shapeOf P B).nPc1 + 1
    omega
  have huV : o.data < shVal (shapeOf P B) := by
    obtain ⟨a, d, hm, hd, hp⟩ := authOccMsgs_of_mem ho
    rw [hd]
    exact uIdx_lt' _ _
  have hpV : o.peerVal < shVal (shapeOf P B) := by
    obtain ⟨a, d, hm, hd, hp⟩ := authOccMsgs_of_mem ho
    rw [hp]
    exact uIdx_lt' _ _
  have hv : o.pos.val ∈ allExprs P ∧ o.pos.peer ∈ allExprs P := by
    rcases hact with ⟨hisc, hA⟩ | ⟨hisc, hA⟩
    · exact (mem_allExprs_commit hA).symm
    · exact (mem_allExprs_claim hA).symm
  rw [authOccLits, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · show evAct (shapeOf P B) o.step o.pos.sess < bsAuth (shapeOf P B)
    rw [bsAuth]
    exact evAct_lt_nVars hstep hshS
  · show vpc (shapeOf P B) o.step o.pos.sess o.pos.pc < bsAuth (shapeOf P B)
    rw [bsAuth]
    exact vpc_lt_nVars (by omega : o.step ≤ (shapeOf P B).steps) hshS hshPc
  · show vxe (shapeOf P B) o.step o.pos.sess (eIdx P o.pos.val) o.data < bsAuth (shapeOf P B)
    rw [bsAuth]
    exact vxe_lt_nVars (by omega : o.step ≤ (shapeOf P B).steps) hshS (heIdx o.pos.val hv.1) huV
  · show vxe (shapeOf P B) o.step o.pos.sess (eIdx P o.pos.peer) o.peerVal < bsAuth (shapeOf P B)
    rw [bsAuth]
    exact vxe_lt_nVars (by omega : o.step ≤ (shapeOf P B).steps) hshS (heIdx o.pos.peer hv.2) hpV

/-! ### The construction reflects the clauses -/

/-- The literals of an occurrence are evaluated the same way by the characteristic assignment and by
its agreement extension. -/
theorem authOccLits_eval_ag {P : Protocol} {B : Bounds} {commit : Bool} {o : AuthOcc}
    {cfg : Nat -> Cfg} {ev : Nat -> Ev} (ho : o ∈ authOccs (shapeOf P B) P commit)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B)) :
    ∀ l ∈ authOccLits (shapeOf P B) P o,
      l.eval (assignOfAg (shapeOf P B) P cfg ev) =
        l.eval (assignOf (shapeOf P B) P cfg ev) := by
  intro l hl
  exact lit_eval_congr (assignOfAg_below (authOccLits_below ho heIdx l hl))

/-! ### Reading an authentication action -/

/-- A claim step only ever produces an instance flagged as a claim. -/
theorem authOfStep_isCommit_of_claim {P : Protocol} {C : Cfg} {q : Nat} {m : Term} {d : NonceName}
    {tag : Tag} {peer v : Expr} {y : AuthInst}
    (hA : P.actionAt q (pcOf C q) = some (Action.claim tag peer v))
    (h : y ∈ authOfStep P C (Ev.act q m d)) : y.isCommit = false := by
  have hred : authOfStep P C (Ev.act q m d) =
      (match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
      | some (Term.agent A), some val => [{ isCommit := false, tag := tag, peer := A, val}]
      | _, _ => []) := by
    simp only [authOfStep, hA]
    rfl
  rw [hred] at h
  cases hpe : Expr.eval peer (storeOf C q) with
  | none => rw [hpe] at h; simp at h
  | some tv =>
      cases hv : Expr.eval v (storeOf C q) with
      | none => rw [hpe, hv] at h; simp at h
      | some val =>
          cases tv with
          | agent A =>
              rw [hpe, hv] at h
              rw [List.mem_singleton] at h
              subst h
              rfl
          | nonce _ | key _ | pair _ _ | encS _ _ | encA _ _ | hash _ =>
              rw [hpe, hv] at h; simp at h


/-- The authentication action the flag selects. -/
def authAction (b : Bool) (tag : Tag) (peer v : Expr) : Action :=
  if b then Action.commit tag peer v else Action.claim tag peer v

theorem authAction_false {tag : Tag} {peer v : Expr} : authAction false tag peer v =
    Action.claim tag peer v := by
  simp [authAction]

theorem authAction_true {tag : Tag} {peer v : Expr} : authAction true tag peer v =
    Action.commit tag peer v := by
  simp [authAction]

/-- What an authentication step of the run tells, uniformly in the commit flag. -/
theorem authOfStep_authAction {P : Protocol} {C : Cfg} {q : Nat} {m : Term} {d : NonceName}
    {b : Bool} {tag : Tag} {peer v : Expr} {y : AuthInst}
    (hA : P.actionAt q (pcOf C q) = some (authAction b tag peer v))
    (hy : y ∈ authOfStep P C (Ev.act q m d)) :
    ∃ (A : Agent) (val : Term),
      Expr.eval peer (storeOf C q) = some (Term.agent A) ∧
        Expr.eval v (storeOf C q) = some val ∧
        y.tag = tag ∧ y.peer = A ∧ y.val = val ∧ y.isCommit = b := by
  cases b with
  | false =>
      rw [authAction_false] at hA
      obtain ⟨A, val, h1, h2, h3, h4, h5⟩ := AgreesBase.authOfStep_claim_elim hA hy
      exact ⟨A, val, h1, h2, h3, h4, h5, authOfStep_isCommit_of_claim hA hy⟩
  | true =>
      rw [authAction_true] at hA
      have hred : authOfStep P C (Ev.act q m d) =
          (match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
          | some (Term.agent A), some val => [{ isCommit := true, tag := tag, peer := A, val}]
          | _, _ => []) := by
        simp only [authOfStep, hA]
        rfl
      rw [hred] at hy
      cases hpe : Expr.eval peer (storeOf C q) with
      | none => rw [hpe] at hy; simp at hy
      | some tv =>
          cases hv : Expr.eval v (storeOf C q) with
          | none => rw [hpe, hv] at hy; simp at hy
          | some val =>
              cases tv with
              | agent A =>
                  rw [hpe, hv] at hy
                  rw [List.mem_singleton] at hy
                  subst hy
                  exact ⟨A, val, rfl, rfl, rfl, rfl, rfl, rfl⟩
              | nonce _ | key _ | pair _ _ | encS _ _ | encA _ _ | hash _ =>
                  rw [hpe, hv] at hy; simp at hy

/-- **The construction side of the commit half of the bridge.** If the characteristic assignment
makes the four literals of an authentication occurrence true, the run performs that occurrence:
the instance is in the trace, it is a commit exactly when the occurrence says it is, and the triple
the occurrence records is the triple the instance carries. Only two of the four literals are read:
the session acts, and its program counter is the position's. -/
theorem instance_of_lits_true {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs)
    {commit : Bool} {o : AuthOcc} (ho : o ∈ authOccs (shapeOf P B) P commit)
    (hall : ∀ l ∈ authOccLits (shapeOf P B) P o,
        l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true) :
    ∃ x ∈ authInsts P Cs tr, x.isCommit = commit ∧
      authTriple (shapeOf P B) o = some (x.tag, x.peer, x.val) := by
  obtain ⟨hpos, hcommit, hstep, hidx⟩ := AgreesBase.authOccs_elim ho
  obtain ⟨hlt, hpc, hact⟩ := AgreesBase.mem_authPositions hpos
  have hnS1 : o.pos.sess < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hlt
  have hshS : o.pos.sess < shS (shapeOf P B) := lt_shS hnS1
  have hshPc : o.pos.pc < shPc (shapeOf P B) := by
    have hle := roleLen_le_nPc1 hnS1
    show o.pos.pc < (shapeOf P B).nPc1 + 1
    omega
  have h1 : (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
      (evAct (shapeOf P B) o.step o.pos.sess)) = true := by
    have := hall (pos (evAct (shapeOf P B) o.step o.pos.sess)) (by simp [authOccLits])
    simpa using this
  have hrd' : decide (rdEv (shapeOf P B) P (cfgAt Cs) (evAt tr) o.step = 1 + o.pos.sess) = true := by
    rw [← assignOf_evAct (shapeOf P B) P (cfgAt Cs) (evAt tr) hstep hshS]
    exact h1
  have hrd := decide_eq_true_eq.mp hrd'
  obtain ⟨m, d, hev⟩ := (evActs (shapeOf P B) P (cfgAt Cs) (evAt tr) hshS).mpr hrd
  have h2 : (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
      (vpc (shapeOf P B) o.step o.pos.sess o.pos.pc)) = true := by
    have := hall (pos (vpc (shapeOf P B) o.step o.pos.sess o.pos.pc)) (by simp [authOccLits])
    simpa using this
  have hpc'' : decide (rdPc (shapeOf P B) P (cfgAt Cs) (evAt tr) o.step o.pos.sess = o.pos.pc) =
      true := by
    rw [← assignOf_pc (shapeOf P B) P (cfgAt Cs) (evAt tr)
      (by omega : o.step ≤ (shapeOf P B).steps) hshS hshPc]
    exact h2
  have hpc' : pcOf (cfgAt Cs o.step) o.pos.sess = o.pos.pc := decide_eq_true_eq.mp hpc''
  have hlenCs : Cs.length = tr.length + 1 := runs_length hbt.1
  have hstep' : o.step < tr.length := by
    by_contra he
    rw [evAt_past o.step (by omega)] at hev
    exact absurd hev (by simp)
  obtain ⟨A, d', hm, hd, hp⟩ := authOccMsgs_of_mem ho
  have hcv := AgreesBase.authOccMsgs_some hm
  have hcp := AgreesBase.constVal_closed hcv.1
  have hcv2 := AgreesBase.constVal_closed hcv.2.1
  have hb : o.pos.isCommit = commit := by simpa using hcommit
  have hcmt : (commit = true ∧
      P.actionAt o.pos.sess o.pos.pc = some (Action.commit o.pos.tag o.pos.peer o.pos.val)) ∨
      (commit = false ∧
      P.actionAt o.pos.sess o.pos.pc = some (Action.claim o.pos.tag o.pos.peer o.pos.val)) := by
    rcases hact with ⟨hisc, hact'⟩ | ⟨hisc, hact'⟩
    · exact Or.inl ⟨by rw [← hb, hisc], hact'⟩
    · exact Or.inr ⟨by rw [← hb, hisc], hact'⟩
  have hA : P.actionAt o.pos.sess o.pos.pc =
      some (authAction commit o.pos.tag o.pos.peer o.pos.val) := by
    rcases hcmt with ⟨rfl, hact'⟩ | ⟨rfl, hact'⟩
    · rw [authAction_true, hact']
    · rw [authAction_false, hact']
  have hstep'' : authOfStep P (cfgAt Cs o.step) (evAt tr o.step) =
      [{ isCommit := commit, tag := o.pos.tag, peer := A, val := d'}] := by
    rcases hcmt with ⟨(rfl : commit = true), hact''⟩ | ⟨(rfl : commit = false), hact''⟩
    · have hred : authOfStep P (cfgAt Cs o.step) (evAt tr o.step) =
          (match Expr.eval o.pos.peer (storeOf (cfgAt Cs o.step) o.pos.sess),
                 Expr.eval o.pos.val (storeOf (cfgAt Cs o.step) o.pos.sess) with
          | some (Term.agent A''), some val' =>
              [{ isCommit := true, tag := o.pos.tag, peer := A'', val := val'}]
          | _, _ => []) := by
        rw [hev]
        simp only [authOfStep, hpc', hact'']
        rfl
      rw [hred,
        eval_eq_constVal o.pos.peer (storeOf (cfgAt Cs o.step) o.pos.sess)
          hcp.1 hcp.2.1 hcp.2.2,
        eval_eq_constVal o.pos.val (storeOf (cfgAt Cs o.step) o.pos.sess)
          hcv2.1 hcv2.2.1 hcv2.2.2, hcv.1, hcv.2.1]
    · have hred : authOfStep P (cfgAt Cs o.step) (evAt tr o.step) =
          (match Expr.eval o.pos.peer (storeOf (cfgAt Cs o.step) o.pos.sess),
                 Expr.eval o.pos.val (storeOf (cfgAt Cs o.step) o.pos.sess) with
          | some (Term.agent A''), some val' =>
              [{ isCommit := false, tag := o.pos.tag, peer := A'', val := val'}]
          | _, _ => []) := by
        rw [hev]
        simp only [authOfStep, hpc', hact'']
        rfl
      rw [hred,
        eval_eq_constVal o.pos.peer (storeOf (cfgAt Cs o.step) o.pos.sess)
          hcp.1 hcp.2.1 hcp.2.2,
        eval_eq_constVal o.pos.val (storeOf (cfgAt Cs o.step) o.pos.sess)
          hcv2.1 hcv2.2.1 hcv2.2.2, hcv.1, hcv.2.1]

  have hzip : rget (Cs.zip tr) o.step = some (cfgAt Cs o.step, evAt tr o.step) :=
    rget_zip_cfgAt_evAt hstep' hlenCs
  have hmem : (cfgAt Cs o.step, evAt tr o.step) ∈ Cs.zip tr :=
    rget_some_mem (Cs.zip tr) o.step _ hzip
  have hinst : ({ isCommit := commit, tag := o.pos.tag, peer := A, val := d'} : AuthInst) ∈
      authInsts P Cs tr := by
    unfold authInsts
    rw [List.mem_flatten]
    refine ⟨_, List.mem_map.mpr ⟨(cfgAt Cs o.step, evAt tr o.step), hmem, rfl⟩, ?_⟩
    rw [hstep'']
    simp
  refine ⟨_, hinst, rfl, ?_⟩
  · unfold authTriple
    rw [hm]
    rfl

/-! ### The run performs an occurrence -/

/-- **The construction side of the claim half of the bridge.** A nameable authentication event of the
run is an occurrence of the model all four of whose literals the characteristic assignment makes
true: the event literal from \textsf{assignOf\_evAct}, the program-counter literal from
\textsf{assignOf\_pc}, and the two value literals from \textsf{assignOf\_xe} together with the fact
that a nameable annotation evaluates to its constant in every store. -/
theorem lits_true_of_instance_aux {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hN : authNameable (shapeOf P B) P)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B))
    {b : Bool} {i q : Nat} {m : Term} {d : NonceName}
    {tag : Tag} {peer v : Expr} {x : AuthInst}
    (hev : evAt tr i = Ev.act q m d)
    (hA : P.actionAt q (pcOf (cfgAt Cs i) q) = some (authAction b tag peer v))
    (hstep : x ∈ authOfStep P (cfgAt Cs i) (Ev.act q m d))
    (hxi : x.isCommit = b) (hi : i < tr.length) :
    ∃ o ∈ authOccs (shapeOf P B) P b,
      authTriple (shapeOf P B) o = some (x.tag, x.peer, x.val) ∧
        ∀ l ∈ authOccLits (shapeOf P B) P o,
          l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true := by
  obtain ⟨A, val, hpe, hv, hxt, hxp, hxv, hflag⟩ := authOfStep_authAction hA hstep
  have hq : q < P.sessions.length := by
    by_contra he
    have hr : P.roleAt q = none := by
      unfold roleAt
      rw [List.drop_eq_nil_of_le (by omega : P.sessions.length ≤ q)]
      rfl
    have hl : P.roleLen q = 0 := by
      unfold roleLen
      rw [hr]
    have hpcLt : pcOf (cfgAt Cs i) q < P.roleLen q :=
      lt_roleLen_of_actionAt (by rw [hA]; intro h; cases h)
    omega
  have hpcLt : pcOf (cfgAt Cs i) q < P.roleLen q :=
    lt_roleLen_of_actionAt (by rw [hA]; intro h; cases h)
  have hstepLt : i < (shapeOf P B).steps := by
    have hlen : tr.length ≤ B.steps := hbt.2.1
    rw [steps_eq]
    omega
  have hnS1 : q < (shapeOf P B).nS1 := by rw [nS1_eq]; exact hq
  have hshS : q < shS (shapeOf P B) := lt_shS hnS1
  have hshPc : pcOf (cfgAt Cs i) q < shPc (shapeOf P B) := by
    have hle := roleLen_le_nPc1 hnS1
    show pcOf (cfgAt Cs i) q < (shapeOf P B).nPc1 + 1
    omega
  have hexpr : peer ∈ allExprs P ∧ v ∈ allExprs P := by
    cases b
    · rw [authAction_false] at hA
      exact mem_allExprs_claim hA
    · rw [authAction_true] at hA
      exact mem_allExprs_commit hA
  set p : AuthPos := { isCommit := b, sess := q, pc := pcOf (cfgAt Cs i) q, tag := tag, peer := peer, val := v } with hp
  have hpos : p ∈ authPositions P := by
    unfold authPositions
    rw [List.mem_flatMap]
    refine ⟨q, List.mem_range.mpr hq, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨pcOf (cfgAt Cs i) q, List.mem_range.mpr hpcLt, ?_⟩
    rw [hA]
    cases b <;> exact List.Mem.head _
  obtain ⟨u, u', hidx⟩ : ∃ u u', authOccIdx (shapeOf P B) p = some (u, u') := by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hN p hpos)
    cases w with
    | mk u u' => exact ⟨u, u', hw⟩
  obtain ⟨A', d', hmsg, hu_eq, hp_eq⟩ : ∃ A' d',
      authOccMsgs (shapeOf P B) p = some (A', d') ∧
        uIdx (shapeOf P B) (some d') = u ∧
        uIdx (shapeOf P B) (some (Term.agent A')) = u' := by
    rw [authOccIdx_map] at hidx
    cases h : authOccMsgs (shapeOf P B) p with
    | none => rw [h] at hidx; simp at hidx
    | some z =>
        cases z with
        | mk a' d' =>
            rw [h] at hidx
            obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hidx)
            exact ⟨a', d', rfl, h1, h2⟩
  have hcv := AgreesBase.authOccMsgs_some hmsg
  have hcp := AgreesBase.constVal_closed hcv.1
  have hcv2 := AgreesBase.constVal_closed hcv.2.1
  have hA' : A' = A := by
    have h9 := eval_eq_constVal peer (storeOf (cfgAt Cs i) q) hcp.1 hcp.2.1 hcp.2.2
    rw [h9, hcv.1] at hpe
    exact Term.agent.inj (Option.some.inj hpe)
  have hd' : d' = val := by
    have h9 := eval_eq_constVal v (storeOf (cfgAt Cs i) q) hcv2.1 hcv2.2.1 hcv2.2.2
    rw [h9, hcv.2.1] at hv
    exact Option.some.inj hv
  rw [hd'] at hu_eq
  rw [hA'] at hp_eq
  set k : AuthOcc := { pos := p, step := i, data := u, peerVal := u' } with hk
  have hmem : k ∈ authOccs (shapeOf P B) P b := by
    unfold authOccs
    rw [List.bind_eq_flatMap, List.mem_flatMap]
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hpos, by simp [p]⟩
    · rw [hidx]
      rw [List.mem_map]
      exact ⟨i, List.mem_range.mpr hstepLt, rfl⟩
  refine ⟨k, hmem, ?_, ?_⟩
  · unfold authTriple
    rw [hmsg, hA', hd']
    show some (tag, A, val) = some (x.tag, x.peer, x.val)
    rw [← hxt, ← hxp, ← hxv]
  · intro l hl
    rw [hk, hp, authOccLits, List.mem_cons, List.mem_cons, List.mem_cons,
      List.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · show assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr) (evAct (shapeOf P B) i q) = true
      have hrd : rdEv (shapeOf P B) P (cfgAt Cs) (evAt tr) i = 1 + q :=
        (evActs (shapeOf P B) P (cfgAt Cs) (evAt tr) (i := i) hshS).mp ⟨m, d, hev⟩
      rw [assignOf_evAct (shapeOf P B) P (cfgAt Cs) (evAt tr) hstepLt hshS]
      exact decide_eq_true_eq.mpr hrd
    · show assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
        (vpc (shapeOf P B) i q (pcOf (cfgAt Cs i) q)) = true
      rw [assignOf_pc (shapeOf P B) P (cfgAt Cs) (evAt tr) (by omega : i ≤ (shapeOf P B).steps)
        hshS hshPc]
      exact decide_eq_true_eq.mpr rfl
    · show assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
          (vxe (shapeOf P B) i q (eIdx P v) u) = true
      have he : eIdx P v < shE (shapeOf P B) := heIdx v hexpr.2
      have huV : u < shVal (shapeOf P B) := by rw [← hu_eq]; exact uIdx_lt' _ _
      have hxe : rdXe (shapeOf P B) P (cfgAt Cs) (evAt tr) i q (eIdx P v) = u := by
        rw [rdXe_eIdx (shapeOf P B) P (cfgAt Cs) (evAt tr) hexpr.2]
        rw [hv]
        exact hu_eq
      have hx : assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
          (vxe (shapeOf P B) i q (eIdx P v) u) =
            decide (rdXe (shapeOf P B) P (cfgAt Cs) (evAt tr) i q (eIdx P v) = u) :=
        assignOf_xe (shapeOf P B) P (cfgAt Cs) (evAt tr) (by omega : i ≤ (shapeOf P B).steps)
          hshS he huV
      rw [hx]
      exact decide_eq_true_eq.mpr hxe
    · show assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
          (vxe (shapeOf P B) i q (eIdx P peer) u') = true
      have he : eIdx P peer < shE (shapeOf P B) := heIdx peer hexpr.1
      have hpV : u' < shVal (shapeOf P B) := by rw [← hp_eq]; exact uIdx_lt' _ _
      have hxe : rdXe (shapeOf P B) P (cfgAt Cs) (evAt tr) i q (eIdx P peer) = u' := by
        rw [rdXe_eIdx (shapeOf P B) P (cfgAt Cs) (evAt tr) hexpr.1]
        rw [hpe]
        exact hp_eq
      have hx : assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)
          (vxe (shapeOf P B) i q (eIdx P peer) u') =
            decide (rdXe (shapeOf P B) P (cfgAt Cs) (evAt tr) i q (eIdx P peer) = u') :=
        assignOf_xe (shapeOf P B) P (cfgAt Cs) (evAt tr) (by omega : i ≤ (shapeOf P B).steps)
          hshS he hpV
      rw [hx]
      exact decide_eq_true_eq.mpr hxe


/-- **The other direction.** If the run performs an authentication event at a nameable position,
the occurrence of that event at that step has all four literals true under the characteristic
assignment. -/
theorem lits_true_of_instance {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hok : WithinBounds P B (cfgAt Cs) (evAt tr))
    (hN : authNameable (shapeOf P B) P)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B))
    {commit : Bool} {i : Nat} {x : AuthInst}
    (hx : x ∈ authInsts P Cs tr) (hxi : x.isCommit = commit) (hi : i < tr.length)
    (hstep : x ∈ authOfStep P (cfgAt Cs i) (evAt tr i)) :
    ∃ o ∈ authOccs (shapeOf P B) P commit,
      authTriple (shapeOf P B) o = some (x.tag, x.peer, x.val) ∧
        ∀ l ∈ authOccLits (shapeOf P B) P o,
          l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true := by
  cases hev : evAt tr i with
  | act q m d =>
      rw [hev] at hstep
      cases hA : P.actionAt q (pcOf (cfgAt Cs i) q) with
      | none =>
          exfalso
          simp only [authOfStep, hA] at hstep
          exact absurd hstep (by simp)
      | some act =>
          cases act with
          | claim tag peer v =>
              have hA2 : P.actionAt q (pcOf (cfgAt Cs i) q) =
                  some (authAction false tag peer v) := by
                rw [authAction_false]
                exact hA
              have hb : commit = false := by
                rw [← hxi]
                exact authOfStep_isCommit_of_claim hA hstep
              subst hb
              exact lits_true_of_instance_aux (P := P) (B := B) (tr := tr) (Cs := Cs)
                hbt hN heIdx (b := false) hev hA2 hstep hxi hi
          | commit tag peer v =>
              have hA2 : P.actionAt q (pcOf (cfgAt Cs i) q) =
                  some (authAction true tag peer v) := by
                rw [authAction_true]
                exact hA
              have hb : commit = true := by
                rw [← hxi]
                exact AgreesBase.authOfStep_isCommit_of_commit hA hstep
              subst hb
              exact lits_true_of_instance_aux (P := P) (B := B) (tr := tr) (Cs := Cs)
                hbt hN heIdx (b := true) hev hA2 hstep hxi hi
          | fresh _ _ | send _ _ | recv _ _ | assign _ _ | check _ _ | secret _ =>
              exfalso
              simp only [authOfStep, hA] at hstep
              exact absurd hstep (by simp)
  | idle | ded _ =>
      exfalso
      simp only [authOfStep, hev] at hstep
      exact absurd hstep (by simp)

/-- Two occurrences that the triple-only excuse relation pairs record the same triple. -/
theorem triples_eq_of_claimExcuses {P : Protocol} {B : Bounds} {c k : AuthOcc}
    (hc : c ∈ authOccs (shapeOf P B) P true) (hk : k ∈ authOccs (shapeOf P B) P false)
    (hexc : claimExcuses Matching.tripleOnly (shapeOf P B) P c k = true) :
    authTriple (shapeOf P B) c = authTriple (shapeOf P B) k := by
  obtain ⟨ac, dc, hmc, hdc, hpc⟩ := authOccMsgs_of_mem hc
  obtain ⟨ak, dk, hmk, hdk, hpk⟩ := authOccMsgs_of_mem hk
  rw [claimExcuses] at hexc
  simp only [Bool.and_eq_true, beq_iff_eq] at hexc
  have hkc : k.pos.isCommit = false := by simpa using hexc.1.1.1
  have htag : k.pos.tag = c.pos.tag := hexc.1.1.2
  have hdata : k.data = c.data := hexc.1.2
  have hpeer : k.peerVal = c.peerVal := hexc.2
  have hdcU : dc ∈ (shapeOf P B).U := (AgreesBase.authOccMsgs_some hmc).2.2.2
  have hdkU : dk ∈ (shapeOf P B).U := (AgreesBase.authOccMsgs_some hmk).2.2.2
  have hacU : Term.agent ac ∈ (shapeOf P B).U := (AgreesBase.authOccMsgs_some hmc).2.2.1
  have hakU : Term.agent ak ∈ (shapeOf P B).U := (AgreesBase.authOccMsgs_some hmk).2.2.1
  have hd : dc = dk := by
    have h1 : uIdx (shapeOf P B) (some dk) = uIdx (shapeOf P B) (some dc) := by
      rw [← hdk, ← hdc]
      exact hdata
    have h2 := congrArg (valAt (shapeOf P B)) h1
    rw [valAt_uIdx_some _ hdkU, valAt_uIdx_some _ hdcU] at h2
    exact (Option.some.inj h2).symm
  have ha : ak = ac := by
    have h1 : uIdx (shapeOf P B) (some (Term.agent ak)) =
        uIdx (shapeOf P B) (some (Term.agent ac)) := by
      rw [← hpk, ← hpc]
      exact hpeer
    have h2 := congrArg (valAt (shapeOf P B)) h1
    rw [valAt_uIdx_some _ hakU, valAt_uIdx_some _ hacU] at h2
    exact Term.agent.inj (Option.some.inj h2)
  unfold authTriple
  rw [hmc, hmk, ha, hd, htag]

/-! ### The remaining group bounds -/

theorem below_lits_flatMap {N : Nat} {α : Type} {L : List α} {f : α -> List Lit}
    (h : ∀ x ∈ L, ∀ l ∈ f x, l.var < N) : ∀ l ∈ L.flatMap f, l.var < N := by
  intro l hl
  rw [List.mem_flatMap] at hl
  obtain ⟨x, hx, hl⟩ := hl
  exact h x hx l hl

theorem below_lits_map {N : Nat} {α : Type} {L : List α} {f : α -> Lit}
    (h : ∀ x ∈ L, (f x).var < N) : ∀ l ∈ L.map f, l.var < N := by
  intro l hl
  rw [List.mem_map] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  exact h x hx

theorem andNDef_below {aux : BVar} {ls : List Lit} {N : Nat}
    (haux : aux < N) (hls : ∀ l ∈ ls, l.var < N) : below N (andNDef aux ls).clauses := by
  intro cl hcl
  rw [andNDef, andNDefClauses, List.mem_append, List.mem_map, List.mem_singleton] at hcl
  rcases hcl with h | h
  · obtain ⟨w, hw, rfl⟩ := h
    intro l' hl'
    rw [List.mem_cons, List.mem_singleton] at hl'
    rcases hl' with rfl | rfl
    · exact haux
    · exact hls _ hw
  · subst h
    intro l' hl'
    rw [List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · exact haux
    · rw [List.mem_map] at hl'
      obtain ⟨w, hw, rfl⟩ := hl'
      show w.var < N
      exact hls w hw

theorem below_actGuard {i q c : Nat} (hi : i < sh.steps) (hq : q < shS sh) (hc : c < shPc sh) :
    ∀ l ∈ actGuard sh i q c, l.var < nVarsAll sh := by
  intro l hl
  rw [actGuard, List.mem_cons, List.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact evAct_lt_nVars hi hq
  · exact vpc_lt_nVars (by omega : i ≤ sh.steps) hq hc

theorem below_leakAux {P : Protocol} :
    below (nVarsAll sh) (leakAuxClauses sh P).clauses := by
  simp only [leakAuxClauses, cnfOf, eachStep1, eachSess, eachVar]
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  refine below_flatMap_range (fun x hx => ?_)
  show below (nVarsAll sh) (leakAuxEntry sh P i q x)
  by_cases hsec : storeSecret sh P q x
  · simp only [leakAuxEntry, if_pos hsec]
    refine below_flatMap_range (fun u hu => ?_)
    have hu' : u < shVal sh := hu_of_len (sh := sh) hu
    refine andNDef_below (vau_lt_nVars (by omega : i ≤ sh.steps) hq hx hu') ?_
    intro l hl
    rw [List.mem_cons, List.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact vst_lt_nVars (by omega : i ≤ sh.steps) hq hx hu'
    · exact vkn_lt_nVars (by omega : i ≤ sh.steps) hu'
  · simp only [leakAuxEntry, if_neg hsec]
    exact below_nil _

theorem below_pubAux {P : Protocol}
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE sh) :
    below (nVarsAll sh) (pubAuxClauses sh P).clauses := by
  simp only [pubAuxClauses, cnfOf, eachStep, eachSess, eachPc]
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  refine below_flatMap_range (fun c hc => ?_)
  refine below_flatMap_range (fun u hu => ?_)
  show below (nVarsAll sh) (pubAuxEntry sh P i q c u)
  cases hA : P.actionAt q c with
  | none =>
      have hred : pubAuxEntry sh P i q c u = [] := by
        rw [pubAuxEntry, hA]
      rw [hred]
      exact below_nil _
  | some act =>
      cases act with
      | send a e =>
          simp only [pubAuxEntry, hA]
          refine andNDef_below (vpb_lt_nVars hi hq hc (hu_of_len (sh := sh) hu)) ?_
          intro l hl
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl
          · exact evAct_lt_nVars hi hq
          · exact vpc_lt_nVars (by omega : i ≤ sh.steps) hq hc
          · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq
              (heIdx e (mem_allExprs_send hA)) (hu_of_len (sh := sh) hu)
      | fresh _ _ | recv _ _ | assign _ _ | check _ _ | secret _ | claim _ _ _ | commit _ _ _ =>
          have hred : pubAuxEntry sh P i q c u = [] := by
            rw [pubAuxEntry, hA]
          rw [hred]
          exact below_nil _

theorem below_fresh {P : Protocol} :
    below (nVarsAll sh) (freshClauses sh P).clauses := by
  simp only [freshClauses, cnfOf, eachStep, eachSess, eachPc]
  refine below_flatMap_range (fun i hi => ?_)
  refine below_flatMap_range (fun q hq => ?_)
  refine below_flatMap_range (fun c hc => ?_)
  show below (nVarsAll sh) (freshClausesAt sh P i q c)
  cases hA : P.actionAt q c with
  | none =>
      have hred : freshClausesAt sh P i q c = [] := by
        rw [freshClausesAt, hA]
      rw [hred]
      exact below_nil _
  | some act =>
      cases act with
      | fresh x _ =>
          simp only [freshClausesAt, hA]
          refine below_flatMap_range (fun d hd => ?_)
          cases hD : rget sh.D d with
          | none =>
              have hred : freshUseClauses sh i q c d = [] := by
                rw [freshUseClauses, hD]
              rw [hred]
              exact below_nil _
          | some N =>
              simp only [freshUseClauses, hD]
              refine below_append ?_ ?_
              · refine below_flatMap_range (fun r hr => below_map_range (fun y hy => ?_))
                intro l hl
                simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at hl
                rcases hl with hl | rfl | rfl
                · exact below_actGuard hi hq hc l hl
                · exact vfr_lt_nVars hi hq hd
                · exact vst_lt_nVars (by omega : i ≤ sh.steps) hr hy (uIdx_lt' _ _)
              · intro cl' hcl'
                rw [List.mem_singleton] at hcl'
                subst hcl'
                intro l hl
                simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at hl
                rcases hl with hl | rfl | rfl
                · exact below_actGuard hi hq hc l hl
                · exact vfr_lt_nVars hi hq hd
                · exact vkn_lt_nVars (by omega : i ≤ sh.steps) (uIdx_lt' _ _)
      | send _ _ | recv _ _ | assign _ _ | check _ _ | secret _ | claim _ _ _ | commit _ _ _ =>
          have hred : freshClausesAt sh P i q c = [] := by
            rw [freshClausesAt, hA]
          rw [hred]
          exact below_nil _

theorem dedInstsOf_concl {u : Nat} {ins : DedInst} (h : ins ∈ dedInstsOf sh u) :
    ins.concl = u := by
  unfold dedInstsOf at h
  cases hU : rget sh.U u with
  | none => simp [hU] at h
  | some t =>
      rw [hU] at h
      simp only [List.mem_cons, List.mem_append, List.mem_filterMap] at h
      rcases h with h | ⟨a, ha, h⟩
      · rcases h with h | h
        · subst h
          rfl
        · cases t with
          | agent A => simp at h; subst h; rfl
          | nonce N => simp at h
          | key k =>
              cases k with
              | pub A => simp at h; subst h; rfl
              | priv A => simp at h
              | shrk _ _ => simp at h
          | pair x y =>
              rcases h5 : tIx sh x with ⟨b₁⟩ | ⟨b₁⟩
              · simp [h5] at h
              · rcases h6 : tIx sh y with ⟨b₂⟩ | ⟨b₂⟩
                · simp [h6] at h
                · simp [h5, h6] at h; subst h; rfl
          | encS m k =>
              rcases h5 : tIx sh m with ⟨b₁⟩ | ⟨b₁⟩
              · simp [h5] at h
              · rcases h6 : tIx sh (Term.key k) with ⟨b₂⟩ | ⟨b₂⟩
                · simp [h6] at h
                · simp [h5, h6] at h; subst h; rfl
          | encA m ag =>
              rcases h5 : tIx sh m with ⟨b₁⟩ | ⟨b₁⟩
              · simp [h5] at h
              · simp [h5] at h; subst h; rfl
          | hash m =>
              rcases h5 : tIx sh m with ⟨b₁⟩ | ⟨b₁⟩
              · simp [h5] at h
              · simp [h5] at h; subst h; rfl
      · cases a with
        | pair x y =>
            by_cases h1 : x = t
            · simp [h1] at h
              subst h
              rfl
            · by_cases h2 : y = t
              · simp [h1, h2] at h
                subst h
                rfl
              · simp [h1, h2] at h
        | encS m k =>
            by_cases h1 : m = t
            · simp [h1] at h
              rcases h5 : tIx sh (Term.key k) with ⟨b₂⟩ | ⟨b₂⟩
              · rw [h5] at h
                simp at h
              · rw [h5] at h
                simp at h
                subst h
                rfl
            · simp [h1] at h
        | encA m ag =>
            by_cases h1 : m = t
            · simp [h1] at h
              rcases h5 : tIx sh (Term.key (Key.priv ag)) with ⟨b₂⟩ | ⟨b₂⟩
              · rw [h5] at h
                simp at h
              · rw [h5] at h
                simp at h
                subst h
                rfl
            · simp [h1] at h
        | agent A | nonce N | key k | hash m => simp at h

theorem below_init {P : Protocol} : below (nVarsAll sh) (initClauses sh P).clauses := by
  simp only [initClauses, initPcClauses, initStClauses, initKnClauses, eachSess, eachVar, cnfOf]
  refine below_append (below_append ?_ ?_) ?_
  · refine below_flatMap_range (fun q hq => below_map_range (fun c hc => ?_))
    intro l hl
    by_cases hh : c = 0
    · simp only [if_pos hh] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact vpc_lt_nVars (by omega : (0 : Nat) ≤ sh.steps) hq hc
    · simp only [if_neg hh] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact vpc_lt_nVars (by omega : (0 : Nat) ≤ sh.steps) hq hc
  · refine below_flatMap_range (fun q hq => below_flatMap_range (fun x hx =>
        below_map_range (fun u hu => ?_)))
    intro l hl
    by_cases hh : u = sh.U.length
    · simp only [if_pos hh] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact vst_lt_nVars (by omega : (0 : Nat) ≤ sh.steps) hq hx hu
    · simp only [if_neg hh] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact vst_lt_nVars (by omega : (0 : Nat) ≤ sh.steps) hq hx hu
  · refine below_map_range (fun u hu => ?_)
    intro l hl
    by_cases hh : initKnHolds sh P u
    · simp only [if_pos hh] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact vkn_lt_nVars (by omega : (0 : Nat) ≤ sh.steps) (hu_of_len (sh := sh) hu)
    · simp only [if_neg hh] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact vkn_lt_nVars (by omega : (0 : Nat) ≤ sh.steps) (hu_of_len (sh := sh) hu)

theorem below_frame : below (nVarsAll sh) (frameClauses sh).clauses := by
  simp only [frameClauses, frameKnClauses, frameSessClauses, eachStep, eachSess, eachVar, mapMsg,
    mapVal, cnfOf]
  refine below_flatMap_range (fun i hi => below_append ?_
    (below_flatMap_range (fun q hq => below_append ?_ ?_)))
  · refine below_map_range (fun u hu => ?_)
    intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact vkn_lt_nVars (by omega : i ≤ sh.steps) (hu_of_len (sh := sh) hu)
    · exact vkn_lt_nVars (by omega : i + 1 ≤ sh.steps) (hu_of_len (sh := sh) hu)
  · refine below_map_range (fun c hc => ?_)
    intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact evAct_lt_nVars hi hq
    · exact vpc_lt_nVars (by omega : i ≤ sh.steps) hq hc
    · exact vpc_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hc
  · refine below_flatMap_range (fun x hx => below_map_range (fun u hu => ?_))
    intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact evAct_lt_nVars hi hq
    · exact vst_lt_nVars (by omega : i ≤ sh.steps) hq hx hu
    · exact vst_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hx hu

theorem dedInst_bounds {ins : DedInst} (h : instAt sh n = some ins) :
    ins.concl < shVal sh ∧ ∀ p ∈ ins.prem, p < shVal sh := by
  obtain ⟨u, hu, hin⟩ := mem_dedInsts h
  refine ⟨by rw [dedInstsOf_concl hin]; exact hu_of_len (sh := sh) hu, ?_⟩
  intro p hp
  exact hu_of_len (sh := sh) (dedInstsOf_prem_lt hu hin p hp)

theorem below_knSupport {P : Protocol} :
    below (nVarsAll sh) (knSupportClauses sh P).clauses := by
  simp only [knSupportClauses, cnfOf, eachStep, mapMsg]
  refine below_flatMap_range (fun i hi => below_map_range (fun u hu => ?_))
  have hu' : u < shVal sh := hu_of_len (sh := sh) hu
  intro l hl
  rw [List.mem_append] at hl
  rcases hl with hl | hl
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact vkn_lt_nVars (by omega : i + 1 ≤ sh.steps) hu'
    · exact vkn_lt_nVars (by omega : i ≤ sh.steps) hu'
  · simp only [publisherLits, litsSess, litsPc, litsInst] at hl
    rw [List.mem_append] at hl
    rcases hl with hl | hl
    · rw [List.mem_flatMap] at hl
      obtain ⟨q, hq, hl⟩ := hl
      rw [List.mem_flatMap] at hl
      obtain ⟨c, hc, hl⟩ := hl
      cases hA : P.actionAt q c with
      | none =>
          have hred : sendPubLit sh P i q c u = [] := by
            rw [sendPubLit, hA]
          rw [hred] at hl
          exact absurd hl (by simp)
      | some act =>
          cases act with
          | send a e =>
              simp only [sendPubLit, hA] at hl
              rw [List.mem_singleton] at hl
              subst hl
              exact vpb_lt_nVars hi (List.mem_range.mp hq) (List.mem_range.mp hc) hu'
          | fresh _ _ | recv _ _ | assign _ _ | check _ _ | secret _ | claim _ _ _ | commit _ _ _ =>
              have hred : sendPubLit sh P i q c u = [] := by
                rw [sendPubLit, hA]
              rw [hred] at hl
              exact absurd hl (by simp)
    · rw [List.mem_flatMap] at hl
      obtain ⟨n, hn, hl⟩ := hl
      cases hinst : instAt sh n with
      | none =>
          have hred : instPublisher sh i n u = [] := by
            rw [instPublisher, hinst]
          rw [hred] at hl
          exact absurd hl (by simp)
      | some inst =>
          by_cases hcu : inst.concl = u
          · simp only [instPublisher, hinst, if_pos hcu] at hl
            rw [List.mem_singleton] at hl
            subst hl
            have hlt : u < shVal sh := by
              rw [← hcu]
              exact (dedInst_bounds hinst).1
            exact evDed_lt_nVars hi (by
              have : nInst sh = (dedInsts sh).length := rfl
              have := List.mem_range.mp hn
              omega)
          · simp only [instPublisher, hinst, if_neg hcu] at hl
            exact absurd hl (by simp)

theorem below_ded : below (nVarsAll sh) (dedClauses sh).clauses := by
  simp only [dedClauses, cnfOf, eachStep, eachInst]
  refine below_flatMap_range (fun i hi => below_flatMap_range (fun n hn => ?_))
  show below (nVarsAll sh) (dedClausesAt sh i n)
  cases hinst : instAt sh n with
  | none =>
      have hred : dedClausesAt sh i n = [] := by
        rw [dedClausesAt, hinst]
      rw [hred]
      exact below_nil _
  | some ins =>
      have hmem := mem_dedInsts hinst
      obtain ⟨u, hu, hin⟩ := hmem
      have hc : ins.concl = u := dedInstsOf_concl hin
      have hnn : n < nInst sh := hn
      have hev : evDed sh i n < nVarsAll sh := evDed_lt_nVars hi hnn
      simp only [dedClausesAt, hinst]
      refine below_append ?_ ?_
      · refine below_map_list (fun p hp => ?_)
        intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · show evDed sh i n < nVarsAll sh
          exact hev
        · show vkn sh i p < nVarsAll sh
          exact vkn_lt_nVars (by omega : i ≤ sh.steps)
            (hu_of_len (sh := sh) (dedInstsOf_prem_lt hu hin p hp))
      · intro cl' hcl'
        rw [List.mem_singleton] at hcl'
        subst hcl'
        intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · show evDed sh i n < nVarsAll sh
          exact hev
        · show vkn sh (i + 1) ins.concl < nVarsAll sh
          rw [hc]
          exact vkn_lt_nVars (by omega : i + 1 ≤ sh.steps) (hu_of_len (sh := sh) hu)

theorem below_flatMap {N : Nat} {α : Type} {L : List α} {f : α -> List (List Lit)}
    (h : ∀ x ∈ L, below N (f x)) : below N (L.flatMap f) := by
  intro cl hcl
  rw [List.mem_flatMap] at hcl
  obtain ⟨x, hx, hcl⟩ := hcl
  exact h x hx cl hcl

theorem ohOf_vals {f : Nat -> Nat} {K : Nat} {hK : 0 < K}
    {inj : ∀ x y, x < K -> y < K -> f x = f y -> x = y} {aux : Nat -> Nat} :
    (ohOf f K hK inj aux).vals = List.range K := rfl

theorem ohOf_varOf {f : Nat -> Nat} {K : Nat} {hK : 0 < K}
    {inj : ∀ x y, x < K -> y < K -> f x = f y -> x = y} {aux : Nat -> Nat} :
    (ohOf f K hK inj aux).varOf = f := rfl

theorem fwdClausesOn_below {α : Type} {o : Oh α} {ant : List Lit} {g : α -> Lit} {N : Nat}
    (hant : ∀ l ∈ ant, l.var < N) (hv : ∀ x ∈ o.vals, o.varOf x < N)
    (hg : ∀ x ∈ o.vals, (g x).var < N) : below N (fwdClausesOn ant o g).clauses := by
  intro cl hcl
  unfold fwdClausesOn cnfOf at hcl
  rw [List.mem_map] at hcl
  obtain ⟨x, hx, rfl⟩ := hcl
  intro l hl
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  rcases hl with hl | rfl | rfl
  · exact hant l hl
  · exact hv x hx
  · exact hg x hx

theorem fwd2ClausesOn_below {α β : Type} {o₁ : Oh α} {o₂ : Oh β} {ant : List Lit}
    {g : α -> β -> Lit} {N : Nat}
    (hant : ∀ l ∈ ant, l.var < N) (hv₁ : ∀ x ∈ o₁.vals, o₁.varOf x < N)
    (hv₂ : ∀ y ∈ o₂.vals, o₂.varOf y < N)
    (hg : ∀ x ∈ o₁.vals, ∀ y ∈ o₂.vals, (g x y).var < N) :
    below N (fwd2ClausesOn ant o₁ o₂ g).clauses := by
  intro cl hcl
  unfold fwd2ClausesOn cnfOf at hcl
  rw [List.mem_flatMap] at hcl
  obtain ⟨x, hx, hcl⟩ := hcl
  rw [List.mem_map] at hcl
  obtain ⟨y, hy, rfl⟩ := hcl
  intro l hl
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  rcases hl with hl | rfl | rfl | rfl
  · exact hant l hl
  · exact hv₁ x hx
  · exact hv₂ y hy
  · exact hg x hx y hy

theorem below_eval {P : Protocol}
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE sh)
    (hvars : ∀ E ∈ allExprs P, ∀ x ∈ Expr.vars E, x < shV sh) :
    below (nVarsAll sh) (evalClauses sh P).clauses := by
  simp only [evalClauses, cnfOf, eachStep1, eachSess]
  refine below_flatMap_range (fun i hi => below_flatMap_range (fun q hq => ?_))
  have hi' : i ≤ sh.steps := by omega
  have hq' : q < shS sh := hq
  show below (nVarsAll sh) (evalClausesAt sh P i q)
  unfold evalClausesAt
  refine below_flatMap (fun E hE => ?_)
  have heE : eIdx P E < shE sh := heIdx E hE
  cases h1 : Expr.child1 E with
  | some c =>
      have hc : c ∈ allExprs P := mem_allExprs_child1 hE h1
      rw [evalGate, h1]
      refine fwdClausesOn_below (by simp) ?_ ?_
      · intro x hx
        dsimp only [xeOh, ohOf] at hx ⊢
        exact vxe_lt_nVars hi' hq' (heIdx c hc) (List.mem_range.mp hx)
      · intro x hx
        dsimp only [xeOh, ohOf] at hx
        show (pos (vxe sh i q (eIdx P E) (f1 sh E x))).var < nVarsAll sh
        exact vxe_lt_nVars hi' hq' heE (uIdx_lt' _ _)
  | none =>
      cases h2 : Expr.child2 E with
      | some cb =>
          have hcb : Expr.child2 E = some (cb.1, cb.2) := by
            rw [h2]
          have hca : cb.1 ∈ allExprs P := (mem_allExprs_child2 hE hcb).1
          have hcb' : cb.2 ∈ allExprs P := (mem_allExprs_child2 hE hcb).2
          rw [evalGate, h1, h2]
          refine fwd2ClausesOn_below (by simp) ?_ ?_ ?_
          · intro x hx
            dsimp only [xeOh, ohOf] at hx ⊢
            exact vxe_lt_nVars hi' hq' (heIdx cb.1 hca) (List.mem_range.mp hx)
          · intro y hy
            dsimp only [xeOh, ohOf] at hy ⊢
            exact vxe_lt_nVars hi' hq' (heIdx cb.2 hcb') (List.mem_range.mp hy)
          · intro x hx y hy
            dsimp only [xeOh, ohOf] at hx hy
            show (pos (vxe sh i q (eIdx P E) (f2 sh E x y))).var < nVarsAll sh
            exact vxe_lt_nVars hi' hq' heE (uIdx_lt' _ _)
      | none =>
          have hred : evalGate sh P i q E = evalLeafGate sh P i q (eIdx P E) E := by
            rw [evalGate, h1, h2]
          rw [hred]
          cases E with
          | var x =>
              have hxv : x ∈ Expr.vars (Expr.var x) := by simp [Expr.vars]
              have hx' : x < shV sh := hvars (Expr.var x) hE x hxv
              simp only [evalLeafGate]
              refine fwdClausesOn_below (by simp) ?_ ?_
              · intro y hy
                dsimp only [stOh, ohOf] at hy ⊢
                exact vst_lt_nVars hi' hq' hx' (List.mem_range.mp hy)
              · intro y hy
                dsimp only [stOh, ohOf] at hy
                show (pos (vxe sh i q (eIdx P (Expr.var x)) y)).var < nVarsAll sh
                exact vxe_lt_nVars hi' hq' heE (List.mem_range.mp hy)
          | agent _ | nonce _ | shrk _ _ | pubk _ | privk _ | pair _ _ | encS _ _ | encA _ _ | hash _ | decS _ _ | decA _ _ | fst _ | snd _ =>
              simp only [evalLeafGate]
              intro cl hcl l hl
              rw [List.mem_singleton] at hcl
              subst hcl
              simp only [List.mem_singleton] at hl
              subst hl
              exact vxe_lt_nVars hi' hq' heE (uIdx_lt' _ _)

theorem below_step {P : Protocol}
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE sh)
    (hwritten : ∀ q c act, P.actionAt q c = some act -> ∀ x ∈ act.written, x < shV sh)
    (hpcAct : ∀ q c, P.actionAt q c ≠ none -> c + 1 < shPc sh) :
    below (nVarsAll sh) (stepClauses sh P).clauses := by
  simp only [stepClauses, cnfOf, eachStep, eachSess, eachPc]
  refine below_flatMap_range (fun i hi => below_flatMap_range (fun q hq =>
    below_flatMap_range (fun c hc => ?_)))
  show below (nVarsAll sh) (stepClausesAt sh P i q c)
  cases hA : P.actionAt q c with
  | none =>
      have hred : stepClausesAt sh P i q c = [actGuard sh i q c] := by
        rw [stepClausesAt, hA]
      rw [hred]
      intro cl hcl l hl
      rw [List.mem_singleton] at hcl
      subst hcl
      exact below_actGuard hi hq hc l hl
  | some act =>
      have hpc : c + 1 < shPc sh := hpcAct q c (by
        rw [hA]
        simp)
      rw [stepClausesAt, hA]
      refine below_append (below_append ?_ ?_) ?_
      · intro cl hcl l hl
        rw [List.mem_singleton] at hcl
        subst hcl
        simp only [advClause, List.mem_append, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at hl
        rcases hl with hl | rfl
        · exact below_actGuard hi hq hc l hl
        · exact vpc_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hpc
      · refine below_flatMap_range (fun y hy => ?_)
        by_cases hwy : writtenVar act = some y
        · have hred : (if writtenVar act = some y then [] else keepVarClauses sh i q c y) = [] :=
            if_pos hwy
          rw [hred]
          exact below_nil _
        · have hred : (if writtenVar act = some y then [] else keepVarClauses sh i q c y) =
              keepVarClauses sh i q c y := if_neg hwy
          rw [hred]
          unfold keepVarClauses mapVal
          refine below_map_range (fun u hu => ?_)
          intro l hl
          simp only [keepClause, List.mem_append, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hl
          rcases hl with hl | rfl | rfl
          · exact below_actGuard hi hq hc l hl
          · exact vst_lt_nVars (by omega : i ≤ sh.steps) hq hy hu
          · exact vst_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hy hu
      · unfold actionClauses
        cases act with
        | fresh x N =>
            have hx : x < shV sh := hwritten q c (Action.fresh x N) hA x (by simp [Action.written])
            refine below_append ?_ ?_
            · refine below_flatMap_range (fun d hd => ?_)
              cases hD : rget sh.D d with
              | none =>
                  simp only [freshStepClauses, hD]
                  intro cl hcl l hl
                  rw [List.mem_singleton] at hcl
                  subst hcl
                  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                    or_false] at hl
                  rcases hl with hl | rfl
                  · exact below_actGuard hi hq hc l hl
                  · exact vfr_lt_nVars hi hq hd
              | some N' =>
                  simp only [freshStepClauses, hD]
                  intro cl hcl l hl
                  rw [List.mem_singleton] at hcl
                  subst hcl
                  simp only [List.mem_append, List.mem_cons, List.mem_cons, List.mem_singleton,
                    List.not_mem_nil, or_false] at hl
                  rcases hl with hl | rfl | rfl
                  · exact below_actGuard hi hq hc l hl
                  · exact vfr_lt_nVars hi hq hd
                  · exact vst_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hx (uIdx_lt' _ _)
            · intro cl hcl l hl
              rw [List.mem_singleton] at hcl
              subst hcl
              simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hl
              rcases hl with hl | rfl
              · exact below_actGuard hi hq hc l hl
              · exact vfr_lt_nVars hi hq (Nat.sub_lt (shD_pos sh) (by omega))
        | send a e =>
            have he : eIdx P e < shE sh := heIdx e (mem_allExprs_send hA)
            refine below_append ?_ ?_
            · intro cl hcl l hl
              rw [List.mem_singleton] at hcl
              subst hcl
              simp only [sendRealClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hl
              rcases hl with hl | rfl
              · exact below_actGuard hi hq hc l hl
              · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq he
                  (len_lt_shVal sh)
            · unfold mapMsg
              refine below_map_range (fun u hu => ?_)
              intro l hl
              simp only [sendPublishClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hl
              rcases hl with hl | rfl | rfl
              · exact below_actGuard hi hq hc l hl
              · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq he (hu_of_len (sh := sh) hu)
              · exact vkn_lt_nVars (by omega : i + 1 ≤ sh.steps)
                  (hu_of_len (sh := sh) hu)
        | recv a x =>
            have hx : x < shV sh := hwritten q c (Action.recv a x) hA x (by simp [Action.written])
            unfold eachVal
            refine below_flatMap_range (fun u hu => ?_)
            by_cases hut : u < sh.U.length
            · simp only [if_pos hut]
              intro cl hcl
              rw [List.mem_cons, List.mem_singleton] at hcl
              rcases hcl with rfl | rfl
              · intro l hl
                simp only [recvStoreClause, List.mem_append, List.mem_cons, List.mem_singleton,
                  List.not_mem_nil, or_false] at hl
                rcases hl with hl | rfl | rfl
                · exact below_actGuard hi hq hc l hl
                · exact vdl_lt_nVars hi hq hu
                · exact vst_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hx hu
              · intro l hl
                simp only [recvKnowClause, List.mem_append, List.mem_cons, List.mem_singleton,
                  List.not_mem_nil, or_false] at hl
                rcases hl with hl | rfl | rfl
                · exact below_actGuard hi hq hc l hl
                · exact vdl_lt_nVars hi hq hu
                · exact vkn_lt_nVars (by omega : i ≤ sh.steps) hu
            · simp only [if_neg hut]
              intro cl hcl l hl
              rw [List.mem_singleton] at hcl
              subst hcl
              simp only [recvRealClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hl
              rcases hl with hl | rfl
              · exact below_actGuard hi hq hc l hl
              · exact vdl_lt_nVars hi hq hu
        | assign x e =>
            have he : eIdx P e < shE sh := heIdx e (mem_allExprs_assign hA)
            have hx : x < shV sh := hwritten q c (Action.assign x e) hA x (by simp [Action.written])
            unfold eachVal
            refine below_flatMap_range (fun u hu => ?_)
            by_cases hut : u < sh.U.length
            · simp only [if_pos hut]
              intro cl hcl l hl
              rw [List.mem_singleton] at hcl
              subst hcl
              simp only [assignClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hl
              rcases hl with hl | rfl | rfl
              · exact below_actGuard hi hq hc l hl
              · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq he hu
              · exact vst_lt_nVars (by omega : i + 1 ≤ sh.steps) hq hx hu
            · simp only [if_neg hut]
              intro cl hcl l hl
              rw [List.mem_singleton] at hcl
              subst hcl
              simp only [assignRealClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hl
              rcases hl with hl | rfl
              · exact below_actGuard hi hq hc l hl
              · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq he hu
        | check e₁ e₂ =>
            have h12 : eIdx P e₁ < shE sh ∧ eIdx P e₂ < shE sh := by
              obtain ⟨h1, h2⟩ := mem_allExprs_check hA
              exact ⟨heIdx e₁ h1, heIdx e₂ h2⟩
            refine below_append ?_ ?_
            · intro cl hcl
              rw [List.mem_cons, List.mem_singleton] at hcl
              rcases hcl with rfl | rfl
              · intro l' hl'
                simp only [checkRealClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at hl'
                rcases hl' with hl' | rfl
                · exact below_actGuard hi hq hc l' hl'
                · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq h12.1
                    (len_lt_shVal sh)
              · intro l' hl'
                simp only [checkRealClause, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at hl'
                rcases hl' with hl' | rfl
                · exact below_actGuard hi hq hc l' hl'
                · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq h12.2
                    (len_lt_shVal sh)
            · unfold eachVal
              refine below_flatMap_range (fun u hu => below_filterMap ?_)
              intro v hv cl hfv
              by_cases hue : u = v
              · have hred : (if u == v then none
                    else some (checkEqClause sh i q c (eIdx P e₁) (eIdx P e₂) u v)) = none := by
                  simp [hue]
                rw [hred] at hfv
                exact absurd hfv (by simp)
              · have hred : (if u == v then none
                    else some (checkEqClause sh i q c (eIdx P e₁) (eIdx P e₂) u v)) =
                    some (checkEqClause sh i q c (eIdx P e₁) (eIdx P e₂) u v) := by
                  simp [hue]
                rw [hred] at hfv
                have hcl2 := Option.some.inj hfv
                subst hcl2
                intro cl' hcl' l hl
                rw [List.mem_singleton] at hcl'
                subst hcl'
                simp only [checkEqClause, List.mem_append, List.mem_cons, List.mem_singleton,
                  List.not_mem_nil, or_false] at hl
                rcases hl with hl | rfl | rfl
                · exact below_actGuard hi hq hc l hl
                · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq h12.1 hu
                · exact vxe_lt_nVars (by omega : i ≤ sh.steps) hq h12.2 hv
        | secret e =>
            show below (nVarsAll sh) []
            exact below_nil _
        | claim t peer v =>
            show below (nVarsAll sh) []
            exact below_nil _
        | commit t peer v =>
            show below (nVarsAll sh) []
            exact below_nil _


/-! ### The agreement group under the extended witness -/

theorem sat_baseEncode_of_groups {P : Protocol} {B : Bounds} {a : Assignment}
    (h1 : Sat a (oneHotClauses (shapeOf P B) P))
    (h2 : Sat a (initClauses (shapeOf P B) P))
    (h3 : Sat a (frameClauses (shapeOf P B)))
    (h4 : Sat a (evalClauses (shapeOf P B) P))
    (h5 : Sat a (stepClauses (shapeOf P B) P))
    (h6 : Sat a (dedClauses (shapeOf P B)))
    (h7 : Sat a (pubAuxClauses (shapeOf P B) P))
    (h8 : Sat a (knSupportClauses (shapeOf P B) P))
    (h9 : Sat a (freshClauses (shapeOf P B) P))
    (h10 : Sat a (leakAuxClauses (shapeOf P B) P)) :
    Sat a (AuthClauses.baseEncode P B) := by
  intro cl hcl
  obtain ⟨g, hg, hc⟩ := List.mem_flatMap.mp hcl
  rw [AuthClauses.baseGroups] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 cl hc
  · exact h2 cl hc
  · exact h3 cl hc
  · exact h4 cl hc
  · exact h5 cl hc
  · exact h6 cl hc
  · exact h7 cl hc
  · exact h8 cl hc
  · exact h9 cl hc
  · exact h10 cl hc

/-- **The agreement violation group is satisfied by the extended witness**, provided the run commits
a triple that was never claimed *and no committed triple of the run was claimed*. -/
theorem sat_authViolation_of_all_unclaimed {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hok : WithinBounds P B (cfgAt Cs) (evAt tr))
    (hN : authNameable (shapeOf P B) P)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B))
    (hall : ∀ t ∈ commitsOf P Cs tr, t ∉ claimsOf P Cs tr)
    (hbrk : AuthBreak P Cs tr) :
    Sat (assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr))
      (authViolationClauses Matching.tripleOnly (shapeOf P B) P) := by
  intro cl hcl
  rw [authViolationClauses, cnfOf] at hcl
  rw [List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · rw [List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · -- the demand clause
      rw [List.mem_singleton] at hcl
      subst hcl
      obtain ⟨c, hc, hnc⟩ := hbrk
      simp only [commitsOf, List.mem_filterMap] at hc
      obtain ⟨x, hx, hfx⟩ := hc
      have hxc : x.isCommit = true := by
        cases h : x.isCommit
        · rw [h] at hfx
          exact absurd hfx (by simp)
        · rfl
      have htrip : (x.tag, x.peer, x.val) = c := by
        have h2 := hfx
        rw [hxc] at h2
        exact Option.some.inj h2
      obtain ⟨i, C, e, hi, hzip, hstep⟩ := AgreesBase.mem_authInsts_elim hx
      rw [AgreesBase.rget_zip] at hzip
      obtain ⟨hCi, hei⟩ := hzip
      have hCe : C = cfgAt Cs i := (cfgAt_eq_of_rget Cs i C hCi).symm
      have hee : e = evAt tr i := (evAt_eq_of_rget tr i e hei).symm
      subst hCe
      subst hee
      have hlenCs : Cs.length = tr.length + 1 := runs_length hbt.1
      have hi' : i < tr.length := by
        have h2 : (Cs.zip tr).length ≤ tr.length := by
          rw [List.length_zip]
          omega
        omega
      obtain ⟨o, ho, hot, hall'⟩ :=
        lits_true_of_instance (P := P) (B := B) (tr := tr) (Cs := Cs) hbt hok hN heIdx
          (commit := true) (i := i) (x := x) hx hxc hi' hstep
      have hau : assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr) (authOccVar (shapeOf P B) P o) =
          true := (assignOfAg_aux_iff ho).mpr hall'
      refine clause_eval_holds (pos (authOccVar (shapeOf P B) P o)) ?_ hau
      · rw [authViolationLits]
        exact List.mem_map.mpr ⟨o, ho, rfl⟩
    · -- the excuse clauses
      rw [authExcuseClauses, List.mem_flatMap] at hcl
      obtain ⟨c0, hc0, hcl⟩ := hcl
      rw [List.mem_filterMap] at hcl
      obtain ⟨k, hk, hsome⟩ := hcl
      by_cases hex : claimExcuses Matching.tripleOnly (shapeOf P B) P c0 k
      · rw [if_pos hex] at hsome
        have hcl2 := Option.some.inj hsome
        subst hcl2
        by_cases haux : assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr)
            (authOccVar (shapeOf P B) P c0) = false
        · refine clause_eval_holds (neg (authOccVar (shapeOf P B) P c0))
            (List.mem_append_left _ (List.Mem.head _)) ?_
          simpa [neg_eval] using haux
        · have htrue : assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr)
              (authOccVar (shapeOf P B) P c0) = true := by
            cases h : assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr)
                (authOccVar (shapeOf P B) P c0) <;> simp_all
          have hallc0 : ∀ l ∈ authOccLits (shapeOf P B) P c0,
              l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true :=
            ((assignOfAg_aux_iff hc0).mp htrue)
          obtain ⟨x0, hx0, hxc0, hT0⟩ :=
            instance_of_lits_true (P := P) (B := B) (tr := tr) (Cs := Cs) hbt
              (commit := true) (o := c0) hc0 hallc0
          by_cases hkall : ∀ l ∈ authOccLits (shapeOf P B) P k,
              l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true
          · exfalso
            obtain ⟨x1, hx1, hxc1, hT1⟩ :=
              instance_of_lits_true (P := P) (B := B) (tr := tr) (Cs := Cs) hbt
                (commit := false) (o := k) hk hkall
            have hclaim : (x1.tag, x1.peer, x1.val) ∈ claimsOf P Cs tr := by
              unfold claimsOf
              rw [List.mem_filterMap]
              exact ⟨x1, hx1, by rw [hxc1]; rfl⟩
            have hcommit : (x0.tag, x0.peer, x0.val) ∈ commitsOf P Cs tr := by
              unfold commitsOf
              rw [List.mem_filterMap]
              exact ⟨x0, hx0, by rw [hxc0]; rfl⟩
            have heq : some (x0.tag, x0.peer, x0.val) =
                some (x1.tag, x1.peer, x1.val) := by
              rw [← hT0, ← hT1, triples_eq_of_claimExcuses hc0 hk hex]
            have heq2 : (x0.tag, x0.peer, x0.val) = (x1.tag, x1.peer, x1.val) :=
              Option.some.inj heq
            exact hall _ hcommit (by rw [heq2]; exact hclaim)
          · obtain ⟨l, hl, hfalse⟩ : ∃ l ∈ authOccLits (shapeOf P B) P k,
                l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = false := by
              push_neg at hkall
              obtain ⟨l, hl, h⟩ := hkall
              refine ⟨l, hl, ?_⟩
              cases e : l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) <;> simp_all
            refine clause_eval_holds l.flip
              (List.mem_append_right _ (List.mem_map.mpr ⟨l, hl, rfl⟩)) ?_
            have hAg : l.eval (assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr)) =
                l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) :=
              authOccLits_eval_ag (P := P) (B := B) (commit := false) (o := k) hk heIdx l hl
            rw [Lit.flip_eval, hAg, hfalse]
            simp
      · rw [if_neg hex] at hsome
        exact absurd hsome (by simp)
  · -- a selected violation must be a realized commit
    rw [authAuxClauses, List.mem_flatMap] at hcl
    obtain ⟨o, ho, hcl⟩ := hcl
    have hiff : assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr)
        (authOccVar (shapeOf P B) P o) = true <->
        (∀ l ∈ authOccLits (shapeOf P B) P o,
          l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true) :=
      assignOfAg_aux_iff ho
    have hAg : ∀ l ∈ authOccLits (shapeOf P B) P o,
        l.eval (assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr)) =
          l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) :=
      authOccLits_eval_ag (P := P) (B := B) (commit := true) (o := o) ho heIdx
    refine (sat_authSelectorClauses.mpr ?_) cl hcl
    intro hau l hl
    rw [hAg l hl]
    exact hiff.mp hau l hl

/-! ### Completeness -/

/-- **COMPLETENESS for the agreement goal.** A permitted bounded attack run in which no committed
triple was ever claimed yields a model of the goal-indexed agreement formula. Note that
\textsf{univClosed} is not consumed by this proof - completeness builds the assignment FROM the run,
so it never has to name a value the universe lacks - and it is kept only to mirror the shape the
soundness theorems take. Dropping it would strengthen the statement; keeping it makes the two
directions line up. -/
theorem encoding_complete_agreement_of {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (hgap : domainGap P B = false) (hbt : BoundedTrace P B tr Cs)
    (hall : ∀ t ∈ commitsOf P Cs tr, t ∉ claimsOf P Cs tr)
    (hbrk : AuthBreak P Cs tr) :
    Satisfiable (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) := by
  have hbnd : WithinBounds P B (cfgAt Cs) (evAt tr) := withinBounds_of_bounded hbt hgap
  have hrel : ∀ i, Rel P (cfgAt Cs i) (evAt tr i) (cfgAt Cs (i + 1)) := (runs_rel hbt.1).2
  have hcfg0 : cfgAt Cs 0 = initCfg P := ((runs_rel hbt.1).1).symm
  have heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B) :=
    runOK_eIdx (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  have hvars : ∀ E ∈ allExprs P, ∀ x ∈ Expr.vars E, x < shV (shapeOf P B) :=
    runOK_vars (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  have hwritten : ∀ q c act, P.actionAt q c = some act -> ∀ x ∈ act.written,
      x < shV (shapeOf P B) := runOK_written (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  have hpcAct : ∀ q c, P.actionAt q c ≠ none -> c + 1 < shPc (shapeOf P B) :=
    runOK_pcAct (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  set a := assignOfAg (shapeOf P B) P (cfgAt Cs) (evAt tr) with ha_def
  have htr {g : CNF} (hb : below (nVarsAll (shapeOf P B)) g.clauses)
      (hs : Sat (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) g) : Sat a g :=
    sat_congr _ hb (fun v hv => (assignOfAg_below hv).symm) hs
  refine ⟨a, ?_⟩
  rw [encodeGoalsOfM_agreement, AuthClauses.agreementEncode]
  refine sat_append.mpr ⟨sat_baseEncode_of_groups
      (htr below_oneHot (sat_oneHot (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) hrel))
      (htr below_init (sat_init (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hcfg0))
      (htr below_frame (sat_frame (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel))
      (htr (below_eval heIdx hvars)
        (sat_eval (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd))
      (htr (below_step heIdx hwritten hpcAct)
        (sat_step (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel))
      (htr below_ded (sat_ded (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) hrel))
      (htr (below_pubAux heIdx) (sat_pubAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd))
      (htr below_knSupport (sat_knSupport (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) U_nodup hrel))
      (htr below_fresh (sat_fresh (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (fun N hN => nonces_subset_univ P B N hN) hrel))
      (htr below_leakAux (sat_leakAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd)),
    sat_authViolation_of_all_unclaimed (P := P) (B := B) (tr := tr) (Cs := Cs)
      hbt hbnd hN heIdx hall hbrk⟩


/-! ### The instance -/

abbrev gapP : Protocol := Regressions.Authentication.P
abbrev gapB : Bounds := Regressions.Authentication.B
abbrev gapC : Certificate := Regressions.Authentication.c

theorem gap_gapFree : domainGap gapP gapB = false := by decide

theorem gap_bt : BoundedTrace gapP gapB (certTrace gapC) (certCfgs gapC) :=
  ⟨checkSteps_runs gapP gapC.steps (initCfg gapP) (by decide),
    by decide,
    by
      change ∀ C ∈ certCfgs gapC, cfgInUniverse C (univ gapP gapB) = true
      decide⟩

theorem gap_tr : certTrace gapC = Regressions.Authentication.tr :=
  Examples.certOfTrace_trace gapP Regressions.Authentication.tr

theorem gap_break : AuthBreak gapP (certCfgs gapC) (certTrace gapC) := by
  rw [gap_tr]
  exact Regressions.Authentication.authBreak

theorem gap_all : ∀ t ∈ commitsOf gapP (certCfgs gapC) (certTrace gapC),
    t ∉ claimsOf gapP (certCfgs gapC) (certTrace gapC) := by decide

theorem gap_complete :
    Satisfiable (encodeGoalsOfM gapP gapB [Goal.agreement] Matching.tripleOnly) :=
  encoding_complete_agreement_of (P := gapP) (B := gapB)
    (tr := certTrace gapC) (Cs := certCfgs gapC)
    AgreesBase.authGap_univClosed AgreesBase.authGap_authNameable gap_gapFree gap_bt gap_all
    gap_break

/-! ### Assignment extension and selected-violation facts -/

/-- **The obstruction the task's route runs into.** The agreement auxiliaries live strictly above every
block \textsf{Complete.assignOf} knows about, so the characteristic assignment sets every one of them
false. When the model has a commit occurrence at all, the demand clause is therefore refuted by
\textsf{assignOf} itself: the completeness witness has to be an extension of the characteristic
assignment, and the ten semantic groups have to be transferred across that extension. -/
theorem assignOf_not_a_model_of_agreement {P : Protocol} {B : Bounds}
    (cfg : Nat -> Cfg) (ev : Nat -> Ev) :
    ¬ Sat (assignOf (shapeOf P B) P cfg ev)
      (authViolationClauses Matching.tripleOnly (shapeOf P B) P) := by
  intro h
  have hcl := h (authViolationLits (shapeOf P B) P)
    (List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _)))
  rw [Clause.eval, List.any_eq_true] at hcl
  obtain ⟨l, hl, hal⟩ := hcl
  rw [authViolationLits, List.mem_map] at hl
  obtain ⟨o, ho, rfl⟩ := hl
  have hle : bsAuth (shapeOf P B) ≤ authOccVar (shapeOf P B) P o := by
    show bsAuth (shapeOf P B) ≤ bsAuth (shapeOf P B) + ixOf o (authOccs (shapeOf P B) P true)
    exact Nat.le_add_right _ _
  have hf : assignOf (shapeOf P B) P cfg ev (authOccVar (shapeOf P B) P o) = false :=
    assignOf_ge_bsAuth hle
  have h2 : (pos (authOccVar (shapeOf P B) P o)).eval (assignOf (shapeOf P B) P cfg ev) = true := hal
  simp [pos_eval, hf] at h2

/-- Every selected violating commit has no realized excusing claim. Other commits may be matched. -/
theorem every_selected_commit_is_unexcused {P : Protocol} {B : Bounds} {a : Assignment}
    (h : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly))
    {c : AuthOcc} (hc : c ∈ authOccs (shapeOf P B) P true)
    (haux : a (authOccVar (shapeOf P B) P c) = true)
    {k : AuthOcc} (hk : k ∈ authOccs (shapeOf P B) P false)
    (hex : claimExcuses Matching.tripleOnly (shapeOf P B) P c k = true) :
    ∃ l ∈ authOccLits (shapeOf P B) P k, l.eval a = false :=
  GoalEncode.authNoExcuse (by simp) h hc hk hex haux

/-! ### Selecting one unclaimed commit: completeness without the all-unclaimed restriction -/

/-- Distinct named occurrences have distinct selector variables. -/
theorem authOccVar_inj {sh : Shape} {P : Protocol} {c k : AuthOcc}
    (hc : c ∈ authOccs sh P true) (hk : k ∈ authOccs sh P true)
    (h : authOccVar sh P c = authOccVar sh P k) : c = k := by
  have hi : ixOf c (authOccs sh P true) = ixOf k (authOccs sh P true) :=
    Nat.add_left_cancel h
  have he := congrArg (rget (authOccs sh P true)) hi
  rw [rget_ixOf _ _ hc, rget_ixOf _ _ hk] at he
  exact Option.some.inj he

/-- Preserve the characteristic run assignment and select exactly one violating occurrence. -/
def assignOfSelected (sh : Shape) (P : Protocol) (cfg : Nat → Cfg) (ev : Nat → Ev)
    (chosen : AuthOcc) : Assignment :=
  fun v => if v < bsAuth sh then assignOf sh P cfg ev v
    else decide (v = authOccVar sh P chosen)

theorem assignOfSelected_below {sh : Shape} {P : Protocol} {cfg : Nat → Cfg} {ev : Nat → Ev}
    {chosen : AuthOcc} {v : BVar} (hv : v < bsAuth sh) :
    assignOfSelected sh P cfg ev chosen v = assignOf sh P cfg ev v := by
  simp [assignOfSelected, hv]

theorem assignOfSelected_aux_iff {sh : Shape} {P : Protocol} {cfg : Nat → Cfg} {ev : Nat → Ev}
    {chosen c : AuthOcc} (hc : c ∈ authOccs sh P true)
    (hchosen : chosen ∈ authOccs sh P true) :
    assignOfSelected sh P cfg ev chosen (authOccVar sh P c) = true ↔ c = chosen := by
  have hge : ¬ authOccVar sh P c < bsAuth sh := by
    exact Nat.not_lt.mpr (Nat.le_add_right (bsAuth sh) _)
  simp only [assignOfSelected, if_neg hge, decide_eq_true_eq]
  exact ⟨authOccVar_inj hc hchosen, fun h => congrArg (authOccVar sh P) h⟩

theorem authOccLits_eval_selected {P : Protocol} {B : Bounds} {commit : Bool}
    {o chosen : AuthOcc} {cfg : Nat → Cfg} {ev : Nat → Ev}
    (ho : o ∈ authOccs (shapeOf P B) P commit)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B)) :
    ∀ l ∈ authOccLits (shapeOf P B) P o,
      l.eval (assignOfSelected (shapeOf P B) P cfg ev chosen) =
        l.eval (assignOf (shapeOf P B) P cfg ev) := by
  intro l hl
  exact lit_eval_congr (assignOfSelected_below (authOccLits_below ho heIdx l hl))

/-- An agreement break provides a realized named commit whose triple is unclaimed. -/
theorem unclaimed_occurrence_of_authBreak {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hok : WithinBounds P B (cfgAt Cs) (evAt tr))
    (hN : authNameable (shapeOf P B) P)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B))
    (hbrk : AuthBreak P Cs tr) :
    ∃ o ∈ authOccs (shapeOf P B) P true, ∃ t,
      authTriple (shapeOf P B) o = some t ∧ t ∉ claimsOf P Cs tr ∧
      ∀ l ∈ authOccLits (shapeOf P B) P o,
        l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true := by
  obtain ⟨t, hc, hnc⟩ := hbrk
  simp only [commitsOf, List.mem_filterMap] at hc
  obtain ⟨x, hx, hfx⟩ := hc
  have hxc : x.isCommit = true := by
    cases h : x.isCommit
    · simp [h] at hfx
    · rfl
  have htrip : (x.tag, x.peer, x.val) = t := by
    simpa [hxc] using hfx
  obtain ⟨i, C, e, hi, hzip, hstep⟩ := AgreesBase.mem_authInsts_elim hx
  rw [AgreesBase.rget_zip] at hzip
  obtain ⟨hCi, hei⟩ := hzip
  have hCe : C = cfgAt Cs i := (cfgAt_eq_of_rget Cs i C hCi).symm
  have hee : e = evAt tr i := (evAt_eq_of_rget tr i e hei).symm
  subst hCe
  subst hee
  have hi' : i < tr.length := by
    have hz : (Cs.zip tr).length ≤ tr.length := by simp [List.length_zip]
    omega
  obtain ⟨o, ho, hot, hall⟩ := lits_true_of_instance hbt hok hN heIdx hx hxc hi' hstep
  exact ⟨o, ho, t, htrip ▸ hot, hnc, hall⟩

/-- The selected violation is realized and no matching claim occurs; other commits are unrestricted. -/
theorem sat_authViolation_selected {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs)
    (heIdx : ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B))
    {chosen : AuthOcc} (hchosen : chosen ∈ authOccs (shapeOf P B) P true)
    {t : Tag × Agent × Term} (ht : authTriple (shapeOf P B) chosen = some t)
    (hnt : t ∉ claimsOf P Cs tr)
    (hlits : ∀ l ∈ authOccLits (shapeOf P B) P chosen,
      l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true) :
    Sat (assignOfSelected (shapeOf P B) P (cfgAt Cs) (evAt tr) chosen)
      (authViolationClauses Matching.tripleOnly (shapeOf P B) P) := by
  let a := assignOfSelected (shapeOf P B) P (cfgAt Cs) (evAt tr) chosen
  have hsel : ∀ c ∈ authOccs (shapeOf P B) P true,
      a (authOccVar (shapeOf P B) P c) = true ↔ c = chosen :=
    fun c hc => assignOfSelected_aux_iff hc hchosen
  have heval {commit : Bool} {o : AuthOcc} (ho : o ∈ authOccs (shapeOf P B) P commit) :
      ∀ l ∈ authOccLits (shapeOf P B) P o,
        l.eval a = l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) :=
    authOccLits_eval_selected ho heIdx
  intro cl hcl
  rw [authViolationClauses, cnfOf, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · rw [List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · rw [List.mem_singleton] at hcl
      subst hcl
      refine clause_eval_holds (pos (authOccVar (shapeOf P B) P chosen)) ?_
        ((hsel chosen hchosen).mpr rfl)
      exact List.mem_map.mpr ⟨chosen, hchosen, rfl⟩
    · rw [authExcuseClauses, List.mem_flatMap] at hcl
      obtain ⟨c, hc, hcl⟩ := hcl
      rw [List.mem_filterMap] at hcl
      obtain ⟨k, hk, hsome⟩ := hcl
      by_cases hex : claimExcuses Matching.tripleOnly (shapeOf P B) P c k
      · rw [if_pos hex] at hsome
        have heq := Option.some.inj hsome
        subst heq
        by_cases haux : a (authOccVar (shapeOf P B) P c) = true
        · have hcchosen := (hsel c hc).mp haux
          subst hcchosen
          have hnot : ¬ ∀ l ∈ authOccLits (shapeOf P B) P k,
              l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = true := by
            intro hall
            obtain ⟨x, hx, hxc, htx⟩ := instance_of_lits_true hbt hk hall
            have hclaim : (x.tag, x.peer, x.val) ∈ claimsOf P Cs tr := by
              unfold claimsOf
              exact List.mem_filterMap.mpr ⟨x, hx, by rw [hxc]; rfl⟩
            have heq : t = (x.tag, x.peer, x.val) := by
              apply Option.some.inj
              rw [← ht, triples_eq_of_claimExcuses hchosen hk hex, htx]
            exact hnt (heq ▸ hclaim)
          push_neg at hnot
          obtain ⟨l, hl, hfalse⟩ := hnot
          have hf : l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) = false := by
            cases hh : l.eval (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) <;> simp_all
          refine clause_eval_holds l.flip
            (List.mem_append_right _ (List.mem_map.mpr ⟨l, hl, rfl⟩)) ?_
          rw [Lit.flip_eval, heval hk l hl, hf]
          rfl
        · have hf : a (authOccVar (shapeOf P B) P c) = false := by
            cases hh : a (authOccVar (shapeOf P B) P c) <;> simp_all
          refine clause_eval_holds (neg (authOccVar (shapeOf P B) P c))
            (List.mem_append_left _ (List.Mem.head _)) ?_
          simpa [neg_eval] using hf
      · rw [if_neg hex] at hsome
        simp at hsome
  · rw [authAuxClauses, List.mem_flatMap] at hcl
    obtain ⟨c, hc, hcl⟩ := hcl
    refine (sat_authSelectorClauses.mpr ?_) cl hcl
    intro haux l hl
    have hcchosen := (hsel c hc).mp haux
    subst hcchosen
    rw [heval hchosen l hl]
    exact hlits l hl

/-- Agreement completeness: any representable bounded agreement break yields a model.
Only the violating commit is selected; matched commits may occur in the same run. -/
theorem encoding_complete_agreement {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hN : authNameable (shapeOf P B) P) (hgap : domainGap P B = false)
    (hbt : BoundedTrace P B tr Cs) (hbrk : AuthBreak P Cs tr) :
    Satisfiable (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) := by
  have hbnd := withinBounds_of_bounded hbt hgap
  have hrel := (runs_rel hbt.1).2
  have hcfg0 : cfgAt Cs 0 = initCfg P := ((runs_rel hbt.1).1).symm
  have heIdx := runOK_eIdx (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  have hvars := runOK_vars (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  have hwritten := runOK_written (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  have hpcAct := runOK_pcAct (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
  obtain ⟨chosen, hchosen, t, ht, hnt, hlits⟩ :=
    unclaimed_occurrence_of_authBreak hbt hbnd hN heIdx hbrk
  let a := assignOfSelected (shapeOf P B) P (cfgAt Cs) (evAt tr) chosen
  have htr {g : CNF} (hb : below (nVarsAll (shapeOf P B)) g.clauses)
      (hs : Sat (assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr)) g) : Sat a g :=
    sat_congr _ hb (fun v hv => (assignOfSelected_below hv).symm) hs
  refine ⟨a, ?_⟩
  rw [encodeGoalsOfM_agreement, AuthClauses.agreementEncode]
  refine sat_append.mpr ⟨sat_baseEncode_of_groups
      (htr below_oneHot (sat_oneHot (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) hrel))
      (htr below_init (sat_init (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hcfg0))
      (htr below_frame (sat_frame (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel))
      (htr (below_eval heIdx hvars) (sat_eval (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd))
      (htr (below_step heIdx hwritten hpcAct)
        (sat_step (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd hrel))
      (htr below_ded (sat_ded (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) hrel))
      (htr (below_pubAux heIdx) (sat_pubAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd))
      (htr below_knSupport (sat_knSupport (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (univSub_shapeOf P B) U_nodup hrel))
      (htr below_fresh (sat_fresh (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd
        (fun N hN => nonces_subset_univ P B N hN) hrel))
      (htr below_leakAux (sat_leakAux (shapeOf P B) P (cfgAt Cs) (evAt tr) hbnd)),
    sat_authViolation_selected hbt heIdx hchosen ht hnt hlits⟩

/-- The corrected formula corresponds exactly to the query's unordered agreement goal. -/
theorem encoding_correct_agreement {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (hgap : domainGap P B = false) :
    Satisfiable (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) ↔
      boundedAttackGoals (Query.mk P B [Goal.agreement]) := by
  constructor
  · exact AgreesBase.boundedAttackGoals_of_satisfiable_agreement hU hN
  · rintro ⟨g, hg, tr, Cs, hbt, hv⟩
    have hg' : g = Goal.agreement := List.mem_singleton.mp hg
    subst hg'
    exact encoding_complete_agreement hN hgap hbt hv

/-- Unsatisfiability rules out the unordered agreement goal under the same explicit hypotheses. -/
theorem boundedSafe_agreement_of_unsat {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (hgap : domainGap P B = false)
    (hunsat : Unsat (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly)) :
    boundedSafeGoals (Query.mk P B [Goal.agreement]) := by
  intro hattack
  exact hunsat ((encoding_correct_agreement hU hN hgap).mpr hattack)

end ProtSat.AgreesBaseComplete
