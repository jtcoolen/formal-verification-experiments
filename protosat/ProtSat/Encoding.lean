/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Clauses

/-!
# ProtSat: the correspondence between bounded attacks and satisfying assignments

This module contains the principal results of the project, specification sections 8A and
8B.  Writing sh := ProtSat.Encode.shapeOf P B for the shape of the analysis and a for an
assignment of its variables, we prove

* ProtSat.Encoding.encoding_sound (8A): every satisfying assignment of encode P B decodes
  to a bounded attack on P within the bounds B;
* ProtSat.Encoding.encoding_complete (8B): every bounded attack on P within the bounds B is
  represented by a satisfying assignment of encode P B.

Both directions assume the universe hypothesis ProtSat.Encode.univClosed: the bounds must be
large enough that the protocol's own message operations stay inside the universe.  The
analyser tests that hypothesis by computation before trusting an answer, and reports that
the bounds are too small when it fails.

## How the proofs are organised

Four correspondences tie the Boolean variables to the semantic objects of
ProtSat.Operational:

* decodePc_of_true / decodePc_true: the program counter decoded from a pc group is the one
  the assignment selects;
* readVar_decodeStore: the store decoded by ProtSat.Encode.decodeStore reads back through
  the store groups;
* decXe_eq: the value decoded from the Tseitin group of an expression is the value of that
  expression in the decoded store - by structural induction over the expression table,
  using ProtSat.Expr.eval_child1 / eval_child2 and ProtSat.OneHot.fwdClausesOn_correct;
* decKn_corr: a universe message belongs to the decoded knowledge list exactly when its kn
  variable is true - by induction over the step, using the frame, deduction, support and
  send clauses.

With those in hand, each of the ten introduction rules of ProtSat.Rel is discharged by
reading off the event alternative the assignment selected and applying the step clauses
guarded by it.
-/

namespace ProtSat.Encoding

open ProtSat Term OneHot Bounded Attacker Encode
open Protocol

variable {P : Protocol} {B : Bounds} {a : Assignment}

/-! ### Elementary facts about lists and about the shape -/

/-- Erasing duplicates produces a duplicate-free list. -/
theorem nodup_eraseDups [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.Nodup := by
  have key : ∀ (n : Nat) (l : List α), l.length ≤ n -> l.eraseDups.Nodup := by
    intro n
    induction n with
    | zero =>
        intro l hl
        have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        exact List.nodup_nil
    | succ n ih =>
        intro l hl
        cases l with
        | nil => exact List.nodup_nil
        | cons x xs =>
            rw [List.eraseDups_cons]
            refine (List.nodup_cons).mpr ⟨?_, ih _ (Nat.le_trans (List.length_filter_le _ _) ?_)⟩
            · intro h
              rw [List.mem_eraseDups, List.mem_filter] at h
              exact absurd h.2 (by simp)
            · simpa [List.length_cons] using hl
  intro l
  exact key (List.length l) l (Nat.le_refl _)

/-- Membership and the boolean contains test agree. -/
theorem contains_mem [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    l.contains a = true <-> a ∈ l := by
  unfold List.contains
  rw [List.elem_eq_mem]
  by_cases h : a ∈ l <;> simp [h]

/-- The universe of an analysis is duplicate-free. -/
theorem U_nodup : (shapeOf P B).U.Nodup := nodup_eraseDups _

/-- In a duplicate-free list, two positions holding the same element are equal. -/
theorem rget_nodup_inj {α : Type} : ∀ (l : List α), l.Nodup ->
    ∀ (u v : Nat) (x : α), rget l u = some x -> rget l v = some x -> u = v := by
  intro l
  induction l with
  | nil => intro _ u v x hx _; exact absurd hx (by simp [rget])
  | cons y ys ih =>
      intro hnd u v x hu hv
      rw [List.nodup_cons] at hnd
      cases u with
      | zero =>
          cases v with
          | zero => rfl
          | succ v =>
              rw [show rget (y :: ys) 0 = some y from rfl] at hu
              rw [rget_succ] at hv
              have hyx : x = y := (Option.some.inj hu).symm
              subst hyx
              exact absurd (rget_some_mem ys v _ hv) hnd.1
      | succ u =>
          cases v with
          | zero =>
              rw [rget_succ] at hu
              have hyx : x = y := (Option.some.inj hv).symm
              subst hyx
              exact absurd (rget_some_mem ys u _ hu) hnd.1
          | succ v =>
              rw [rget_succ] at hu
              rw [rget_succ] at hv
              exact congrArg Nat.succ (ih hnd.2 u v x hu hv)

/-- Two in-range universe positions holding the same message are equal. -/
theorem valAt_inj {u v : Nat} (hu : u < (shapeOf P B).U.length)
    (hv : v < (shapeOf P B).U.length)
    (h : valAt (shapeOf P B) u = valAt (shapeOf P B) v) : u = v := by
  obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U u hu
  have h1 : rget (shapeOf P B).U u = some t := ht
  have h2 : rget (shapeOf P B).U v = some t := by
    have h3 : valAt (shapeOf P B) v = some t := by
      rw [← h]
      exact h1
    exact h3
  exact rget_nodup_inj (shapeOf P B).U U_nodup u v t h1 h2

/-- The position of a universe message is in range. -/
theorem uIdx_lt_of_mem {t : Term} (ht : t ∈ (shapeOf P B).U) :
    uIdx (shapeOf P B) (some t) < (shapeOf P B).U.length := by
  have h1 : rget (shapeOf P B).U (ixOf t (shapeOf P B).U) = some t := rget_ixOf _ _ ht
  show ixOf t (shapeOf P B).U < (shapeOf P B).U.length
  by_contra e
  have h2 : rget (shapeOf P B).U (ixOf t (shapeOf P B).U) = none :=
    rget_oob_ge _ _ (by omega)
  rw [h2] at h1; simp at h1

/-- The number of a universe message inverts valAt. -/
theorem uIdx_valAt {u : Nat} (hu : u < (shapeOf P B).U.length) :
    uIdx (shapeOf P B) (valAt (shapeOf P B) u) = u := by
  obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U u hu
  have hval : valAt (shapeOf P B) u = some t := ht
  have hmem : t ∈ (shapeOf P B).U := rget_mem (shapeOf P B).U u t hu ht
  have h2 : valAt (shapeOf P B) (uIdx (shapeOf P B) (valAt (shapeOf P B) u))
      = valAt (shapeOf P B) u := by
    rw [hval, valAt_uIdx_some (shapeOf P B) hmem, ← hval]
  exact valAt_inj (by rw [hval]; exact uIdx_lt_of_mem hmem) hu h2

/-- An admissible value is recovered from its number. -/
theorem valAt_uIdx_adm {v : Val} (h : admissible (shapeOf P B) v = true) :
    valAt (shapeOf P B) (uIdx (shapeOf P B) v) = v :=
  admissible_valAt_uIdx v h

/-- Every in-range position holds an admissible value. -/
theorem admissible_valAt {u : Nat} (hu : u < shVal (shapeOf P B)) :
    admissible (shapeOf P B) (valAt (shapeOf P B) u) = true := by
  cases h : valAt (shapeOf P B) u with
  | none => simp [admissible]
  | some t =>
      have hu' : u < (shapeOf P B).U.length := by
        rw [shVal] at hu
        by_contra e
        have h2 : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
        rw [h2] at h; simp at h
      show ((shapeOf P B).U).contains t = true
      rw [contains_mem]
      exact rget_mem (shapeOf P B).U u t hu' h

/-- The initial knowledge is contained in the universe. -/
theorem initKn_mem_univ {t : Term} (h : t ∈ P.initKn) : t ∈ (shapeOf P B).U :=
  initKn_subset_univ P B t h

/-- A domain nonce is contained in the universe. -/
theorem nonceDomain_mem_univ {N : NonceName} (h : N ∈ P.nonceDomain) :
    Term.nonce N ∈ (shapeOf P B).U := nonces_subset_univ P B N h

/-- A declared closed secret is contained in the universe. -/
theorem closedSecret_mem_univ {t : Term} (h : t ∈ P.closedSecretTerms) :
    t ∈ (shapeOf P B).U := secrets_subset_univ P B t h

/-! ### Extracting the clause groups from a satisfying assignment -/

theorem sat_oneHot (h : Sat a (encode P B)) : Sat a (oneHotClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_init (h : Sat a (encode P B)) : Sat a (initClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_frame (h : Sat a (encode P B)) : Sat a (frameClauses (shapeOf P B)) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_eval (h : Sat a (encode P B)) : Sat a (evalClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_step (h : Sat a (encode P B)) : Sat a (stepClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_ded (h : Sat a (encode P B)) : Sat a (dedClauses (shapeOf P B)) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_pubAux (h : Sat a (encode P B)) : Sat a (pubAuxClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_knSupport (h : Sat a (encode P B)) : Sat a (knSupportClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_fresh (h : Sat a (encode P B)) : Sat a (freshClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_leakAux (h : Sat a (encode P B)) : Sat a (leakAuxClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_violation (h : Sat a (encode P B)) : Sat a (violationClauses (shapeOf P B) P) :=
  sat_encodeGroup (by simp [encodeGroups]) h

/-! ### Membership of each one-hot group's clauses in the one-hot family -/

theorem mem_oneHot_pc {i q : Nat} {cl : Clause} (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : cl ∈ (pcOh (shapeOf P B) i q).clauses.clauses) :
    cl ∈ (oneHotClauses (shapeOf P B) P).clauses := by
  have h1 : i < (shapeOf P B).steps + 1 := Nat.lt_succ_of_le hi
  unfold oneHotClauses cnfOf
  refine List.mem_flatMap.mpr ⟨ohPcClauses (shapeOf P B), List.Mem.head _, ?_⟩
  unfold ohPcClauses
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h1,
    List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, h⟩⟩

theorem mem_oneHot_st {i q x : Nat} {cl : Clause} (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (hx : x < shV (shapeOf P B))
    (h : cl ∈ (stOh (shapeOf P B) i q x).clauses.clauses) :
    cl ∈ (oneHotClauses (shapeOf P B) P).clauses := by
  have h1 : i < (shapeOf P B).steps + 1 := Nat.lt_succ_of_le hi
  unfold oneHotClauses cnfOf
  refine List.mem_flatMap.mpr ⟨ohStClauses (shapeOf P B), List.Mem.tail _ (List.Mem.head _), ?_⟩
  · unfold ohStClauses
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h1,
      List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
        List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, h⟩⟩⟩

theorem mem_oneHot_xe {i q e : Nat} {cl : Clause} (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (he : e < shE (shapeOf P B))
    (h : cl ∈ (xeOh (shapeOf P B) i q e).clauses.clauses) :
    cl ∈ (oneHotClauses (shapeOf P B) P).clauses := by
  have h1 : i < (shapeOf P B).steps + 1 := Nat.lt_succ_of_le hi
  unfold oneHotClauses cnfOf
  refine List.mem_flatMap.mpr ⟨ohXeClauses (shapeOf P B), ?_, ?_⟩
  · simp [List.mem_cons]
  · unfold ohXeClauses
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h1,
      List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
        List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he, h⟩⟩⟩

theorem mem_oneHot_ev {i : Nat} {cl : Clause} (hi : i < B.steps)
    (h : cl ∈ (evOh (shapeOf P B) i).clauses.clauses) :
    cl ∈ (oneHotClauses (shapeOf P B) P).clauses := by
  unfold oneHotClauses cnfOf
  refine List.mem_flatMap.mpr ⟨ohEvClauses (shapeOf P B), ?_, ?_⟩
  · simp [List.mem_cons]
  · unfold ohEvClauses
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h⟩

theorem mem_oneHot_dl {i q : Nat} {cl : Clause} (hi : i < B.steps)
    (hq : q < shS (shapeOf P B)) (h : cl ∈ (dlOh (shapeOf P B) i q).clauses.clauses) :
    cl ∈ (oneHotClauses (shapeOf P B) P).clauses := by
  unfold oneHotClauses cnfOf
  refine List.mem_flatMap.mpr ⟨ohDlClauses (shapeOf P B), ?_, ?_⟩
  · simp [List.mem_cons]
  · unfold ohDlClauses
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, h⟩⟩

theorem mem_oneHot_fr {i q : Nat} {cl : Clause} (hi : i < B.steps)
    (hq : q < shS (shapeOf P B)) (h : cl ∈ (frOh (shapeOf P B) i q).clauses.clauses) :
    cl ∈ (oneHotClauses (shapeOf P B) P).clauses := by
  unfold oneHotClauses cnfOf
  refine List.mem_flatMap.mpr ⟨ohFrClauses (shapeOf P B), ?_, ?_⟩
  · simp [List.mem_cons]
  · unfold ohFrClauses
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, h⟩⟩

/-! ### One-hot groups of a satisfying assignment -/

theorem sat_pcOh (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    Sat a (pcOh (shapeOf P B) i q).clauses :=
  fun cl hcl => sat_oneHot h cl (mem_oneHot_pc hi hq hcl)

theorem sat_stOh (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (encode P B)) :
    Sat a (stOh (shapeOf P B) i q x).clauses :=
  fun cl hcl => sat_oneHot h cl (mem_oneHot_st hi hq hx hcl)

theorem sat_xeOh (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (he : e < shE (shapeOf P B)) (h : Sat a (encode P B)) :
    Sat a (xeOh (shapeOf P B) i q e).clauses :=
  fun cl hcl => sat_oneHot h cl (mem_oneHot_xe hi hq he hcl)

theorem sat_evOh (hi : i < B.steps) (h : Sat a (encode P B)) :
    Sat a (evOh (shapeOf P B) i).clauses :=
  fun cl hcl => sat_oneHot h cl (mem_oneHot_ev hi hcl)

theorem sat_dlOh (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    Sat a (dlOh (shapeOf P B) i q).clauses :=
  fun cl hcl => sat_oneHot h cl (mem_oneHot_dl hi hq hcl)

theorem sat_frOh (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    Sat a (frOh (shapeOf P B) i q).clauses :=
  fun cl hcl => sat_oneHot h cl (mem_oneHot_fr hi hq hcl)

/-! ### Program counters -/

/-- The program counter the assignment selects for session q at step i is the true one. -/
theorem decodePc_true (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (encode P B)) :
    a (vpc (shapeOf P B) i q (decodePc (shapeOf P B) a i q)) = true := by
  have hoh := sat_pcOh hi hq h
  obtain ⟨c, hc⟩ := Oh.decode_some hoh
  have hcv : a (Oh.varOf (pcOh (shapeOf P B) i q) c) = true := (decodeGo_some _ _ _ _ hc).2
  unfold decodePc
  rw [hc]
  simpa [decodePc, pcOh, ohOf] using hcv

/-- If a program-counter variable is true, it is the decoded one. -/
theorem decodePc_of_true {i q c : Nat} (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (h : Sat a (encode P B))
    (ha : a (vpc (shapeOf P B) i q c) = true) :
    decodePc (shapeOf P B) a i q = c := by
  have hoh := sat_pcOh hi hq h
  have h1 : (pcOh (shapeOf P B) i q).decode a = some c :=
    Oh.decode_of_true hoh (List.mem_range.mpr hc) ha
  unfold decodePc
  rw [h1]
  simp

/-! ### Store slots -/

/-- Looking up a key in a list of pairs whose first components avoid that key. -/
theorem lookup_none_of_keys {x : Nat} : ∀ (l : List (Nat × Term)),
    (∀ p ∈ l, p.1 ≠ x) -> Expr.lookup x l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro h
      show (if p.1 = x then some p.2 else Expr.lookup x rest) = none
      rw [if_neg (h p (List.Mem.head _))]
      exact ih (fun q hq => h q (List.Mem.tail _ hq))

/-- Looking up a key in a filterMap of a key-preserving function. -/
theorem lookup_filterMap {f : Nat -> Option (Nat × Term)}
    (hf : ∀ y p, f y = some p -> p.1 = y) :
    ∀ (l : List Nat), l.Nodup -> ∀ x, x ∈ l ->
      Expr.lookup x (l.filterMap f) = (f x).map Prod.snd := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons y ys ih =>
      intro hnd x hx
      rw [List.nodup_cons] at hnd
      rw [List.mem_cons] at hx
      rw [List.filterMap_cons]
      rcases hx with hx | hx
      · subst hx
        cases h : f x with
        | none =>
            have hne : ∀ p ∈ ys.filterMap f, p.1 ≠ x := by
              intro p hp
              obtain ⟨z, hz, hzf⟩ := List.mem_filterMap.mp hp
              intro hpx
              have hzx : z = x := by rw [← hf z p hzf]; exact hpx
              exact hnd.1 (hzx ▸ hz)
            simpa using lookup_none_of_keys (ys.filterMap f) hne
        | some p =>
            show (if p.1 = x then some p.2 else Expr.lookup x (ys.filterMap f)) = some p.2
            rw [hf x p h]
            simp
      · cases h : f y with
        | none => simpa using ih hnd.2 x hx
        | some p =>
            have hne : ¬(y = x) := by
              intro e2
              subst e2
              exact hnd.1 hx
            show (if p.1 = x then some p.2 else Expr.lookup x (ys.filterMap f))
                = (f x).map Prod.snd
            rw [hf y p h, if_neg hne]
            exact ih hnd.2 x hx

/-- The value a store slot selects is the second component of its pair. -/
theorem decSt_slotPair (i q x : Nat) :
    decSt (shapeOf P B) a i q x = (slotPair (shapeOf P B) a i q x).map Prod.snd := by
  unfold decSt decVal slotPair
  cases h : (stOh (shapeOf P B) i q x).decode a with
  | none => simp [h]
  | some u => cases h2 : valAt (shapeOf P B) u <;> simp [h, h2]

/-- **Store correspondence.**  Reading variable x of the decoded store gives the value the
store group of x selects. -/
theorem readVar_decodeStore {i q x : Nat} (hx : x < shV (shapeOf P B)) :
    readVar x (decodeStore (shapeOf P B) a i q) = decSt (shapeOf P B) a i q x := by
  have hf : ∀ (y : Nat) (p : Nat × Term),
      slotPair (shapeOf P B) a i q y = some p -> p.1 = y := by
    intro y p h
    unfold slotPair at h
    cases h2 : (stOh (shapeOf P B) i q y).decode a with
    | none => rw [h2] at h; simp at h
    | some u =>
        cases h3 : valAt (shapeOf P B) u with
        | none => rw [h2] at h; simp [h3] at h
        | some t => rw [h2] at h; simp [h3] at h; cases h; rfl
  have h1 := lookup_filterMap hf (List.range (shV (shapeOf P B))) List.nodup_range x
    (List.mem_range.mpr hx)
  unfold decodeStore readVar
  rw [decSt_slotPair]
  exact h1
