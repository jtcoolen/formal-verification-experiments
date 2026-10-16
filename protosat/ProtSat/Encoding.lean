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

/-! ### Expression table membership -/

/-- Every expression is one of its own subexpressions. -/
theorem Expr.mem_subexpressions (e : Expr) : e ∈ e.subexpressions := by
  cases e with
  | agent A | nonce N | shrk a b | pubk a | privk a | var x => simp [Expr.subexpressions]
  | pair a b | encS a b | decS a b =>
      simp [Expr.subexpressions, List.mem_cons]
  | encA a _ | hash a | fst a | snd a | decA a _ =>
      simp [Expr.subexpressions, List.mem_cons]

/-- If the head of a drop is some a, then a is a member of the list. -/
theorem mem_of_head?_drop {α : Type} {a : α} : ∀ (l : List α) (c : Nat),
    (l.drop c).head? = some a -> a ∈ l := by
  intro l
  induction l with
  | nil => intro c h; exact absurd h (by simp)
  | cons x xs ih =>
      intro c h
      cases c with
      | zero =>
          cases h
          exact List.Mem.head _
      | succ c =>
          have h' : (xs.drop c).head? = some a := by simpa using h
          exact List.Mem.tail _ (ih c h')

/-- If session q has action a at program counter c, that action occurs in one of the roles.
-/
theorem mem_acts_of_actionAt {q c : Nat} {a : Action} (h : P.actionAt q c = some a) :
    a ∈ (P.roles.flatMap fun r => r.acts) := by
  unfold Protocol.actionAt at h
  have h0 : ((P.roleAt q).map (fun r => (r.acts.drop c).head?)).getD none = some a := h
  obtain ⟨r, hr, hdrop⟩ : ∃ r, P.roleAt q = some r ∧ (r.acts.drop c).head? = some a := by
    have h1 : ∃ r, P.roleAt q = some r := by
      by_contra e
      have : P.roleAt q = none := by
        cases h3 : P.roleAt q with
        | some r => exact absurd ⟨r, h3⟩ e
        | none => rfl
      rw [this] at h0; simp at h0
    obtain ⟨r, hr⟩ := h1
    exact ⟨r, hr, by rw [hr] at h0; exact h0⟩
  have hmem : a ∈ r.acts := mem_of_head?_drop r.acts c hdrop
  have hrr : r ∈ P.roles := by
    unfold Protocol.roleAt at hr
    cases h2 : (P.sessions.drop q).head? with
    | none => rw [h2] at hr; simp at hr
    | some s =>
        have h3 : (P.roles.drop s.role).head? = some r := by rw [h2] at hr; exact hr
        exact mem_of_head?_drop P.roles s.role h3
  exact List.mem_flatMap.mpr ⟨r, hrr, hmem⟩

/-- Every expression an action of the protocol evaluates is in the expression table. -/
theorem mem_allExprs {q c : Nat} {act : Action} (h : P.actionAt q c = some act) :
    ∀ e ∈ act.exprs, e ∈ allExprs P := by
  intro e he
  have ha : act ∈ P.roles.flatMap (fun r => r.acts) := mem_acts_of_actionAt h
  rcases List.mem_flatMap.mp ha with ⟨r, hr, ham⟩
  rw [allExprs, List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨act, ham, he⟩⟩

/-- The expression a send action transmits is in the expression table. -/
theorem mem_allExprs_send {q c : Nat} {a' : Agent} {e : Expr}
    (h : P.actionAt q c = some (Action.send a' e)) : e ∈ allExprs P :=
  mem_allExprs h e (by simp [Action.exprs, Expr.mem_subexpressions])

/-- The expressions an assign action evaluates are in the expression table. -/
theorem mem_allExprs_assign {q c : Nat} {x : Nat} {e : Expr}
    (h : P.actionAt q c = some (Action.assign x e)) : e ∈ allExprs P :=
  mem_allExprs h e (by simp [Action.exprs, Expr.mem_subexpressions])

/-- The expressions a check action compares are in the expression table. -/
theorem mem_allExprs_check {q c : Nat} {e1 e2 : Expr}
    (h : P.actionAt q c = some (Action.check e1 e2)) :
    e1 ∈ allExprs P ∧ e2 ∈ allExprs P :=
  ⟨mem_allExprs h e1 (by simp [Action.exprs, Expr.mem_subexpressions]), mem_allExprs h e2 (by simp [Action.exprs, Expr.mem_subexpressions])⟩

/-- The expressions a secret declaration reads are in the expression table. -/
theorem mem_allExprs_secret {q c : Nat} {e : Expr}
    (h : P.actionAt q c = some (Action.secret e)) : e ∈ allExprs P :=
  mem_allExprs h e (by simp [Action.exprs, Expr.mem_subexpressions])

/-- The expressions an authentication event evaluates are in the expression table. -/
theorem mem_allExprs_claim {q c : Nat} {t : Nat} {peer v : Expr}
    (h : P.actionAt q c = some (Action.claim t peer v)) :
    peer ∈ allExprs P ∧ v ∈ allExprs P :=
  ⟨mem_allExprs h peer (by simp [Action.exprs, Expr.mem_subexpressions]), mem_allExprs h v (by simp [Action.exprs, Expr.mem_subexpressions])⟩

theorem mem_allExprs_commit {q c : Nat} {t : Nat} {peer v : Expr}
    (h : P.actionAt q c = some (Action.commit t peer v)) :
    peer ∈ allExprs P ∧ v ∈ allExprs P :=
  ⟨mem_allExprs h peer (by simp [Action.exprs, Expr.mem_subexpressions]), mem_allExprs h v (by simp [Action.exprs, Expr.mem_subexpressions])⟩

/-- Two positions holding the same universe message are equal; no bounds are needed. -/
theorem valAt_inj_some {u v : Nat} {t : Term}
    (hu : valAt (shapeOf P B) u = some t) (hv : valAt (shapeOf P B) v = some t) : u = v :=
  rget_nodup_inj (shapeOf P B).U U_nodup u v t hu hv

/-! ### Membership helpers for the clause families -/

theorem mem_frame {i : Nat} {cl : Clause} (hi : i < B.steps) (h : cl ∈ frameKnClauses (shapeOf P B) i) :
    cl ∈ (frameClauses (shapeOf P B)).clauses := by
  unfold frameClauses cnfOf eachStep
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_append_left _ h⟩

theorem mem_initKn {u : Nat} {cl : Clause} (hu : u < (shapeOf P B).U.length)
    (h : cl ∈ initKnClauses (shapeOf P B) P) : cl ∈ (initClauses (shapeOf P B) P).clauses := by
  unfold initClauses cnfOf
  exact List.mem_append_right _ h

theorem mem_ded {i n : Nat} {cl : Clause} (hi : i < B.steps) (hn : n < nInst (shapeOf P B))
    (h : cl ∈ dedClausesAt (shapeOf P B) i n) : cl ∈ (dedClauses (shapeOf P B)).clauses := by
  unfold dedClauses cnfOf eachStep eachInst
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, h⟩⟩

theorem mem_step {i q c : Nat} {cl : Clause} (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (h : cl ∈ stepClausesAt (shapeOf P B) P i q c) :
    cl ∈ (stepClauses (shapeOf P B) P).clauses := by
  unfold stepClauses cnfOf eachStep eachSess eachPc
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
      List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, h⟩⟩⟩

theorem mem_knSupport {i u : Nat} {cl : Clause} (hi : i < B.steps) (hu : u < (shapeOf P B).U.length)
    (h : cl ∈ (List.range (shapeOf P B).U.length).map (fun u =>
        [neg (vkn (shapeOf P B) (i + 1) u), pos (vkn (shapeOf P B) i u)]
          ++ publisherLits (shapeOf P B) P i u)) :
    cl ∈ (knSupportClauses (shapeOf P B) P).clauses := by
  unfold knSupportClauses cnfOf eachStep mapMsg
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h⟩

theorem mem_pubAux {i q c u : Nat} {cl : Clause} (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (hu : u < (shapeOf P B).U.length)
    (h : cl ∈ pubAuxEntry (shapeOf P B) P i q c u) :
    cl ∈ (pubAuxClauses (shapeOf P B) P).clauses := by
  unfold pubAuxClauses cnfOf eachStep eachSess eachPc
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
      List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc,
        List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu, h⟩⟩⟩⟩

theorem mem_eval {i q e : Nat} {cl : Clause} (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (he : e < shE (shapeOf P B))
    (h : cl ∈ evalClausesEntry (shapeOf P B) P i q e) :
    cl ∈ (evalClauses (shapeOf P B) P).clauses := by
  unfold evalClauses cnfOf eachStep1 eachSess evalClausesAt eachExpr
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi),
    List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
      List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he, h⟩⟩⟩

theorem mem_fresh {i q c : Nat} {cl : Clause} (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (h : cl ∈ freshClausesAt (shapeOf P B) P i q c) :
    cl ∈ (freshClauses (shapeOf P B) P).clauses := by
  unfold freshClauses cnfOf eachStep eachSess eachPc
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
      List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, h⟩⟩⟩

/-! ### Events -/

/-- The event code the assignment selects at step i. -/
def decCode (P : Protocol) (B : Bounds) (a : Assignment) (i : Nat) : Nat :=
  ((evOh (shapeOf P B) i).decode a).getD 0

/-- The selected event code is true. -/
theorem decCode_true (hi : i < B.steps) (h : Sat a (encode P B)) :
    a (vev (shapeOf P B) i (decCode P B a i)) = true := by
  have hoh := sat_evOh hi h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hkv : a (Oh.varOf (evOh (shapeOf P B) i) k) = true := (decodeGo_some _ _ _ _ hk).2
  unfold decCode
  rw [hk]
  simpa [evOh, ohOf] using hkv

/-- If an event variable is true, it is the selected code. -/
theorem decCode_eq_of_true {i k : Nat} (hi : i < B.steps)
    (hk : k < shEv (shapeOf P B)) (h : Sat a (encode P B))
    (ha : a (vev (shapeOf P B) i k) = true) : decCode P B a i = k := by
  have hoh := sat_evOh hi h
  have h1 : (evOh (shapeOf P B) i).decode a = some k :=
    Oh.decode_of_true hoh (List.mem_range.mpr hk) ha
  unfold decCode
  rw [h1]
  exact rfl

/-- The selected event code is in range. -/
theorem decCode_lt (hi : i < B.steps) (h : Sat a (encode P B)) :
    decCode P B a i < shEv (shapeOf P B) := by
  have hoh := sat_evOh hi h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hmem := (decodeGo_some _ _ _ _ hk).1
  unfold decCode
  rw [hk]
  exact (List.mem_range.mp hmem)

/-- The decoded event is idle when the code is 0. -/
theorem decEv_of_code (hi : i < B.steps) (h : Sat a (encode P B)) :
    decEv (shapeOf P B) P a i =
      match (evOh (shapeOf P B) i).decode a with
      | none => Ev.idle
      | some k =>
          if k = 0 then Ev.idle
          else if h : k < 1 + shS (shapeOf P B) then
            Ev.act (k - 1) (decDeliver (shapeOf P B) a i (k - 1))
              (decNonce (shapeOf P B) a i (k - 1))
          else
            match instAt (shapeOf P B) (k - 1 - shS (shapeOf P B)) with
            | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
            | none => Ev.idle := rfl

/-! ### Decomposing the selected event -/

/-- The event group decodes to the selected code. -/
theorem decode_evOh (hi : i < B.steps) (h : Sat a (encode P B)) :
    (evOh (shapeOf P B) i).decode a = some (decCode P B a i) := by
  have hoh := sat_evOh hi h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hmem := (decodeGo_some _ _ _ _ hk).1
  have : decCode P B a i = k := by
    unfold decCode
    rw [hk]
    exact rfl
  rw [this]
  exact hk

/-- The learned message, expressed through the selected event code. -/
theorem decLearn_code (hi : i < B.steps) (h : Sat a (encode P B)) :
    decLearn (shapeOf P B) P a i =
      if decCode P B a i = 0 then none
      else if hc : decCode P B a i < 1 + shS (shapeOf P B) then
        match P.actionAt (decCode P B a i - 1)
            (decodePc (shapeOf P B) a i (decCode P B a i - 1)) with
        | some (Action.send _ e) =>
            decXe (shapeOf P B) P a i (decCode P B a i - 1) e
        | _ => none
      else
        match instAt (shapeOf P B) (decCode P B a i - 1 - shS (shapeOf P B)) with
        | some ins => valAt (shapeOf P B) ins.concl
        | none => none := by
  unfold decLearn
  rw [decode_evOh hi h]
  rfl

/-- The decoded event, expressed through the selected event code. -/
theorem decEv_code (hi : i < B.steps) (h : Sat a (encode P B)) :
    decEv (shapeOf P B) P a i =
      if decCode P B a i = 0 then Ev.idle
      else if hc : decCode P B a i < 1 + shS (shapeOf P B) then
        Ev.act (decCode P B a i - 1)
          (decDeliver (shapeOf P B) a i (decCode P B a i - 1))
          (decNonce (shapeOf P B) a i (decCode P B a i - 1))
      else
        match instAt (shapeOf P B) (decCode P B a i - 1 - shS (shapeOf P B)) with
        | some ins => match valAt (shapeOf P B) ins.concl with
            | some t => Ev.ded t
            | none => Ev.idle
        | none => Ev.idle := by
  unfold decEv
  rw [decode_evOh hi h]
  rfl

/-- The three possible shapes of the selected event code. -/
theorem ev_cases (hi : i < B.steps) (h : Sat a (encode P B)) :
    decCode P B a i = 0
    ∨ (∃ q, q < shS (shapeOf P B) ∧ decCode P B a i = 1 + q)
    ∨ (∃ n, n < nInst (shapeOf P B) ∧
          decCode P B a i = 1 + shS (shapeOf P B) + n) := by
  have hlt := decCode_lt hi h
  have h2 : decCode P B a i < 1 + shS (shapeOf P B) + nInst (shapeOf P B) := by
    unfold shEv at hlt
    exact hlt
  by_cases h0 : decCode P B a i = 0
  · exact Or.inl h0
  · right
    by_cases hq : decCode P B a i - 1 < shS (shapeOf P B)
    · exact Or.inl ⟨decCode P B a i - 1, hq, by omega⟩
    · exact Or.inr ⟨decCode P B a i - 1 - shS (shapeOf P B), by omega, by omega⟩

/-- The selected code is 0 exactly when its variable is true for the idle alternative. -/
theorem evAct_eq_of_code (hi : i < B.steps) (h : Sat a (encode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) :
    a (evAct (shapeOf P B) i q) = true := by
  have h1 : a (vev (shapeOf P B) i (decCode P B a i)) = true := decCode_true hi h
  rw [hk] at h1
  exact h1

/-- Sessions other than the selected one do not act. -/
theorem evAct_false_of_ne (hi : i < B.steps) (h : Sat a (encode P B)) {q r : Nat}
    (hq : q < shS (shapeOf P B)) (hr : r < shS (shapeOf P B)) (hne : q ≠ r)
    (hk : decCode P B a i = 1 + r) : a (evAct (shapeOf P B) i q) = false := by
  by_contra e
  have h2 : decCode P B a i = 1 + q := decCode_eq_of_true hi (by
    show 1 + q < shEv (shapeOf P B)
    exact evAct_lt (shapeOf P B) i q hq) h (by simpa [evAct] using e)
  omega

/-- No deduction instance fires when a session acts. -/
theorem evDed_false_of_code (hi : i < B.steps) (h : Sat a (encode P B)) {q n : Nat}
    (hq : q < shS (shapeOf P B)) (hn : n < nInst (shapeOf P B))
    (hk : decCode P B a i = 1 + q) :
    a (evDed (shapeOf P B) i n) = false := by
  by_contra e
  have h2 : decCode P B a i = 1 + shS (shapeOf P B) + n := decCode_eq_of_true hi (by
    show 1 + shS (shapeOf P B) + n < shEv (shapeOf P B)
    exact evDed_lt (shapeOf P B) i n hn) h (by simpa [evDed] using e)
  omega

/-- The idle alternative is selected exactly when the code is 0. -/
theorem evIdle_of_code (hi : i < B.steps) (h : Sat a (encode P B))
    (hk : decCode P B a i = 0) : a (evIdle (shapeOf P B) i) = true := by
  have h1 := decCode_true hi h
  rwa [hk] at h1

/-! ### Applying the step clauses -/

/-- The step clauses of an acting session with a known program counter hold. -/
theorem step_holds (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (hc : c < shPc (shapeOf P B))
    (h : Sat a (encode P B)) (ha : a (evAct (shapeOf P B) i q) = true)
    (hpc : a (vpc (shapeOf P B) i q c) = true)
    {cl : Clause} (hcl : cl ∈ stepClausesAt (shapeOf P B) P i q c) :
    Clause.eval a cl = true :=
  sat_step h cl (mem_step hi hq hc hcl)

/-- The guard literals of an acting session are false, so the body of a step clause must be
satisfied. -/
theorem step_body (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (hc : c < shPc (shapeOf P B))
    (h : Sat a (encode P B)) (ha : a (evAct (shapeOf P B) i q) = true)
    (hpc : a (vpc (shapeOf P B) i q c) = true) {rest : List Lit}
    (hcl : (actGuard (shapeOf P B) i q c ++ rest) ∈ stepClausesAt (shapeOf P B) P i q c) :
    Clause.eval a rest = true := by
  have := step_holds hi hq hc h ha hpc hcl
  refine clause_eval_append_of_false (actGuard (shapeOf P B) i q c) rest this ?_
  intro l hl
  unfold actGuard at hl
  rw [List.mem_cons] at hl
  rcases hl with rfl | hl
  · show (neg (evAct (shapeOf P B) i q)).eval a = false
    simp [neg_eval, ha]
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · show (neg (vpc (shapeOf P B) i q c)).eval a = false
      simp [neg_eval, hpc]
    · exact absurd hl (by simp)

/-- The frame clauses of a session that does not act hold. -/
theorem frame_holds (hi : i < B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B))
    (ha : a (evAct (shapeOf P B) i q) = false) :
    ∀ cl ∈ frameSessClauses (shapeOf P B) i q, Clause.eval a cl = true := by
  intro cl hcl
  have := sat_frame h cl (by
    unfold frameClauses cnfOf eachStep
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, hcl⟩)⟩)
  exact this

theorem frame_kn_holds (hi : i < B.steps) (h : Sat a (encode P B)) :
    ∀ cl ∈ frameKnClauses (shapeOf P B) i, Clause.eval a cl = true := by
  intro cl hcl
  exact sat_frame h cl (mem_frame hi hcl)

/-! ### More decoding facts -/

/-- The decoded program counter is in range. -/
theorem decodePc_lt (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    decodePc (shapeOf P B) a i q < shPc (shapeOf P B) := by
  have hoh := sat_pcOh hi hq h
  obtain ⟨k, hk⟩ := Oh.decode_some hoh
  have hmem : k ∈ (pcOh (shapeOf P B) i q).vals := (decodeGo_some _ _ _ _ hk).1
  have h2 : decodePc (shapeOf P B) a i q = k := by
    unfold decodePc
    rw [hk]
    exact rfl
  rw [h2]
  rw [pcOh, ohOf] at hmem
  exact List.mem_range.mp hmem

/-- The table index of an expression of the protocol is in range. -/
theorem eIdx_lt {e : Expr} (he : e ∈ allExprs P) : eIdx P e < shE (shapeOf P B) := by
  have h : eIdx P e ≤ (allExprs P).length := ixOf_le _ e
  have h2 : (allExprs P).length = (shapeOf P B).nE1 := rfl
  rw [shE]
  omega

/-- The value an evaluation group selects, together with the fact that its variable is true.
-/
theorem decXe_true {i q : Nat} {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    ∃ u, decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) u ∧
      a (vxe (shapeOf P B) i q (eIdx P e) u) = true := by
  have hix : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hoh := sat_xeOh hi hq hix h
  obtain ⟨u, hu⟩ := Oh.decode_some hoh
  have hmem := (decodeGo_some _ _ _ _ hu).2
  refine ⟨u, ?_, by simpa [xeOh, ohOf] using hmem⟩
  unfold decXe decVal
  rw [hu]

/-- If an evaluation variable is true, the group selects that value. -/
theorem decXe_of_true {i q : Nat} {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) {u : Nat}
    (hu : u < shVal (shapeOf P B)) (ha : a (vxe (shapeOf P B) i q (eIdx P e) u) = true) :
    decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) u := by
  have hix : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hoh := sat_xeOh hi hq hix h
  have h1 : (xeOh (shapeOf P B) i q (eIdx P e)).decode a = some u :=
    Oh.decode_of_true hoh (List.mem_range.mpr hu) ha
  unfold decXe decVal
  rw [h1]

/-- The in-range universe positions hold actual messages. -/
theorem valAt_some {u : Nat} (hu : u < (shapeOf P B).U.length) :
    ∃ t, valAt (shapeOf P B) u = some t := rget_lt (shapeOf P B).U u hu

/-- The knowledge after i+1 steps is the knowledge after i plus what step i taught. -/
theorem decKnSeq_succ (P : Protocol) (B : Bounds) (a : Assignment) (i : Nat) :
    decKnSeq (shapeOf P B) P a (i + 1) =
      decKnSeq (shapeOf P B) P a i ++ (decLearn (shapeOf P B) P a i).toList := rfl

/-- The selected code is 1+q when session q's event variable is true. -/
theorem decCode_of_evAct (hi : i < B.steps) (h : Sat a (encode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    decCode P B a i = 1 + q :=
  decCode_eq_of_true hi (evAct_lt (shapeOf P B) i q hq) h (by simpa [evAct] using ha)

/-- The selected code is the deduction instance when its event variable is true. -/
theorem decCode_of_evDed (hi : i < B.steps) (h : Sat a (encode P B)) {n : Nat}
    (hn : n < nInst (shapeOf P B)) (ha : a (evDed (shapeOf P B) i n) = true) :
    decCode P B a i = 1 + shS (shapeOf P B) + n :=
  decCode_eq_of_true hi (evDed_lt (shapeOf P B) i n hn) h (by simpa [evDed] using ha)

/-- What a session-act step teaches: the value sent, if the action is a send. -/
theorem decLearn_act (hi : i < B.steps) (h : Sat a (encode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) :
    decLearn (shapeOf P B) P a i =
        match P.actionAt q (decodePc (shapeOf P B) a i q) with
        | some (Action.send _ e) => decXe (shapeOf P B) P a i q e
        | _ => none := by
  rw [decLearn_code hi h, hk]
  rw [if_neg (by omega : 1 + q ≠ 0), dif_pos (by omega : 1 + q < 1 + shS (shapeOf P B))]
  rw [show (1 + q - 1) = q by omega]

/-- What a deduction step teaches: the conclusion of the instance that fired. -/
theorem decLearn_ded (hi : i < B.steps) (h : Sat a (encode P B)) {n : Nat}
    (hn : n < nInst (shapeOf P B)) (ins : DedInst) (hins : instAt (shapeOf P B) n = some ins)
    (hk : decCode P B a i = 1 + shS (shapeOf P B) + n) :
    decLearn (shapeOf P B) P a i = valAt (shapeOf P B) ins.concl := by
  rw [decLearn_code hi h, hk]
  rw [if_neg (by omega : 1 + shS (shapeOf P B) + n ≠ 0),
    dif_neg (by omega : ¬(1 + shS (shapeOf P B) + n < 1 + shS (shapeOf P B)))]
  rw [show (1 + shS (shapeOf P B) + n - 1 - shS (shapeOf P B)) = n by omega, hins]


/-- The publisher auxiliary of a send records the acting session, its program counter and
the value it sends. -/
theorem pubAux_holds {i q c u : Nat} (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (hu : u < (shapeOf P B).U.length)
    {a' : Agent} {e : Expr} (hact : P.actionAt q c = some (Action.send a' e))
    (h : Sat a (encode P B)) (ha : a (vpb (shapeOf P B) i q c u) = true) :
    a (evAct (shapeOf P B) i q) = true ∧ a (vpc (shapeOf P B) i q c) = true ∧
      a (vxe (shapeOf P B) i q (eIdx P e) u) = true := by
  have hsat : Sat a (andNDef (vpb (shapeOf P B) i q c u)
      [pos (evAct (shapeOf P B) i q), pos (vpc (shapeOf P B) i q c),
        pos (vxe (shapeOf P B) i q (eIdx P e) u)]) := by
    intro cl hcl
    refine sat_pubAux h cl (mem_pubAux hi hq hc hu ?_)
    rw [pubAuxEntry, hact]
    exact hcl
  have h2 := ((sat_andNDef).mp hsat).1 ha
  refine ⟨h2 _ (List.Mem.head _), h2 _ (List.Mem.tail _ (List.Mem.head _)),
    h2 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- **Initial knowledge is sound.**  If the assignment says the attacker knows a universe
message at step 0, then that message is part of the protocol's initial knowledge: the
initial clauses are the only place the attacker is given anything. -/
theorem init_kn_sound {u : Nat} {t : Term} (hut : valAt (shapeOf P B) u = some t)
    (h : Sat a (encode P B)) (ha : a (vkn (shapeOf P B) 0 u) = true) : t ∈ P.initKn := by
  have hu : u < (shapeOf P B).U.length := by
    by_contra e
    have : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
    rw [this] at hut
    simp at hut
  by_contra e
  have hfalse : initKnHolds (shapeOf P B) P u = false := by
    unfold initKnHolds
    rw [hut]
    simp [e]
  have hcl : [neg (vkn (shapeOf P B) 0 u)] ∈ (initClauses (shapeOf P B) P).clauses := by
    unfold initClauses cnfOf
    refine List.mem_append_right _ ?_
    unfold initKnClauses
    refine List.mem_map.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
    simp [hfalse]
  have h1 := sat_init h _ hcl
  rw [Clause.eval, List.any_cons, List.any_nil, neg_eval, ha] at h1
  simp at h1

/-- The two shapes a publisher literal can take. -/
theorem publisherLits_cases {i u : Nat} {l : Lit} (hi : i < B.steps)
    (hu : u < (shapeOf P B).U.length)
    (hl : l ∈ publisherLits (shapeOf P B) P i u) :
    (∃ q c : Nat, q < shS (shapeOf P B) ∧ c < shPc (shapeOf P B) ∧
        ∃ (a' : Agent) (e : Expr), P.actionAt q c = some (Action.send a' e) ∧
          l = pos (vpb (shapeOf P B) i q c u))
    ∨ (∃ n : Nat, ∃ ins : DedInst, n < nInst (shapeOf P B) ∧
        instAt (shapeOf P B) n = some ins ∧ ins.concl = u ∧ l = pos (evDed (shapeOf P B) i n)) := by
  rw [publisherLits, List.mem_append] at hl
  rcases hl with hl | hl
  · left
    simp only [litsSess, litsPc, List.mem_flatMap] at hl
    rcases hl with ⟨q, hq, c, hc, hl⟩
    cases h5 : P.actionAt q c with
    | none => exact absurd hl (by simp [sendPubLit, h5])
    | some act =>
        cases act with
        | send a' e =>
            have hred : sendPubLit (shapeOf P B) P i q c u = [pos (vpb (shapeOf P B) i q c u)] := by
              rw [sendPubLit, h5]
            rw [hred, List.mem_singleton] at hl
            exact ⟨q, c, List.mem_range.mp hq, List.mem_range.mp hc, a', e, h5, hl⟩
        | _ => exact absurd hl (by simp [sendPubLit, h5])
  · right
    simp only [litsInst, List.mem_flatMap] at hl
    rcases hl with ⟨n, hn, hl⟩
    cases hins : instAt (shapeOf P B) n with
    | none => exact absurd hl (by simp [instPublisher, hins])
    | some ins =>
        by_cases h5 : ins.concl = u
        · have hred : instPublisher (shapeOf P B) i n u = [pos (evDed (shapeOf P B) i n)] := by
            rw [instPublisher, hins]
            simp [h5]
          rw [hred, List.mem_singleton] at hl
          exact ⟨n, ins, List.mem_range.mp hn, hins, h5, hl⟩
        · have hred : instPublisher (shapeOf P B) i n u = [] := by
            rw [instPublisher, hins]
            simp [h5]
          exact absurd hl (by rw [hred]; simp)

/-- **Knowledge soundness** (the hard half of specification 8A).  If the assignment claims
that the attacker knows the universe message with number u at step i, then that message
really is in the knowledge of the decoded configuration: the kn variables are justified,
not guessed.  The induction uses the frame clauses (knowledge grows), the deduction
clauses, the publisher auxiliaries (a send that publishes u) and the support clauses
(nothing else makes u known). -/
theorem kn_sound (h : Sat a (encode P B)) {u : Nat} {t : Term}
    (hut : valAt (shapeOf P B) u = some t) :
    ∀ (i : Nat), i ≤ B.steps ->
      a (vkn (shapeOf P B) i u) = true -> t ∈ decKnSeq (shapeOf P B) P a i := by
  have hu : u < (shapeOf P B).U.length := by
    by_contra e
    have : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
    rw [this] at hut
    simp at hut
  intro i
  induction i with
  | zero =>
      intro _ ha
      unfold decKnSeq
      exact init_kn_sound hut h ha
  | succ i ih =>
      intro hi ha
      have hstep : i < B.steps := by omega
      rw [decKnSeq_succ P B a, List.mem_append]
      by_cases hprev : a (vkn (shapeOf P B) i u) = true
      · exact Or.inl (ih (by omega) hprev)
      · right
        have hcl : ([neg (vkn (shapeOf P B) (i + 1) u), pos (vkn (shapeOf P B) i u)]
            ++ publisherLits (shapeOf P B) P i u)
            ∈ (knSupportClauses (shapeOf P B) P).clauses :=
          mem_knSupport hstep hu (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)
        have h1 := sat_knSupport h _ hcl
        rw [clause_eval_any] at h1
        obtain ⟨l, hl, hle⟩ := h1
        rw [List.mem_append] at hl
        rcases hl with hl | hpub
        · rw [List.mem_cons, List.mem_cons] at hl
          simp only [List.not_mem_nil, or_false] at hl
          rcases hl with h1 | h1
          · rw [h1] at hle; exact absurd hle (by simp [neg_eval, ha])
          · rw [h1] at hle; exact absurd hle (by simp [pos_eval, hprev])
        · -- a publisher literal holds
          obtain ⟨q, c, hq, hc, a', e, he, hl'⟩ | ⟨n, ins, hn, hins, hcon, hev⟩ :=
            publisherLits_cases hstep hu hpub
          · -- a send publisher: the auxiliary records the session, the counter and the value
            subst hl'
            obtain ⟨h1', h2', h3'⟩ := pubAux_holds hstep hq hc hu he h hle
            have hk := decCode_of_evAct hstep h hq h1'
            have hpc := decodePc_of_true (Nat.le_of_lt hstep) hq hc h h2'
            have hu' : u < shVal (shapeOf P B) := by rw [shVal]; omega
            have hlearn : decLearn (shapeOf P B) P a i
                = decXe (shapeOf P B) P a i q e := by
              rw [decLearn_act hstep h hq hk, hpc, he]
            rw [hlearn, decXe_of_true (mem_allExprs_send he) (Nat.le_of_lt hstep) hq h hu' h3']
            rw [hut]
            simp
          · -- a deduction instance concluding in u
            rw [hev] at hle
            have hk := decCode_of_evDed hstep h hn (by simpa using hle)
            have hlearn := decLearn_ded hstep h hn ins hins hk
            have hsome : decLearn (shapeOf P B) P a i = some t := by
              rw [hlearn, hcon, hut]
            rw [hsome]
            simp

