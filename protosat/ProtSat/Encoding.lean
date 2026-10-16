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

/-- The session count of the shape is the number of sessions. -/
theorem nS1_eq : (shapeOf P B).nS1 = P.sessions.length := rfl

/-- The step bound of the shape is the step bound of the bounds. -/
theorem steps_eq : (shapeOf P B).steps = B.steps := rfl

/-- The nonce domain of the shape is the nonce domain of the protocol. -/
theorem D_eq : (shapeOf P B).D = P.nonceDomain := rfl

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
        | some r => exact absurd (Exists.intro r h3) e
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

theorem mem_eval {i q : Nat} {e : Expr} {cl : Clause} (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (he : e ∈ allExprs P)
    (h : cl ∈ evalGate (shapeOf P B) P i q e) :
    cl ∈ (evalClauses (shapeOf P B) P).clauses := by
  unfold evalClauses cnfOf eachStep1 eachSess evalClausesAt
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by show i < B.steps + 1; omega),
    List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq,
      List.mem_flatMap.mpr ⟨e, he, h⟩⟩⟩

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


/-! ### The evaluation correspondence -/

/-- Reading the expression table at its own index returns the expression. -/
theorem eAt_eIdx {e : Expr} (he : e ∈ allExprs P) : eAt P (eIdx P e) = e := by
  unfold eAt
  have h : rget (allExprs P) (eIdx P e) = some e := rget_ixOf (allExprs P) e he
  rw [h]
  simp

/-- A value is admissible exactly when it belongs to the value domain of the universe. -/
theorem admissible_iff_vals {sh : Shape} {v : Val} :
    admissible sh v = true <-> v ∈ vals sh.U := by
  cases v with
  | none => simp [admissible, vals]
  | some t =>
      simp only [admissible, vals, List.mem_cons, List.mem_map]
      rw [contains_mem]
      constructor
      · intro h; exact Or.inr ⟨t, h, rfl⟩
      · rintro (h | ⟨u, hu, hu2⟩)
        · exact absurd h (by simp)
        · have h2 : u = t := Option.some.inj hu2
          subst h2
          exact hu


/-! ### The evaluation correspondence -/

/-- A variable that is an expression of some action has a store slot in the shape. -/
theorem le_maxNat_of_mem {lo : Nat} : ∀ (l : List Nat) (y : Nat), y ∈ l -> y ≤ maxNat l lo := by
  intro l
  induction l with
  | nil => intro y h; cases h
  | cons x xs ih =>
      intro y h
      rw [List.mem_cons] at h
      rcases h with h | h
      · subst h
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih y h) (Nat.le_max_right _ _)

/-- Every variable mentioned by a protocol expression has a store slot in the shape. -/
theorem var_lt_shV {e : Expr} (he : e ∈ allExprs P) {x : Nat} (hx : x ∈ Expr.vars e) :
    x < shV (shapeOf P B) := by
  have hmem : x ∈ (P.roles.flatMap fun r =>
      r.acts.flatMap fun a => a.written ++ a.exprs.flatMap Expr.vars) := by
    rw [allExprs, List.mem_eraseDups] at he
    rcases List.mem_flatMap.mp he with ⟨r, hr, he2⟩
    rcases List.mem_flatMap.mp he2 with ⟨act, hact, he3⟩
    refine List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨act, hact, ?_⟩⟩
    rw [List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨e, he3, hx⟩)
  have hle := le_maxNat_of_mem (lo := 0) _ x hmem
  have h2 : (shapeOf P B).nV1 = maxNat (P.roles.flatMap fun r =>
      r.acts.flatMap fun a => a.written ++ a.exprs.flatMap Expr.vars) 0 := rfl
  show x < (shapeOf P B).nV1 + 1
  rw [h2]
  omega

/-- An expression cannot be both unary and binary. -/
theorem child1_none_of_child2 {e c₁ c₂ : Expr} (h : Expr.child2 e = some (c₁, c₂)) :
    Expr.child1 e = none := by
  cases e with
  | agent A | nonce N | shrk a b | pubk a | privk a | var x => rfl
  | pair a b | encS a b | decS a b => rfl
  | encA m a | hash m | fst m | snd m | decA m a => cases h

/-- The expression list of an action is closed under taking subexpressions. -/
theorem Action.closed_exprs : ∀ (act : Action) (e : Expr), e ∈ act.exprs ->
    ∀ f ∈ e.subexpressions, f ∈ act.exprs := by
  intro act
  cases act with
  | fresh x N | recv x y =>
      intro e h _ _
      simp [Action.exprs] at h
  | send _ x | assign _ x | secret x =>
      intro e h f hf
      simp only [Action.exprs] at h ⊢
      exact Expr.subexpressions_trans x e h f hf
  | check x y | claim _ x y | commit _ x y =>
      intro e h f hf
      simp only [Action.exprs, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (Expr.subexpressions_trans x e h f hf)
      · exact Or.inr (Expr.subexpressions_trans y e h f hf)

/-- The expression table is closed under subexpressions. -/
theorem mem_allExprs_sub {e f : Expr} (he : e ∈ allExprs P) (hf : f ∈ e.subexpressions) :
    f ∈ allExprs P := by
  rw [allExprs, List.mem_eraseDups] at he ⊢
  rcases List.mem_flatMap.mp he with ⟨r, hr, he2⟩
  rcases List.mem_flatMap.mp he2 with ⟨act, hact, he3⟩
  refine List.mem_flatMap.mpr ⟨r, hr,
    List.mem_flatMap.mpr ⟨act, hact, Action.closed_exprs act e he3 f hf⟩⟩

/-- The child of a table expression is again in the table. -/
theorem mem_allExprs_child1 {e c : Expr} (he : e ∈ allExprs P) (h : Expr.child1 e = some c) :
    c ∈ allExprs P := by
  have hsub : c ∈ e.subexpressions := by
    cases e with
    | agent A | nonce N | shrk a b | pubk a | privk a | var x => cases h
    | pair a b | encS a b | decS a b => cases h
    | encA m a | decA m a =>
        have h3 : m = c := Option.some.inj (h : some m = some c)
        subst h3
        rw [Expr.subexpressions]
        exact List.mem_cons.mpr (Or.inr (Expr.mem_subexpressions _))
    | hash m | fst m | snd m =>
        have h3 : m = c := Option.some.inj (h : some m = some c)
        subst h3
        rw [Expr.subexpressions]
        exact List.mem_cons.mpr (Or.inr (Expr.mem_subexpressions _))
  exact mem_allExprs_sub he hsub

/-- Both children of a table expression are again in the table. -/
theorem mem_allExprs_child2 {e c₁ c₂ : Expr} (he : e ∈ allExprs P)
    (h : Expr.child2 e = some (c₁, c₂)) : c₁ ∈ allExprs P ∧ c₂ ∈ allExprs P := by
  have hsub : c₁ ∈ e.subexpressions ∧ c₂ ∈ e.subexpressions := by
    cases e with
    | agent A | nonce N | shrk a b | pubk a | privk a | var x => cases h
    | encA m a | hash m | fst m | snd m | decA m a => cases h
    | pair a b =>
        have h3 : (a, b) = (c₁, c₂) :=
          Option.some.inj (h : some (a, b) = some (c₁, c₂))
        cases h3
        rw [Expr.subexpressions]
        exact ⟨List.mem_cons.mpr (Or.inr (List.mem_append_left _ (Expr.mem_subexpressions _))),
          List.mem_cons.mpr (Or.inr (List.mem_append_right _ (Expr.mem_subexpressions _)))⟩
    | encS a b =>
        have h3 : (a, b) = (c₁, c₂) :=
          Option.some.inj (h : some (a, b) = some (c₁, c₂))
        cases h3
        rw [Expr.subexpressions]
        exact ⟨List.mem_cons.mpr (Or.inr (List.mem_append_left _ (Expr.mem_subexpressions _))),
          List.mem_cons.mpr (Or.inr (List.mem_append_right _ (Expr.mem_subexpressions _)))⟩
    | decS a b =>
        have h3 : (a, b) = (c₁, c₂) :=
          Option.some.inj (h : some (a, b) = some (c₁, c₂))
        cases h3
        rw [Expr.subexpressions]
        exact ⟨List.mem_cons.mpr (Or.inr (List.mem_append_left _ (Expr.mem_subexpressions _))),
          List.mem_cons.mpr (Or.inr (List.mem_append_right _ (Expr.mem_subexpressions _)))⟩
  exact ⟨mem_allExprs_sub he hsub.1, mem_allExprs_sub he hsub.2⟩

/-- The gate clauses of a unary expression. -/
theorem evalGate_unary {sh : Shape} {P : Protocol} {i q : Nat} {e c : Expr}
    (hchild : Expr.child1 e = some c) :
    evalGate sh P i q e =
      (fwdClausesOn [] (xeOh sh i q (eIdx P c))
        (fun u => pos (vxe sh i q (eIdx P e) (f1 sh e u)))).clauses := by
  unfold evalGate
  rw [hchild]

/-- The gate clauses of a binary expression. -/
theorem evalGate_binary {sh : Shape} {P : Protocol} {i q : Nat} {e c₁ c₂ : Expr}
    (hchild : Expr.child2 e = some (c₁, c₂)) :
    evalGate sh P i q e =
      (fwd2ClausesOn [] (xeOh sh i q (eIdx P c₁)) (xeOh sh i q (eIdx P c₂))
        (fun u v => pos (vxe sh i q (eIdx P e) (f2 sh e u v)))).clauses := by
  unfold evalGate
  rw [child1_none_of_child2 hchild, hchild]

/-- The gate clauses of a variable read. -/
theorem evalGate_var {sh : Shape} {P : Protocol} {i q x : Nat} :
    evalGate sh P i q (Expr.var x) =
      (fwdClausesOn [] (stOh sh i q x)
        (fun u => pos (vxe sh i q (eIdx P (Expr.var x)) u))).clauses := by
  unfold evalGate evalLeafGate
  simp [Expr.child1, Expr.child2]

/-- The gate clauses of a constant expression. -/
theorem evalGate_konst {sh : Shape} {P : Protocol} {i q : Nat} {E : Expr}
    (h1 : Expr.child1 E = none) (h2 : Expr.child2 E = none) (hv : ∀ x, E ≠ Expr.var x) :
    evalGate sh P i q E =
      [[pos (vxe sh i q (eIdx P E) (uIdx sh (Expr.constVal E)))]] := by
  unfold evalGate evalLeafGate
  rw [h1, h2]
  cases E with
  | var x => exact absurd rfl (hv x)
  | _ => rfl

/-- The gate clauses of a table expression are satisfied by any satisfying assignment. -/
theorem sat_gate {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    ∀ cl ∈ evalGate (shapeOf P B) P i q e, Clause.eval a cl = true :=
  fun cl hcl => sat_eval h cl (mem_eval hi hq he hcl)

/-- The index selected by an evaluation group is in range. -/
theorem decodeXe_lt {i q : Nat} {e : Expr} (he : e ∈ allExprs P) (hi : i ≤ B.steps)
    (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B)) :
    ∃ v, (xeOh (shapeOf P B) i q (eIdx P e)).decode a = some v ∧ v < shVal (shapeOf P B) ∧
      a (vxe (shapeOf P B) i q (eIdx P e) v) = true := by
  have hix : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hoh := sat_xeOh hi hq hix h
  obtain ⟨v, hv⟩ := Oh.decode_some hoh
  exact ⟨v, hv, List.mem_range.mp ((decodeGo_some _ _ _ _ hv).1),
    (decodeGo_some _ _ _ _ hv).2⟩

/-- **Unary Tseitin gate.**  The value decoded for a unary expression is one evaluation step
applied to the value decoded for its child. -/
theorem xe_unary {e c : Expr} (he : e ∈ allExprs P) (hc : c ∈ allExprs P)
    (hchild : Expr.child1 e = some c)
    (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q e =
      Expr.stepEval1 e (decXe (shapeOf P B) P a i q c) := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt hc hi hq h
  have hixc : eIdx P c < shE (shapeOf P B) := eIdx_lt hc
  have hixe : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have hg : Sat a (fwdClausesOn [] (xeOh (shapeOf P B) i q (eIdx P c))
      (fun u => pos (vxe (shapeOf P B) i q (eIdx P e) (f1 (shapeOf P B) e u)))) := by
    intro cl hcl
    exact sat_gate he hi hq h cl (by rw [evalGate_unary hchild]; exact hcl)
  have h1 := fwdClausesOn_correct (sat_xeOh hi hq hixc h) hg
    (fun l hl => absurd hl (by simp)) v hv
  have h2 : a (vxe (shapeOf P B) i q (eIdx P e)
      (f1 (shapeOf P B) e v)) = true := by simpa using h1
  have h3 : (xeOh (shapeOf P B) i q (eIdx P e)).decode a =
      some (f1 (shapeOf P B) e v) :=
    Oh.decode_of_true (sat_xeOh hi hq hixe h)
      (List.mem_range.mpr (uIdx_lt' (shapeOf P B) _)) h2
  have hval : valAt (shapeOf P B) (f1 (shapeOf P B) e v) =
      Expr.stepEval1 e (valAt (shapeOf P B) v) := by
    show valAt (shapeOf P B) (uIdx (shapeOf P B) (Expr.stepEval1 e (valAt (shapeOf P B) v))) = _
    refine valAt_uIdx_adm ?_
    exact hU.1 e he (valAt (shapeOf P B) v)
      (((admissible_iff_vals (sh := shapeOf P B) (v := valAt (shapeOf P B) v)).mp (admissible_valAt hvlt)))
  have hc' : decXe (shapeOf P B) P a i q c = valAt (shapeOf P B) v := by
    unfold decXe decVal
    rw [hv]
  rw [hc']
  unfold decXe decVal
  rw [h3]
  simpa using hval

/-- **Binary Tseitin gate.** -/
theorem xe_binary {e c₁ c₂ : Expr} (he : e ∈ allExprs P) (hc₁ : c₁ ∈ allExprs P)
    (hc₂ : c₂ ∈ allExprs P) (hchild : Expr.child2 e = some (c₁, c₂))
    (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q e =
      Expr.stepEval2 e (decXe (shapeOf P B) P a i q c₁)
        (decXe (shapeOf P B) P a i q c₂) := by
  obtain ⟨v₁, hv₁, hvl₁, _⟩ := decodeXe_lt hc₁ hi hq h
  obtain ⟨v₂, hv₂, hvl₂, _⟩ := decodeXe_lt hc₂ hi hq h
  have hg : Sat a (fwd2ClausesOn [] (xeOh (shapeOf P B) i q (eIdx P c₁))
      (xeOh (shapeOf P B) i q (eIdx P c₂))
      (fun u v => pos (vxe (shapeOf P B) i q (eIdx P e) (f2 (shapeOf P B) e u v)))) := by
    intro cl hcl
    exact sat_gate he hi hq h cl (by rw [evalGate_binary hchild]; exact hcl)
  have hix1 : eIdx P c₁ < shE (shapeOf P B) := eIdx_lt hc₁
  have hix2 : eIdx P c₂ < shE (shapeOf P B) := eIdx_lt hc₂
  have hixe : eIdx P e < shE (shapeOf P B) := eIdx_lt he
  have h1 := fwd2ClausesOn_correct (sat_xeOh hi hq hix1 h)
    (sat_xeOh hi hq hix2 h) hg (fun l hl => absurd hl (by simp)) v₁ v₂ hv₁ hv₂
  have h2 : a (vxe (shapeOf P B) i q (eIdx P e)
      (f2 (shapeOf P B) e v₁ v₂)) = true := by simpa using h1
  have h3 : (xeOh (shapeOf P B) i q (eIdx P e)).decode a =
      some (f2 (shapeOf P B) e v₁ v₂) :=
    Oh.decode_of_true (sat_xeOh hi hq hixe h) (List.mem_range.mpr (uIdx_lt' (shapeOf P B) _)) h2
  have hval : valAt (shapeOf P B) (f2 (shapeOf P B) e v₁ v₂) =
      Expr.stepEval2 e (valAt (shapeOf P B) v₁) (valAt (shapeOf P B) v₂) := by
    show valAt (shapeOf P B) (uIdx (shapeOf P B)
        (Expr.stepEval2 e (valAt (shapeOf P B) v₁) (valAt (shapeOf P B) v₂))) = _
    refine valAt_uIdx_adm ?_
    exact hU.2.1 e he (valAt (shapeOf P B) v₁)
      (((admissible_iff_vals (sh := shapeOf P B) (v := valAt (shapeOf P B) v₁)).mp (admissible_valAt hvl₁)))
      (valAt (shapeOf P B) v₂)
      (((admissible_iff_vals (sh := shapeOf P B) (v := valAt (shapeOf P B) v₂)).mp (admissible_valAt hvl₂)))
  have h1' : decXe (shapeOf P B) P a i q c₁ = valAt (shapeOf P B) v₁ := by
    unfold decXe decVal; rw [hv₁]
  have h2' : decXe (shapeOf P B) P a i q c₂ = valAt (shapeOf P B) v₂ := by
    unfold decXe decVal; rw [hv₂]
  rw [h1', h2']
  unfold decXe decVal
  rw [h3]
  simpa using hval

/-- **Variable gate.**  The value decoded for a variable read is the store slot. -/
theorem xe_var {x : Nat} (he : Expr.var x ∈ allExprs P) (hx : x < shV (shapeOf P B))
    (h : Sat a (encode P B)) (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q (Expr.var x) = decSt (shapeOf P B) a i q x := by
  obtain ⟨v, hv, hvlt, _⟩ := decodeXe_lt he hi hq h
  have hsat := sat_stOh hi hq hx h
  have hg : Sat a (fwdClausesOn [] (stOh (shapeOf P B) i q x)
      (fun u => pos (vxe (shapeOf P B) i q (eIdx P (Expr.var x)) u))) := by
    intro cl hcl
    exact sat_gate he hi hq h cl (by rw [evalGate_var]; exact hcl)
  obtain ⟨w, hw⟩ := Oh.decode_some hsat
  have h1 := fwdClausesOn_correct hsat hg (fun l hl => absurd hl (by simp)) w hw
  have h2 : a (vxe (shapeOf P B) i q (eIdx P (Expr.var x)) w) = true := by simpa using h1
  have hwlt : w < shVal (shapeOf P B) := by
    show w < shVal (shapeOf P B)
    exact List.mem_range.mp ((decodeGo_some _ _ _ _ hw).1)
  have h3 : (xeOh (shapeOf P B) i q (eIdx P (Expr.var x))).decode a = some w :=
    Oh.decode_of_true (sat_xeOh hi hq (eIdx_lt he) h) (List.mem_range.mpr hwlt) h2
  have h4 : some w = some v := by rw [← h3, ← hv]
  have hwv : w = v := Option.some.inj h4
  subst hwv
  unfold decXe decSt decVal
  rw [hv, hw]

/-- **Constant gate.**  The value decoded for a constant is its message. -/
theorem xe_konst {E : Expr} (he : E ∈ allExprs P) (h1 : Expr.child1 E = none)
    (h2 : Expr.child2 E = none) (hv : ∀ x, E ≠ Expr.var x)
    (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    decXe (shapeOf P B) P a i q E = Expr.constVal E := by
  have hg : Sat a (cnfOf
      [[pos (vxe (shapeOf P B) i q (eIdx P E) (uIdx (shapeOf P B) (Expr.constVal E)))]]) := by
    intro cl hcl
    have hmem : cl ∈ evalGate (shapeOf P B) P i q E := by
      rw [evalGate_konst h1 h2 hv]
      simpa [cnfOf] using hcl
    exact sat_gate he hi hq h cl hmem
  have hcl : Clause.eval a [pos (vxe (shapeOf P B) i q (eIdx P E)
      (uIdx (shapeOf P B) (Expr.constVal E)))] = true := by
    have := hg _ (List.Mem.head _)
    simpa using this
  rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at hcl
  have h2' := hcl
  have h3 : (xeOh (shapeOf P B) i q (eIdx P E)).decode a =
      some (uIdx (shapeOf P B) (Expr.constVal E)) :=
    Oh.decode_of_true (sat_xeOh hi hq (eIdx_lt he) h)
      (List.mem_range.mpr (uIdx_lt' (shapeOf P B) _)) h2'
  unfold decXe decVal
  rw [h3]
  refine valAt_uIdx_adm ?_
  exact hU.2.2 E he

/-- **Evaluation correspondence (specification 8A).**  For every expression of the protocol,
the value decoded from its Tseitin group is exactly the value of the expression in the
decoded store.  This is the lemma that makes the SAT encoding of message construction and
destruction trustworthy. -/
theorem decXe_eq (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B))
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) :
    ∀ e : Expr, e ∈ allExprs P ->
      decXe (shapeOf P B) P a i q e = Expr.eval e (decodeStore (shapeOf P B) a i q) := by
  intro e
  induction e with
  | agent A =>
      intro he
      rw [xe_konst he rfl rfl
        (by intro x; simp [Expr.var]) hU h hi hq]
      simp [Expr.eval, Expr.constVal]
  | nonce N =>
      intro he
      rw [xe_konst he rfl rfl
        (by intro x; simp [Expr.var]) hU h hi hq]
      simp [Expr.eval, Expr.constVal]
  | shrk a b =>
      intro he
      rw [xe_konst he rfl rfl
        (by intro x; simp [Expr.var]) hU h hi hq]
      simp [Expr.eval, Expr.constVal]
  | pubk a =>
      intro he
      rw [xe_konst he rfl rfl
        (by intro x; simp [Expr.var]) hU h hi hq]
      simp [Expr.eval, Expr.constVal]
  | privk a =>
      intro he
      rw [xe_konst he rfl rfl
        (by intro x; simp [Expr.var]) hU h hi hq]
      simp [Expr.eval, Expr.constVal]
  | var x =>
      intro he
      rw [xe_var he (var_lt_shV he (by simp [Expr.vars])) h hi hq]
      exact (readVar_decodeStore (var_lt_shV he (by simp [Expr.vars]))).symm
  | pair a b iha ihb =>
      intro he
      obtain ⟨hca, hcb⟩ := mem_allExprs_child2 he rfl
      rw [Expr.eval_child2 rfl,
        xe_binary he hca hcb rfl hU h hi hq, iha hca, ihb hcb]
  | encS a b iha ihb =>
      intro he
      obtain ⟨hca, hcb⟩ := mem_allExprs_child2 he rfl
      rw [Expr.eval_child2 rfl,
        xe_binary he hca hcb rfl hU h hi hq, iha hca, ihb hcb]
  | decS a b iha ihb =>
      intro he
      obtain ⟨hca, hcb⟩ := mem_allExprs_child2 he rfl
      rw [Expr.eval_child2 rfl,
        xe_binary he hca hcb rfl hU h hi hq, iha hca, ihb hcb]
  | encA a _ iha =>
      intro he
      have hca : a ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [Expr.eval_child1 rfl,
        xe_unary he hca rfl hU h hi hq, iha hca]
  | hash a iha =>
      intro he
      have hca : a ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [Expr.eval_child1 rfl,
        xe_unary he hca rfl hU h hi hq, iha hca]
  | fst a iha =>
      intro he
      have hca : a ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [Expr.eval_child1 rfl,
        xe_unary he hca rfl hU h hi hq, iha hca]
  | snd a iha =>
      intro he
      have hca : a ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [Expr.eval_child1 rfl,
        xe_unary he hca rfl hU h hi hq, iha hca]
  | decA a _ iha =>
      intro he
      have hca : a ∈ allExprs P := mem_allExprs_child1 he rfl
      rw [Expr.eval_child1 rfl,
        xe_unary he hca rfl hU h hi hq, iha hca]

/-! ### Deduction instances are genuine rule applications -/

/-- Two reads of the same universe position agree. -/
theorem valAt_eq {sh : Shape} {p : Nat} {u v : Term} (hu : valAt sh p = some u)
    (hv : valAt sh p = some v) : u = v := Option.some.inj (by rw [← hu, ← hv])

/-- The premises of an instance are known: some message of K sits at each premise index. -/
def instPremises (sh : Shape) (ins : DedInst) (K : List Term) : Prop :=
  ∀ p ∈ ins.prem, ∃ s ∈ K, valAt sh p = some s
/-- **Every universe instance is a genuine one-step deduction.**  This is the lemma that
makes a deduction event in the encoding count as a real ProtSat.Attacker.OneStep step, and
hence as a real transition of ProtSat.Rel (specification 8A).  The proof inspects the
construction of ProtSat.Encode.dedInstsOf: each of its shapes is one of the eleven rules of
specification section 2, and the premise indices were chosen exactly so that the required
messages lie in the universe. -/
theorem dedInst_oneStep {sh : Shape} {u : Nat} {ins : DedInst} (h : ins ∈ dedInstsOf sh u)
    {K : List Term} (hK : instPremises sh ins K) {t : Term}
    (hcon : valAt sh ins.concl = some t) : OneStep K t := by
  unfold dedInstsOf at h
  cases h2 : rget sh.U u with
  | none => rw [h2] at h; simp at h
  | some t' =>
      rw [h2] at h
      have hut : valAt sh u = some t' := h2
      unfold instPremises at hK
      simp only [List.mem_cons, List.mem_append, List.mem_filterMap] at h
      rcases h with h | ⟨a, ha, ham⟩
      · rcases h with h | h
        · -- OneStep.known: the conclusion is itself a premise
          rw [h] at hK hcon
          have ht : t = t' := Option.some.inj (by rw [← hut, hcon])
          subst ht
          obtain ⟨s, hs, hre⟩ := hK u (List.Mem.head _)
          have : s = t := Option.some.inj (by rw [← hre, hut])
          subst this
          exact OneStep.known hs
        · -- the introduction rules, by the shape of the conclusion
          cases t' with
          | agent A =>
              simp at h
              rw [h] at hcon
              have ht : t = Term.agent A := Option.some.inj (by rw [← hut, hcon])
              subst ht
              exact OneStep.agent
          | key k =>
              cases k with
              | pub A =>
                  simp at h
                  rw [h] at hcon
                  have ht : t = Term.key (Key.pub A) :=
                    Option.some.inj (by rw [← hut, hcon])
                  subst ht
                  exact OneStep.pub
              | _ => simp at h
          | pair x y =>
              rcases h5 : tIx sh x with ⟨b₁⟩|⟨b₁⟩
              · simp [h5] at h
              · rcases h6 : tIx sh y with ⟨b₂⟩|⟨b₂⟩
                · simp [h6] at h
                · simp [h5, h6] at h
                  rw [h] at hK hcon
                  have ht : t = Term.pair x y := Option.some.inj (by rw [← hut, hcon])
                  subst ht
                  have hx : valAt sh b₁ = some x := tIx_valAt h5
                  have hy : valAt sh b₂ = some y := tIx_valAt h6
                  obtain ⟨s₁, hs₁, r₁⟩ := hK b₁ (List.Mem.head _)
                  obtain ⟨s₂, hs₂, r₂⟩ := hK b₂ (List.Mem.tail _ (List.Mem.head _))
                  rw [valAt_eq r₁ hx] at hs₁
                  rw [valAt_eq r₂ hy] at hs₂
                  exact OneStep.pairI hs₁ hs₂
          | encS m k =>
              rcases h5 : tIx sh m with ⟨b₁⟩|⟨b₁⟩
              · simp [h5] at h
              · rcases h6 : tIx sh (Term.key k) with ⟨b₂⟩|⟨b₂⟩
                · simp [h6] at h
                · simp [h5, h6] at h
                  rw [h] at hK hcon
                  have ht : t = Term.encS m k := Option.some.inj (by rw [← hut, hcon])
                  subst ht
                  have hx : valAt sh b₁ = some m := tIx_valAt h5
                  have hy : valAt sh b₂ = some (Term.key k) := tIx_valAt h6
                  obtain ⟨s₁, hs₁, r₁⟩ := hK b₁ (List.Mem.head _)
                  obtain ⟨s₂, hs₂, r₂⟩ := hK b₂ (List.Mem.tail _ (List.Mem.head _))
                  rw [valAt_eq r₁ hx] at hs₁
                  rw [valAt_eq r₂ hy] at hs₂
                  exact OneStep.encSI hs₁ hs₂
          | encA m ag =>
              rcases h5 : tIx sh m with ⟨b₁⟩|⟨b₁⟩
              · simp [h5] at h
              · simp [h5] at h
                rw [h] at hK hcon
                have ht : t = Term.encA m ag := Option.some.inj (by rw [← hut, hcon])
                subst ht
                have hx : valAt sh b₁ = some m := tIx_valAt h5
                obtain ⟨s₁, hs₁, r₁⟩ := hK b₁ (List.Mem.head _)
                rw [valAt_eq r₁ hx] at hs₁
                exact OneStep.encAI hs₁
          | hash m =>
              rcases h5 : tIx sh m with ⟨b₁⟩|⟨b₁⟩
              · simp [h5] at h
              · simp [h5] at h
                rw [h] at hK hcon
                have ht : t = Term.hash m := Option.some.inj (by rw [← hut, hcon])
                subst ht
                have hx : valAt sh b₁ = some m := tIx_valAt h5
                obtain ⟨s₁, hs₁, r₁⟩ := hK b₁ (List.Mem.head _)
                rw [valAt_eq r₁ hx] at hs₁
                exact OneStep.hashI hs₁
          | _ => simp at h
      · -- the elimination rules, by the shape of a premise message
        cases a with
        | pair x y =>
            by_cases hxy : x = t'
            · simp at ham
              rw [if_pos hxy] at ham
              simp at ham
              rw [← ham] at hK hcon
              have ht : t = t' := Option.some.inj (by rw [← hut, hcon])
              subst ht
              have hhp : valAt sh (ixOf (Term.pair x y) sh.U) = some (Term.pair x y) :=
                rget_ixOf sh.U (Term.pair x y) ha
              obtain ⟨s₁, hs₁, r₁⟩ := hK (ixOf (Term.pair x y) sh.U) (List.Mem.head _)
              rw [valAt_eq r₁ hhp] at hs₁
              rw [← hxy]
              exact OneStep.fstE hs₁
            · by_cases hxy2 : y = t'
              · simp at ham
                rw [if_neg hxy, if_pos hxy2] at ham
                simp at ham
                rw [← ham] at hK hcon
                have ht : t = t' := Option.some.inj (by rw [← hut, hcon])
                subst ht
                have hhp : valAt sh (ixOf (Term.pair x y) sh.U) = some (Term.pair x y) :=
                  rget_ixOf sh.U (Term.pair x y) ha
                obtain ⟨s₁, hs₁, r₁⟩ := hK (ixOf (Term.pair x y) sh.U) (List.Mem.head _)
                rw [valAt_eq r₁ hhp] at hs₁
                rw [← hxy2]
                exact OneStep.sndE hs₁
              · simp at ham
                rw [if_neg hxy, if_neg hxy2] at ham
                simp at ham
        | encS m k =>
            by_cases hm : m = t'
            · simp at ham
              rcases ham with ⟨h1, ham⟩
              rcases h5 : tIx sh (Term.key k) with ⟨b₂⟩|⟨b₂⟩
              · rw [h5] at ham
                simp at ham
              · simp [h5] at ham
                rw [← ham] at hK hcon
                have ht : t = t' := Option.some.inj (by rw [← hut, hcon])
                subst ht
                have hy : valAt sh b₂ = some (Term.key k) := tIx_valAt h5
                have hhp : valAt sh (ixOf (Term.encS m k) sh.U) = some (Term.encS m k) :=
                  rget_ixOf sh.U (Term.encS m k) ha
                obtain ⟨s₁, hs₁, r₁⟩ := hK (ixOf (Term.encS m k) sh.U) (List.Mem.head _)
                obtain ⟨s₂, hs₂, r₂⟩ := hK b₂ (List.Mem.tail _ (List.Mem.head _))
                rw [valAt_eq r₁ hhp] at hs₁
                rw [valAt_eq r₂ hy] at hs₂
                rw [← hm]
                exact OneStep.encSD hs₁ hs₂
            · simp at ham
              rcases ham with ⟨h1, _⟩
              exact absurd h1 hm
        | encA m ag =>
            by_cases hm : m = t'
            · simp at ham
              rcases ham with ⟨h1, ham⟩
              rcases h5 : tIx sh (Term.key (Key.priv ag)) with ⟨b₂⟩|⟨b₂⟩
              · rw [h5] at ham
                simp at ham
              · simp [h5] at ham
                rw [← ham] at hK hcon
                have ht : t = t' := Option.some.inj (by rw [← hut, hcon])
                subst ht
                have hy : valAt sh b₂ = some (Term.key (Key.priv ag)) := tIx_valAt h5
                have hhp : valAt sh (ixOf (Term.encA m ag) sh.U) = some (Term.encA m ag) :=
                  rget_ixOf sh.U (Term.encA m ag) ha
                obtain ⟨s₁, hs₁, r₁⟩ := hK (ixOf (Term.encA m ag) sh.U) (List.Mem.head _)
                obtain ⟨s₂, hs₂, r₂⟩ := hK b₂ (List.Mem.tail _ (List.Mem.head _))
                rw [valAt_eq r₁ hhp] at hs₁
                rw [valAt_eq r₂ hy] at hs₂
                rw [← hm]
                exact OneStep.encAD hs₁ hs₂
            · simp at ham
              rcases ham with ⟨h1, _⟩
              exact absurd h1 hm
        | _ => simp at ham

/-! ### The decoded run -/

/-- A session store is well formed: its variables are pairwise distinct - the semantics only
ever replaces the value of a variable, it never adds a second binding for one - and each of
its variables is within the bound the shape allocates for the protocol.  This is what makes a
store readable through the decoded one-hot groups: a message is in the store exactly when
some slot reads back as that message, which is what the freshness side condition of
ProtSat.Rel.rFresh needs. -/
def StoreWF (sh : Shape) (s : List (Var × Term)) : Prop :=
  (s.map Prod.fst).Nodup ∧ ∀ p ∈ s, p.1 < shV sh

/-- The configuration C agrees with the assignment a at step i: the program counters, the
variable readings and the attacker's knowledge are exactly the ones the assignment encodes,
the stores are well formed, and there are exactly the sessions the shape instantiates.
This is the bridge between the Boolean world and ProtSat.Operational. -/
def Agrees (P : Protocol) (B : Bounds) (a : Assignment) (C : Cfg) (i : Nat) : Prop :=
  (∀ q, q < (shapeOf P B).nS1 → pcOf C q = decodePc (shapeOf P B) a i q) ∧
  (∀ q x, q < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
      readVar x (storeOf C q) = decSt (shapeOf P B) a i q x) ∧
  C.kn = decKnSeq (shapeOf P B) P a i ∧
  (∀ q, q < (shapeOf P B).nS1 → StoreWF (shapeOf P B) (storeOf C q)) ∧
  C.sess.length = (shapeOf P B).nS1

/-- Whatever a store reads is one of its values. -/
theorem readVar_mem_storeVals {x : Var} {s : List (Var × Term)} {t : Term}
    (h : readVar x s = some t) : t ∈ storeVals s := by
  have key : ∀ (l : List (Var × Term)), Expr.lookup x l = some t -> t ∈ storeVals l := by
    intro l
    induction l with
    | nil => intro h2; simp [Expr.lookup] at h2
    | cons p ps ih =>
        cases p with
        | mk y u =>
            intro h2
            rw [Expr.lookup] at h2
            by_cases hy : y = x
            · subst hy
              rw [if_pos rfl] at h2
              have h3 := Option.some.inj h2
              subst h3
              exact List.Mem.head _
            · rw [if_neg hy] at h2
              exact List.Mem.tail _ (ih h2)
  exact key s h

/-- Whatever a store reads back as some t was put in the store as a pair. -/
theorem mem_of_readVar {x : Var} {s : List (Var × Term)} {t : Term}
    (h : readVar x s = some t) : (x, t) ∈ s := by
  have key : ∀ (l : List (Var × Term)), Expr.lookup x l = some t -> (x, t) ∈ l := by
    intro l
    induction l with
    | nil => intro h2; simp [Expr.lookup] at h2
    | cons p ps ih =>
        cases p with
        | mk y u =>
            intro h2
            rw [Expr.lookup] at h2
            by_cases hy : y = x
            · subst hy
              rw [if_pos rfl] at h2
              have h3 := Option.some.inj h2
              subst h3
              exact List.Mem.head _
            · rw [if_neg hy] at h2
              exact List.Mem.tail _ (ih h2)
  exact key s h

/-- In a store whose variables are distinct, reading the variable of a stored pair returns
that pair's value. -/
theorem readVar_of_mem {x : Var} {t : Term} {s : List (Var × Term)}
    (h : (x, t) ∈ s) (hd : (s.map Prod.fst).Nodup) : readVar x s = some t := by
  induction s with
  | nil => cases h
  | cons p ps ih =>
      cases p with
      | mk y u =>
        rw [List.map_cons, List.nodup_cons] at hd
        show Expr.lookup x ((y, u) :: ps) = some t
        rw [Expr.lookup]
        by_cases hy : y = x
        · subst hy
          rw [if_pos rfl]
          rcases List.mem_cons.mp h with h1 | h1
          · exact congrArg some ((congrArg Prod.snd h1).symm)
          · exact absurd (List.mem_map.mpr ⟨(y, t), h1, rfl⟩) hd.1
        · rw [if_neg hy]
          rcases List.mem_cons.mp h with h1 | h2
          · exact absurd h1 (by simp_all)
          · exact ih h2 hd.2

/-- Replacing a variable's value keeps a store well formed. -/
theorem storeWF_writeVar (sh : Shape) {x : Var} {t : Term} (hx : x < shV sh)
    {s : List (Var × Term)} (hw : StoreWF sh s) : StoreWF sh (writeVar x t s) := by
  unfold StoreWF at hw ⊢
  obtain ⟨hd, hb⟩ := hw
  rw [writeVar]
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hx => ?_,
      List.Nodup.sublist (List.Sublist.map Prod.fst
        (List.filter_sublist (p := fun q : Var × Term => q.1 != x))) hd⟩
    rw [List.mem_map] at hx
    obtain ⟨p, hp, hpe⟩ := hx
    rw [List.mem_filter] at hp
    exact absurd hp.2 (by simpa using hpe)
  · intro q hq
    rw [List.mem_cons] at hq
    rcases hq with hq | hq
    · subst hq; exact hx
    · rw [List.mem_filter] at hq
      exact hb q hq.1

/-- The decoded store of a well formed configuration reads back through the slots: a message
is in the store exactly when some decoded slot holds it. -/
theorem Agrees.storeVals_iff (hag : Agrees P B a C i) (hq : q < (shapeOf P B).nS1) (t : Term) :
    t ∈ storeVals (storeOf C q) <->
      ∃ x, x < (shapeOf P B).nV1 + 1 ∧ decSt (shapeOf P B) a i q x = some t := by
  obtain ⟨hpc_ag, hst_ag, hkn_eq, hwf, hlen⟩ := hag
  constructor
  · intro htm
    unfold storeVals at htm
    rw [List.mem_map] at htm
    obtain ⟨⟨x, u⟩, hp, hut⟩ := htm
    have hx : x < (shapeOf P B).nV1 + 1 := (hwf q hq).2 _ hp
    have hu : u = t := hut
    subst hu
    refine ⟨x, hx, ?_⟩
    rw [← hst_ag q x hq hx]
    exact readVar_of_mem hp (hwf q hq).1
  · rintro ⟨x, hx, he⟩
    unfold storeVals
    rw [List.mem_map]
    have h1 : readVar x (storeOf C q) = some t := (hst_ag q x hq hx).trans he
    exact ⟨(x, t), mem_of_readVar h1, rfl⟩

/-- The successor of C prescribed by the event the assignment selects at step i: the same
function ProtSat.Rel computes, read off the decoded event.  The step clauses guarantee that
the step is enabled (ProtSat.Encoding.rel_agrees). -/
def decStep (P : Protocol) (B : Bounds) (a : Assignment) (C : Cfg) (i : Nat) : Cfg :=
  match decEv (shapeOf P B) P a i with
  | Ev.idle => C
  | Ev.ded t => succDed C t
  | Ev.act q m d =>
      match P.actionAt q (pcOf C q) with
      | some (Action.fresh x _) => succStore C q x (Term.nonce d)
      | some (Action.send _ e) =>
          match Expr.eval e (storeOf C q) with
          | some t => succSend C q t
          | none => C
      | some (Action.recv _ x) => succStore C q x m
      | some (Action.assign x e) =>
          match Expr.eval e (storeOf C q) with
          | some t => succStore C q x t
          | none => C
      | _ => succAdvance C q

/-- The run decoded from the assignment: the initial configuration, then one application of
decStep per step. -/
def decRun (P : Protocol) (B : Bounds) (a : Assignment) : Nat → Cfg
  | 0 => initCfg P
  | i + 1 => decStep P B a (decRun P B a i) i

/-- Reading a mapped list at an index. -/
theorem rget_map {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    rget (l.map f) i = (rget l i).map f := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons x xs ih => intro i; cases i <;> simp [rget, ih]

/-- The stride of sessions exceeds the session count. -/
theorem lt_shS {sh : Shape} {q : Nat} (h : q < sh.nS1) : q < shS sh := by
  show q < sh.nS1 + 1
  omega

/-- The stride of store slots exceeds the slot count. -/
theorem lt_shV {sh : Shape} {x : Nat} (h : x < sh.nV1) : x < shV sh := by
  show x < sh.nV1 + 1
  omega

/-- Every universe position, and the unset position, is inside the value stride. -/
theorem lt_shVal {sh : Shape} {u : Nat} (h : u ≤ sh.U.length) : u < shVal sh := by
  show u < sh.U.length + 1
  omega

/-- At step 0 every store slot is unset: the initial clauses pin each slot to the "unset"
value. -/
theorem decSt_zero_none (h : Sat a (encode P B)) (hq : q < (shapeOf P B).nS1)
    (hx : x < (shapeOf P B).nV1 + 1) :
    decSt (shapeOf P B) a 0 q x = none := by
  have h1 : a (vst (shapeOf P B) 0 q x ((shapeOf P B).U.length)) = true := by
    have hcl : [pos (vst (shapeOf P B) 0 q x ((shapeOf P B).U.length))] ∈
        (initClauses (shapeOf P B) P).clauses := by
      unfold initClauses cnfOf
      refine List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (lt_shS hq),
          List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
            List.mem_map.mpr ⟨(shapeOf P B).U.length,
              List.mem_range.mpr (lt_shVal (Nat.le_refl _)), by simp⟩⟩⟩))
    have := sat_init h _ hcl
    rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at this
    exact this
  have hoh := sat_stOh (Nat.zero_le _) (lt_shS hq) hx h
  have h2 : (stOh (shapeOf P B) 0 q x).decode a = some ((shapeOf P B).U.length) :=
    Oh.decode_of_true hoh (List.mem_range.mpr (lt_shVal (Nat.le_refl _))) h1
  unfold decSt decVal
  rw [h2]
  exact valAt_uIdx_none (shapeOf P B)

/-- The initial configuration agrees with the assignment at step 0: the initial clauses say
exactly that every session is at program counter 0 with an empty store and the attacker
holds the initial knowledge. -/
theorem agrees_zero (h : Sat a (encode P B)) : Agrees P B a (initCfg P) 0 := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro q hq
    have h1 : a (vpc (shapeOf P B) 0 q 0) = true := by
      have hcl : [pos (vpc (shapeOf P B) 0 q 0)] ∈
          (initClauses (shapeOf P B) P).clauses := by
        unfold initClauses cnfOf
        refine List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (lt_shS hq),
            List.mem_map.mpr ⟨0, List.mem_range.mpr (shPc_pos _), rfl⟩⟩))
      have := sat_init h _ hcl
      rw [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] at this
      exact this
    have h2 : decodePc (shapeOf P B) a 0 q = 0 :=
      decodePc_of_true (Nat.zero_le _) (lt_shS hq) (shPc_pos _) h h1
    have h1' : sessAt (initCfg P) q = some { pc := 0, store := [] } := by
      unfold ProtSat.initCfg ProtSat.sessAt
      rw [rget_map]
      have hl : q < P.sessions.length := by rw [← nS1_eq]; exact hq
      cases h3 : rget P.sessions q with
      | none =>
          obtain ⟨s, hs⟩ := rget_lt P.sessions q hl
          rw [h3] at hs
          exact absurd hs (by simp)
      | some s => rfl
    have hpc : pcOf (initCfg P) q = 0 := by
      show ((sessAt (initCfg P) q).map (fun s => s.pc)).getD 0 = 0
      rw [h1']
      rfl
    rw [hpc, h2]
  · intro q x hq hx
    have hdec : decSt (shapeOf P B) a 0 q x = none := decSt_zero_none h hq hx
    have h1'' : sessAt (initCfg P) q = some { pc := 0, store := [] } := by
      unfold ProtSat.initCfg ProtSat.sessAt
      rw [rget_map]
      have hl : q < P.sessions.length := by rw [← nS1_eq]; exact hq
      cases h3 : rget P.sessions q with
      | none =>
          obtain ⟨s, hs⟩ := rget_lt P.sessions q hl
          rw [h3] at hs
          exact absurd hs (by simp)
      | some s => rfl
    have hst : storeOf (initCfg P) q = [] := by
      show ((sessAt (initCfg P) q).map (fun s => s.store)).getD [] = []
      rw [h1'']
      rfl
    rw [hst, hdec]
    rfl
  · intro q hq
    have hst2 : storeOf (initCfg P) q = [] := by
      have h1 : sessAt (initCfg P) q = some { pc := 0, store := [] } := by
        unfold ProtSat.initCfg ProtSat.sessAt
        rw [rget_map]
        have hl : q < P.sessions.length := by rw [← nS1_eq]; exact hq
        cases h3 : rget P.sessions q with
        | none =>
            obtain ⟨s, hs⟩ := rget_lt P.sessions q hl
            rw [h3] at hs
            exact absurd hs (by simp)
        | some s => rfl
      show ((sessAt (initCfg P) q).map (fun s => s.store)).getD [] = []
      rw [h1]
      rfl
    rw [hst2]
    exact ⟨List.nodup_nil, by simp⟩
  · have h1 : (initCfg P).sess = P.sessions.map fun s => { pc := 0, store := [] } := rfl
    rw [h1, List.length_map, nS1_eq]

/-- The index a store group selects, with its variable true. -/
theorem decodeSt_val (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (encode P B)) :
    ∃ v, (stOh (shapeOf P B) i q x).decode a = some v ∧ v < shVal (shapeOf P B) ∧
      a (vst (shapeOf P B) i q x v) = true := by
  have hoh := sat_stOh hi hq hx h
  obtain ⟨v, hv⟩ := Oh.decode_some hoh
  exact ⟨v, hv, List.mem_range.mp ((decodeGo_some _ _ _ _ hv).1),
    (decodeGo_some _ _ _ _ hv).2⟩

/-- A session that does not act keeps its program counter. -/
theorem decodePc_frame (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (encode P B)) (ha : a (evAct (shapeOf P B) i q) = false) :
    decodePc (shapeOf P B) a (i + 1) q = decodePc (shapeOf P B) a i q := by
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true :=
    decodePc_true (Nat.le_of_lt hi) hq h
  have hcl : [pos (evAct (shapeOf P B) i q), neg (vpc (shapeOf P B) i q c),
      pos (vpc (shapeOf P B) (i + 1) q c)] ∈ frameSessClauses (shapeOf P B) i q := by
    unfold frameSessClauses
    refine List.mem_append_left _ (List.mem_map.mpr ⟨c,
      List.mem_range.mpr (decodePc_lt (Nat.le_of_lt hi) hq h), rfl⟩)
  have h1 := frame_holds hi hq h ha _ hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, pos_eval, neg_eval] at h1
  rw [ha, Bool.false_or, hpc, Bool.not_true, Bool.false_or] at h1
  exact decodePc_of_true (Nat.succ_le_of_lt hi) hq (decodePc_lt (Nat.le_of_lt hi) hq h) h h1

/-- A session that does not act keeps every store slot. -/
theorem decSt_frame (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (encode P B))
    (ha : a (evAct (shapeOf P B) i q) = false) :
    decSt (shapeOf P B) a (i + 1) q x = decSt (shapeOf P B) a i q x := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeSt_val (Nat.le_of_lt hi) hq hx h
  have hcl : [pos (evAct (shapeOf P B) i q), neg (vst (shapeOf P B) i q x v),
      pos (vst (shapeOf P B) (i + 1) q x v)] ∈ frameSessClauses (shapeOf P B) i q := by
    unfold frameSessClauses
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx,
      List.mem_map.mpr ⟨v, List.mem_range.mpr (lt_shVal (Nat.le_of_lt_succ hvlt)), rfl⟩⟩)
  have h1 := frame_holds hi hq h ha _ hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, pos_eval, neg_eval] at h1
  rw [ha, Bool.false_or, hvv, Bool.not_true, Bool.false_or] at h1
  have h2 : (stOh (shapeOf P B) (i + 1) q x).decode a = some v :=
    Oh.decode_of_true (sat_stOh (Nat.succ_le_of_lt hi) hq hx h)
      (List.mem_range.mpr hvlt) h1
  unfold decSt decVal
  rw [h2, hv]

/-! ### One decoded step is a real transition -/

/-- When no session acts and the step teaches the attacker nothing, the agreement carries
over from step i to step i+1: this is precisely the content of the frame clauses. -/
theorem agrees_of_noact (h : Sat a (encode P B)) {i : Nat} (hi : i < B.steps)
    (hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false)
    {C : Cfg} (hag : Agrees P B a C i)
    (hlearn : decLearn (shapeOf P B) P a i = none) :
    Agrees P B a C (i + 1) := by
  obtain ⟨hpc_ag, hst_ag, hkn_eq, hwf, hlen⟩ := hag
  refine ⟨?_, ?_, ?_, hwf, hlen⟩
  · intro q hq
    rw [decodePc_frame hi (lt_shS hq) h (hno q hq), hpc_ag q hq]
  · intro q x hq hx
    rw [decSt_frame hi (lt_shS hq) hx h (hno q hq), hst_ag q x hq hx]
  · rw [decKnSeq_succ, hlearn]
    simp [hkn_eq]

/-- A session that acts is one of the instantiated sessions: the step clauses of a slot
with no action there forbid the event. -/
theorem lt_nS1_of_evAct (hi : i < B.steps) (h : Sat a (encode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    q < (shapeOf P B).nS1 := by
  by_contra e
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true :=
    decodePc_true (Nat.le_of_lt hi) hq h
  have hact : P.actionAt q c = none := by
    unfold Protocol.actionAt Protocol.roleAt
    have hn : (shapeOf P B).nS1 = P.sessions.length := nS1_eq
    have h2 : P.sessions.drop q = [] := List.drop_eq_nil_of_le (by omega)
    rw [h2]
    simp
  have hcl : actGuard (shapeOf P B) i q c ∈ stepClausesAt (shapeOf P B) P i q c := by
    rw [stepClausesAt, hact]
    exact List.Mem.head _
  have h1 := step_body hi hq (decodePc_lt (Nat.le_of_lt hi) hq h) h ha hpc hcl
  rw [clause_eval_nil] at h1
  exact absurd h1 (by simp)

/-- The event of a step in which session q acts. -/
theorem decEv_act_of_code (hi : i < B.steps) (h : Sat a (encode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) :
    decEv (shapeOf P B) P a i =
      Ev.act q (decDeliver (shapeOf P B) a i q) (decNonce (shapeOf P B) a i q) := by
  rw [decEv_code hi h, hk]
  rw [if_neg (by omega : 1 + q ≠ 0), dif_pos (by omega : 1 + q < 1 + shS (shapeOf P B))]
  simp

/-- The step teaches nothing unless a session sends or the attacker deduces. -/
theorem decLearn_none_of_not_send (hi : i < B.steps) (h : Sat a (encode P B)) {q : Nat}
    (hq : q < shS (shapeOf P B)) (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = act)
    (hns : ∀ (a' : Agent) (e : Expr), act ≠ Action.send a' e) :
    decLearn (shapeOf P B) P a i = none := by
  rw [decLearn_act hi h hq hk, hact]
  cases act with
  | send a' e => exact absurd rfl (hns a' e)
  | _ => rfl

/-! ### Consequences of the step clauses -/

/-- An acting session has an action at its program counter: the step clauses of a position
with no action forbid the event. -/
theorem some_actionAt_of_evAct (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (encode P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    P.actionAt q (decodePc (shapeOf P B) a i q) ≠ none := by
  set c := decodePc (shapeOf P B) a i q with hc
  intro hact
  have hpc : a (vpc (shapeOf P B) i q c) = true := decodePc_true (Nat.le_of_lt hi) hq h
  have hcl : actGuard (shapeOf P B) i q c ∈ stepClausesAt (shapeOf P B) P i q c := by
    rw [stepClausesAt, hact]
    exact List.Mem.head _
  have h1 := step_body hi hq (decodePc_lt (Nat.le_of_lt hi) hq h) h ha hpc hcl
  rw [clause_eval_nil] at h1
  exact absurd h1 (by simp)

/-- A program counter with an action there is inside the role. -/
theorem lt_roleLen_of_actionAt {q c : Nat} (h : P.actionAt q c ≠ none) : c < P.roleLen q := by
  have h1 : ((P.roleAt q).map (fun r => (r.acts.drop c).head?)).getD none ≠ none := h
  have h2 : ∃ r, P.roleAt q = some r := by
    by_contra e
    push Not at e
    have : P.roleAt q = none := by
      cases h3 : P.roleAt q with
      | none => rfl
      | some r => exact absurd h3 (e r)
    rw [this] at h1
    simp at h1
  obtain ⟨r, hr⟩ := h2
  have h4 : (r.acts.drop c).head? ≠ none := by
    have h3 : ((P.roleAt q).map (fun r' => (r'.acts.drop c).head?)).getD none =
        (r.acts.drop c).head? := by rw [hr]; rfl
    rw [← h3]
    exact h1
  have h5 : r.acts.drop c ≠ [] := by
    intro h6
    rw [h6] at h4
    exact h4 (by simp)
  have h7 : P.roleLen q = r.acts.length := by
    unfold Protocol.roleLen
    rw [hr]
  rw [h7]
  cases h6 : r.acts.drop c with
  | nil => exact absurd h6 h5
  | cons x xs =>
      have h8 : (r.acts.drop c).length = xs.length + 1 := by rw [h6]; simp
      have h9 : (r.acts.drop c).length = r.acts.length - c := by rw [List.length_drop]
      omega

/-- The role length of an instantiated session is within the shape's program-counter bound.
-/
theorem roleLen_le_nPc1 {q : Nat} (hq : q < (shapeOf P B).nS1) :
    P.roleLen q ≤ (shapeOf P B).nPc1 := by
  have h1 : P.roleLen q ∈ ((List.range (shapeOf P B).nS1).map fun q' => P.roleLen q') :=
    List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  show P.roleLen q ≤ maxNat ((List.range (shapeOf P B).nS1).map fun q' => P.roleLen q') 0
  exact le_maxNat_of_mem _ _ h1

/-- A real program counter, advanced by one, is still inside the program-counter stride. -/
theorem lt_shPc_succ {q c : Nat} (h1 : c < P.roleLen q)
    (h2 : P.roleLen q ≤ (shapeOf P B).nPc1) : c + 1 < shPc (shapeOf P B) := by
  show c + 1 < (shapeOf P B).nPc1 + 1
  omega

/-- An acting session advances its program counter by exactly one. -/
theorem step_pc_succ (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (encode P B)) (ha : a (evAct (shapeOf P B) i q) = true) :
    decodePc (shapeOf P B) a (i + 1) q = decodePc (shapeOf P B) a i q + 1 := by
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true := decodePc_true (Nat.le_of_lt hi) hq h
  have hq1 : q < (shapeOf P B).nS1 := lt_nS1_of_evAct hi h hq ha
  have hne : P.actionAt q c ≠ none := some_actionAt_of_evAct hi hq h ha
  have hcl : advClause (shapeOf P B) i q c ∈ stepClausesAt (shapeOf P B) P i q c :=
    advClause_mem_stepClausesAt (shapeOf P B) P i q c hne
  have h1 := step_body hi hq (decodePc_lt (Nat.le_of_lt hi) hq h) h ha hpc hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, pos_eval,
    ha, hpc, Bool.not_true, Bool.false_or] at h1
  exact decodePc_of_true (Nat.succ_le_of_lt hi) hq
    (lt_shPc_succ (lt_roleLen_of_actionAt hne) (roleLen_le_nPc1 hq1)) h h1

/-- An acting session keeps every store slot whose variable its action does not write. -/
theorem step_st_keep (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hy : y < shV (shapeOf P B)) (h : Sat a (encode P B))
    (ha : a (evAct (shapeOf P B) i q) = true)
    {act : Action} (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hny : writtenVar act ≠ some y) :
    decSt (shapeOf P B) a (i + 1) q y = decSt (shapeOf P B) a i q y := by
  set c := decodePc (shapeOf P B) a i q with hc
  have hpc : a (vpc (shapeOf P B) i q c) = true := decodePc_true (Nat.le_of_lt hi) hq h
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeSt_val (Nat.le_of_lt hi) hq hy h
  have hcl : keepClause (shapeOf P B) i q c y v ∈ stepClausesAt (shapeOf P B) P i q c :=
    keepClause_mem_stepClausesAt (shapeOf P B) P i q c y v hact hny hy hvlt
  have h1 := step_body hi hq (decodePc_lt (Nat.le_of_lt hi) hq h) h ha hpc hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval,
    pos_eval, hvv] at h1
  have hoh := sat_stOh (Nat.succ_le_of_lt hi) hq hy h
  have h2 : (stOh (shapeOf P B) (i + 1) q y).decode a = some v :=
    Oh.decode_of_true hoh (List.mem_range.mpr hvlt) h1
  unfold decSt decVal
  rw [h2, hv]

/-! ### From decoded values back to variables

The forward correspondences (decSt, decXe) read a one-hot group and return the value it
selects.  The lemmas in this section go the other way: if a decoded value is a universe
message then the variable that names that message is true.  They are what turn a Boolean
fact extracted from a clause into a fact about the decoded configuration. -/

/-- The value number selected by a store group: if the group decodes to a universe message
then the variable naming that message is true. -/
theorem decSt_some_vst {i q x : Nat} {t : Term} (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B))
    (hx : x < shV (shapeOf P B)) (h : Sat a (encode P B)) (hut : t ∈ (shapeOf P B).U)
    (hst : decSt (shapeOf P B) a i q x = some t) :
    a (vst (shapeOf P B) i q x (uIdx (shapeOf P B) (some t))) = true := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeSt_val hi hq hx h
  have huv : v = uIdx (shapeOf P B) (some t) := by
    have hv' : valAt (shapeOf P B) v = some t := by
      unfold decSt decVal at hst
      rw [hv] at hst
      exact hst
    have hlt : v < (shapeOf P B).U.length := by
      by_contra e
      have h2 : valAt (shapeOf P B) v = none := rget_oob_ge (shapeOf P B).U v (by omega)
      rw [h2] at hv'; simp at hv'
    exact valAt_inj hlt (uIdx_lt_of_mem hut)
      (by rw [hv', valAt_uIdx_some (shapeOf P B) hut])
  rw [← huv]
  exact hvv

/-- The value number selected by an evaluation group: the same fact for the Tseitin
evaluation groups. -/
theorem decXe_some_vxe {i q : Nat} {e : Expr} {t : Term} (he : e ∈ allExprs P)
    (hi : i ≤ B.steps) (hq : q < shS (shapeOf P B)) (h : Sat a (encode P B))
    (hut : t ∈ (shapeOf P B).U) (hxe : decXe (shapeOf P B) P a i q e = some t) :
    a (vxe (shapeOf P B) i q (eIdx P e) (uIdx (shapeOf P B) (some t))) = true := by
  obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt he hi hq h
  have huv : v = uIdx (shapeOf P B) (some t) := by
    have hv' : valAt (shapeOf P B) v = some t := by
      unfold decXe decVal at hxe
      rw [hv] at hxe
      exact hxe
    have hlt : v < (shapeOf P B).U.length := by
      by_contra e2
      have h2 : valAt (shapeOf P B) v = none := rget_oob_ge (shapeOf P B).U v (by omega)
      rw [h2] at hv'; simp at hv'
    exact valAt_inj hlt (uIdx_lt_of_mem hut)
      (by rw [hv', valAt_uIdx_some (shapeOf P B) hut])
  rw [← huv]
  exact hvv

/-! ### Knowledge completeness

ProtSat.Encoding.kn_sound says a true kn variable is justified by a real event.  The
converse is needed for the freshness side condition of ProtSat.Rel.rFresh, which is stated
negatively ("the nonce is not in anyone's store and not known"): the clauses forbid a kn
variable, and we must conclude that the message is absent from the decoded knowledge. -/

/-- Every message of the initial knowledge has its kn variable true at step 0: the initial
clauses give the attacker exactly ProtSat.Protocol.initKn, not less. -/
theorem init_kn_complete {u : Nat} {t : Term} (hut : valAt (shapeOf P B) u = some t)
    (h : Sat a (encode P B)) (ht : t ∈ P.initKn) :
    a (vkn (shapeOf P B) 0 u) = true := by
  have hu : u < (shapeOf P B).U.length := by
    by_contra e
    have : valAt (shapeOf P B) u = none := rget_oob_ge (shapeOf P B).U u (by omega)
    rw [this] at hut; simp at hut
  have hcl : [pos (vkn (shapeOf P B) 0 u)] ∈ (initClauses (shapeOf P B) P).clauses := by
    unfold initClauses cnfOf
    refine List.mem_append_right _ ?_
    unfold initKnClauses
    refine List.mem_map.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
    have hh : initKnHolds (shapeOf P B) P u = true := by
      unfold initKnHolds; rw [hut]; exact decide_eq_true ht
    rw [if_pos hh]
  have := sat_init h _ hcl
  simpa [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, pos_eval] using this

/-- The frame clauses make knowledge monotone on the Boolean side. -/
theorem kn_frame {i u : Nat} (hi : i < B.steps) (h : Sat a (encode P B))
    (hu : u < (shapeOf P B).U.length) :
    a (vkn (shapeOf P B) i u) = true -> a (vkn (shapeOf P B) (i + 1) u) = true := by
  intro ha
  have hcl : [neg (vkn (shapeOf P B) i u), pos (vkn (shapeOf P B) (i + 1) u)] ∈
      (frameClauses (shapeOf P B)).clauses := by
    unfold frameClauses cnfOf
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_append_left _ (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)⟩
  have := sat_frame h _ hcl
  simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, ha, Bool.not_true,
    pos_eval] at this
  exact this

/-! ### What a step publishes -/

/-- When session q acts with program counter c, the send-publish clause of the action's
expression forces the kn variable of the sent value at the next step: a send really
publishes what it sends. -/
theorem sendPublish_mem {i q c u : Nat} (hu : u < (shapeOf P B).U.length)
    {a' : Agent} {e : Expr} (hact : P.actionAt q c = some (Action.send a' e)) :
    sendPublishClause (shapeOf P B) i q c (eIdx P e) u ∈
      stepClausesAt (shapeOf P B) P i q c := by
  rw [stepClausesAt, hact]
  refine List.mem_append_right _ ?_
  have hred : actionClauses (shapeOf P B) P i q c (Action.send a' e) =
      [sendRealClause (shapeOf P B) i q c (eIdx P e)]
        ++ mapMsg (shapeOf P B)
            (fun w => sendPublishClause (shapeOf P B) i q c (eIdx P e) w) := by
    simp [actionClauses]
  rw [hred, mapMsg]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)

/-- The clause concluding a deduction instance is one of its ded clauses: if the instance
fires then its conclusion is known at the next step. -/
theorem dedConcl_mem {i n : Nat} (hn : n < nInst (shapeOf P B)) (ins : DedInst)
    (hins : instAt (shapeOf P B) n = some ins) :
    [neg (evDed (shapeOf P B) i n), pos (vkn (shapeOf P B) (i + 1) ins.concl)] ∈
      dedClausesAt (shapeOf P B) i n := by
  rw [dedClausesAt, hins]
  exact List.mem_append_right _ (List.Mem.head _)

/-- **A taught message is known.**  Whatever the step teaches the attacker - the conclusion
of a firing deduction instance, or the value a session sends - has its kn variable true at
the next step. -/
theorem decLearn_kn (hi : i < B.steps) (h : Sat a (encode P B)) {u : Nat} {t : Term}
    (hu : u < (shapeOf P B).U.length) (hut : valAt (shapeOf P B) u = some t)
    (hl : decLearn (shapeOf P B) P a i = some t) :
    a (vkn (shapeOf P B) (i + 1) u) = true := by
  rcases ev_cases hi h with h0 | ⟨q, hq, hk⟩ | ⟨n, hn, hk⟩
  · rw [decLearn_code hi h, h0] at hl
    exact absurd hl (by simp)
  · have hev : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
    have hc : decodePc (shapeOf P B) a i q < shPc (shapeOf P B) :=
      decodePc_lt (Nat.le_of_lt hi) hq h
    rw [decLearn_act hi h hq hk] at hl
    cases hact : P.actionAt q (decodePc (shapeOf P B) a i q) with
    | none => exact absurd hl (by simp [hact])
    | some act =>
        cases act with
        | send a' e =>
            have hxe : decXe (shapeOf P B) P a i q e = some t := by simpa [hact] using hl
            have hut' : t ∈ (shapeOf P B).U := rget_mem (shapeOf P B).U u t hu hut
            have hui : uIdx (shapeOf P B) (some t) = u := by
              rw [← hut]; exact uIdx_valAt hu
            have hvxe : a (vxe (shapeOf P B) i q (eIdx P e) u) = true := by
              rw [← hui]
              exact decXe_some_vxe (mem_allExprs_send hact) (Nat.le_of_lt hi) hq h hut' hxe
            have hcl : sendPublishClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q)
                (eIdx P e) u ∈ stepClausesAt (shapeOf P B) P i q
                  (decodePc (shapeOf P B) a i q) := sendPublish_mem hu hact
            have h1 := step_body hi hq hc h hev (decodePc_true (Nat.le_of_lt hi) hq h) hcl
            simpa [sendPublishClause, Clause.eval_cons, clause_eval_nil, Bool.or_false,
              neg_eval, hvxe, Bool.not_true, pos_eval] using h1
        | _ => exact absurd hl (by simp [hact])
  · obtain ⟨ins, hins⟩ := rget_lt (dedInsts (shapeOf P B)) n hn
    rw [decLearn_ded hi h hn ins hins hk] at hl
    have hlt : ins.concl < (shapeOf P B).U.length := by
      by_contra e
      have h2 : valAt (shapeOf P B) ins.concl = none :=
        rget_oob_ge (shapeOf P B).U ins.concl (by omega)
      rw [h2] at hl; simp at hl
    have hcu : ins.concl = u := valAt_inj hlt hu (by rw [hl, ← hut])
    have hcl : [neg (evDed (shapeOf P B) i n), pos (vkn (shapeOf P B) (i + 1) ins.concl)] ∈
        dedClausesAt (shapeOf P B) i n := dedConcl_mem hn ins hins
    have this := sat_ded h _ (mem_ded hi hn hcl)
    rw [hcu] at this
    have hev : a (evDed (shapeOf P B) i n) = true := by
      have : a (vev (shapeOf P B) i (decCode P B a i)) = true := decCode_true hi h
      rw [hk] at this
      exact this
    simpa [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hev,
      Bool.not_true, pos_eval] using this

/-- **Knowledge completeness** (the second half of the knowledge correspondence announced as
decKn_corr in the module header).  A message of the decoded knowledge list has its kn
variable true.  Together with kn_sound this makes the decoded knowledge *exactly* the set of
messages whose kn variable is true, which is what the negative side conditions of the
operational rules (freshness) need. -/
theorem kn_complete (h : Sat a (encode P B)) {u : Nat} {t : Term}
    (hu : u < (shapeOf P B).U.length) (hut : valAt (shapeOf P B) u = some t) :
    ∀ (i : Nat), i ≤ B.steps ->
      t ∈ decKnSeq (shapeOf P B) P a i -> a (vkn (shapeOf P B) i u) = true := by
  intro i
  induction i with
  | zero => intro _ hi; exact init_kn_complete hut h hi
  | succ i ih =>
      intro hi hm
      rw [decKnSeq_succ, List.mem_append] at hm
      rcases hm with hm | hm
      · exact kn_frame hi h hu (ih (by omega) hm)
      · have hl : decLearn (shapeOf P B) P a i = some t := by
          cases h2 : decLearn (shapeOf P B) P a i with
          | none => exact absurd hm (by simp [h2])
          | some s =>
              rw [h2] at hm
              have h3 : t = s := by simpa using hm
              exact congrArg some h3.symm
        exact decLearn_kn (by omega) h hu hut hl

/-! ### The frame facts of an acting step

The lemmas in this section are the propositional shadow of the successor definitions of
ProtSat.Operational: they say that the decoded configuration of the successor reads back
through the decoded groups of the next step.  They are the reusable part of specification
8A; ProtSat.Encoding.rel_agrees assembles them case by case. -/

/-- Every session other than the one that acts does not act. -/
theorem evAct_false_of_other (h : Sat a (encode P B)) (hi : i < B.steps)
    {q r : Nat} (hq : q < shS (shapeOf P B)) (hr : r < shS (shapeOf P B))
    (hne : r ≠ q) (hk : decCode P B a i = 1 + q) :
    a (evAct (shapeOf P B) i r) = false :=
  evAct_false_of_ne hi h hr hq hne hk

/-- The program counters after a step in which session q acts: q advances by one and every
other session is frame-preserved. -/
theorem pcOf_succ_act (h : Sat a (encode P B)) (hi : i < B.steps) {C C' : Cfg}
    (hag : Agrees P B a C i) {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q)
    (hpcq : pcOf C' q = pcOf C q + 1)
    (hpcr : ∀ r, r < (shapeOf P B).nS1 → r ≠ q → pcOf C' r = pcOf C r) :
    ∀ r, r < (shapeOf P B).nS1 → pcOf C' r = decodePc (shapeOf P B) a (i + 1) r := by
  intro r hr
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
  by_cases hne : r = q
  · subst hne
    rw [hpcq, hag.1 r (lt_nS1_of_evAct hi h hq haq), ← step_pc_succ hi hq h haq]
  · rw [hpcr r hr hne, hag.1 r hr,
      decodePc_frame hi (lt_shS hr) h (evAct_false_of_other h hi hq (lt_shS hr) hne hk)]

/-- The store after a step in which session q writes x₀ := t: the written slot reads t,
every other slot of q keeps its value, and every other session is frame-preserved. -/
theorem decSt_succ_write (h : Sat a (encode P B)) (hi : i < B.steps) {C : Cfg}
    (hag : Agrees P B a C i) {q x₀ : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hw : writtenVar act = some x₀) {t : Term}
    (hwt : decSt (shapeOf P B) a (i + 1) q x₀ = some t) :
    ∀ r x, r < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
      readVar x (storeOf (succStore C q x₀ t) r) = decSt (shapeOf P B) a (i + 1) r x := by
  intro r x hr hx
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
  by_cases hne : r = q
  · subst hne
    by_cases hxy : x = x₀
    · subst hxy
      obtain ⟨st, hst⟩ := sessAt_lt (by rw [hag.2.2.2.2]; exact hr)
      rw [readVar_succStore C r x t st hst]
      exact hwt.symm
    · rw [readVar_succStore_other C r x₀ x t (by intro e; subst e; exact hxy rfl)]
      rw [hag.2.1 r x hr hx]
      symm
      exact step_st_keep hi hq hx h haq hact
        (by intro e; rw [hw] at e; cases e; exact hxy rfl)
  · rw [storeOf_succStore_other C q r x₀ t hne, hag.2.1 r x hr hx,
      ← decSt_frame hi (lt_shS hr) hx h (evAct_false_of_other h hi hq (lt_shS hr) hne hk)]

/-- The store after a step that writes no variable (advance, send): every slot keeps its
value, in the acting session by the keep clauses and elsewhere by the frame clauses. -/
theorem decSt_succ_keep (h : Sat a (encode P B)) (hi : i < B.steps) {C : Cfg}
    (hag : Agrees P B a C i) {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hw : writtenVar act = none) (C' : Cfg)
    (hst : ∀ r x, readVar x (storeOf C' r) = readVar x (storeOf C r)) :
    ∀ r x, r < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
      readVar x (storeOf C' r) = decSt (shapeOf P B) a (i + 1) r x := by
  intro r x hr hx
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
  rw [hst r x, hag.2.1 r x hr hx]
  by_cases hne : r = q
  · subst hne
    symm
    exact step_st_keep hi hq hx h haq hact (by intro e; rw [hw] at e; cases e)
  · symm
    exact decSt_frame hi (lt_shS hr) hx h (evAct_false_of_other h hi hq (lt_shS hr) hne hk)

/-- Well formedness of the stores is preserved by a step that does not write. -/
theorem storeWF_succ_keep (hag : Agrees P B a C i) (C' : Cfg)
    (hst : ∀ r, storeOf C' r = storeOf C r) :
    ∀ r, r < (shapeOf P B).nS1 → StoreWF (shapeOf P B) (storeOf C' r) := by
  intro r hr
  rw [hst r]
  exact hag.2.2.2.1 r hr

/-- Well formedness of the stores is preserved by a store-writing step: the acting session
replaces one variable, and writeVar keeps the store well formed. -/
theorem storeWF_succ_write (h : Sat a (encode P B)) (hi : i < B.steps)
    (hag : Agrees P B a C i) {q x₀ : Nat} (hq : q < shS (shapeOf P B))
    (hx₀ : x₀ < shV (shapeOf P B)) (hk : decCode P B a i = 1 + q) {t : Term} :
    ∀ r, r < (shapeOf P B).nS1 → StoreWF (shapeOf P B) (storeOf (succStore C q x₀ t) r) := by
  intro r hr
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
  by_cases hne : r = q
  · subst hne
    obtain ⟨st, hst⟩ := sessAt_lt (by rw [hag.2.2.2.2]; exact hr)
    rw [storeOf_succStore_same C r x₀ t st hst]
    exact storeWF_writeVar (shapeOf P B) hx₀
      (hag.2.2.2.1 r (lt_nS1_of_evAct hi h hq haq))
  · rw [storeOf_succStore_other C q r x₀ t hne]
    exact hag.2.2.2.1 r hr

/-- The knowledge after a step that teaches nothing. -/
theorem decKn_succ_none (h : Sat a (encode P B)) (hag : Agrees P B a C i)
    (hlearn : decLearn (shapeOf P B) P a i = none) :
    C.kn = decKnSeq (shapeOf P B) P a (i + 1) := by
  rw [decKnSeq_succ, hag.2.2.1]
  simp [hlearn]

/-! ### More decoding helpers -/

/-- The nonce index a fresh group selects, with its variable true. -/
theorem decodeFr_val (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (encode P B)) :
    ∃ d, (frOh (shapeOf P B) i q).decode a = some d ∧ d < shD (shapeOf P B) ∧
      a (vfr (shapeOf P B) i q d) = true := by
  have hoh := sat_frOh hi hq h
  obtain ⟨d, hd⟩ := Oh.decode_some hoh
  exact ⟨d, hd, List.mem_range.mp ((decodeGo_some _ _ _ _ hd).1),
    (decodeGo_some _ _ _ _ hd).2⟩

/-- The value index a delivery group selects, with its variable true. -/
theorem decodeDl_val (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (h : Sat a (encode P B)) :
    ∃ u, (dlOh (shapeOf P B) i q).decode a = some u ∧ u < shVal (shapeOf P B) ∧
      a (vdl (shapeOf P B) i q u) = true := by
  have hoh := sat_dlOh hi hq h
  obtain ⟨u, hu⟩ := Oh.decode_some hoh
  exact ⟨u, hu, List.mem_range.mp ((decodeGo_some _ _ _ _ hu).1),
    (decodeGo_some _ _ _ _ hu).2⟩

/-- A firing deduction instance is one of the instances of some universe message. -/
theorem mem_dedInsts {sh : Shape} {n : Nat} {ins : DedInst} (h : instAt sh n = some ins) :
    ∃ u, u < sh.U.length ∧ ins ∈ dedInstsOf sh u := by
  unfold instAt at h
  have hmem : ins ∈ dedInsts sh := rget_some_mem (dedInsts sh) n ins h
  unfold dedInsts at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨u, hu, hu2⟩ := hmem
  exact ⟨u, List.mem_range.mp hu, hu2⟩

/-- Agrees carries over to a configuration whose program counters and stores are those of C -
an "idle-like" successor - provided the knowledge is the decoded one at the next step. -/
theorem agrees_of_frame (h : Sat a (encode P B)) (hi : i < B.steps) {C C' : Cfg}
    (hag : Agrees P B a C i)
    (hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false)
    (hpc : ∀ r, r < (shapeOf P B).nS1 → pcOf C' r = pcOf C r)
    (hst : ∀ r x, r < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
              readVar x (storeOf C' r) = readVar x (storeOf C r))
    (hkn : C'.kn = decKnSeq (shapeOf P B) P a (i + 1))
    (hwf : ∀ r, r < (shapeOf P B).nS1 → StoreWF (shapeOf P B) (storeOf C' r))
    (hlen : C'.sess.length = (shapeOf P B).nS1) :
    Agrees P B a C' (i + 1) := by
  refine ⟨?_, ?_, hkn, hwf, hlen⟩
  · intro r hr
    rw [hpc r hr, hag.1 r hr, decodePc_frame hi (lt_shS hr) h (hno r hr)]
  · intro r x hr hx
    rw [hst r x hr hx, hag.2.1 r x hr hx,
      ← decSt_frame hi (lt_shS hr) hx h (hno r hr)]

/-! ### Applying the freshness clauses -/

/-- The guard literals of an acting position are false, so the body of a freshness clause
must be satisfied. -/
theorem fresh_body (hi : i < B.steps) (hq : q < shS (shapeOf P B))
    (hc : c < shPc (shapeOf P B)) (h : Sat a (encode P B))
    (ha : a (evAct (shapeOf P B) i q) = true) (hpc : a (vpc (shapeOf P B) i q c) = true)
    {rest : List Lit}
    (hcl : (actGuard (shapeOf P B) i q c ++ rest) ∈
        freshClausesAt (shapeOf P B) P i q c) :
    Clause.eval a rest = true := by
  have := sat_fresh h _ (mem_fresh hi hq hc hcl)
  refine clause_eval_append_of_false (actGuard (shapeOf P B) i q c) rest this ?_
  intro l hl
  unfold actGuard at hl
  rw [List.mem_cons] at hl
  rcases hl with rfl | hl
  · simp [neg_eval, ha]
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · simp [neg_eval, hpc]
    · exact absurd hl (by simp)

/-- A variable an action writes is within the shape's store-slot bound. -/
theorem lt_shV_of_written {q c : Nat} {act : Action} (hact : P.actionAt q c = some act)
    {x : Nat} (hx : x ∈ act.written) : x < shV (shapeOf P B) := by
  have h1 : x ∈ (P.roles.flatMap fun r =>
      r.acts.flatMap fun a => a.written ++ a.exprs.flatMap Expr.vars) := by
    have ha : act ∈ P.roles.flatMap (fun r => r.acts) := mem_acts_of_actionAt hact
    rw [List.mem_flatMap] at ha ⊢
    obtain ⟨r, hr, ham⟩ := ha
    refine ⟨r, hr, List.mem_flatMap.mpr ⟨act, ham, ?_⟩⟩
    rw [List.mem_append]
    exact Or.inl hx
  have h2 : x ≤ (shapeOf P B).nV1 := le_maxNat_of_mem _ _ h1
  show x < (shapeOf P B).nV1 + 1
  omega

/-- A variable read by an expression of the protocol is within the shape's store-slot
bound: the bound is taken over the variables of every subexpression of every action. -/
theorem lt_shV_of_mem {e : Expr} (he : e ∈ allExprs P) {x : Nat}
    (hx : x ∈ Expr.vars e) : x < shV (shapeOf P B) := by
  rw [allExprs, List.mem_eraseDups] at he
  obtain ⟨r, hr, ham⟩ := List.mem_flatMap.mp he
  obtain ⟨act, ham2, hmem⟩ := List.mem_flatMap.mp ham
  have h1 : x ∈ (P.roles.flatMap fun r =>
      r.acts.flatMap fun a => a.written ++ a.exprs.flatMap Expr.vars) := by
    refine List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨act, ham2, ?_⟩⟩
    rw [List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨e, hmem, hx⟩)
  have h2 : x ≤ (shapeOf P B).nV1 := le_maxNat_of_mem _ _ h1
  show x < (shapeOf P B).nV1 + 1
  omega

/-- Membership in a list is reading it at some index. -/
theorem mem_rget {α : Type} : ∀ (l : List α) (x : α), x ∈ l -> ∃ i, i < l.length ∧
    rget l i = some x := by
  intro l
  induction l with
  | nil => intro x h; exact absurd h (by simp)
  | cons y ys ih =>
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨i, hi, heq⟩ := ih x hx
        exact ⟨i + 1, by simpa [List.length_cons] using hi, by rw [rget_succ, heq]⟩

/-- A Boolean whose negation is true is false. -/
theorem bool_not_true {x : Bool} (h : (!x) = true) : x = false := by
  cases x <;> simp_all

/-! ### The core of specification 8A -/

/-- Agrees after a step that only advances the acting session (a test, a declaration or an
authentication event): the stores are untouched and nothing is published. -/
theorem agrees_succ_advance (h : Sat a (encode P B)) (hi : i < B.steps) {C : Cfg}
    (hag : Agrees P B a C i) {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) {act : Action}
    (hact : P.actionAt q (decodePc (shapeOf P B) a i q) = some act)
    (hw : writtenVar act = none)
    (hlearn : decLearn (shapeOf P B) P a i = none) :
    Agrees P B a (succAdvance C q) (i + 1) := by
  have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
  have hnS : q < (shapeOf P B).nS1 := lt_nS1_of_evAct hi h hq haq
  refine ⟨pcOf_succ_act h hi hag hq hk
      (pcOf_succAdvance' C q (by rw [hag.2.2.2.2]; exact hnS))
      (fun r hr hne => pcOf_succAdvance_other C q r hne),
    decSt_succ_keep h hi hag hq hk hact hw _
      (fun r x => congrArg (readVar x) (storeOf_succAdvance C q r)),
    (decKn_succ_none h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
    storeWF_succ_keep hag _ (fun r => storeOf_succAdvance C q r),
    by rw [sessLength_succAdvance, hag.2.2.2.2]⟩

/-- Every premise index of a universe deduction instance is an in-range universe position.
The instances are built from ProtSat.Encode.tIx and from first-occurrence indices of
messages that are in the universe, so this is a case analysis over the eleven rule shapes of
specification section 2. -/
theorem dedInstsOf_prem_lt {sh : Shape} {u : Nat} (hu : u < sh.U.length) {ins : DedInst}
    (h : ins ∈ dedInstsOf sh u) : ∀ p ∈ ins.prem, p < sh.U.length := by
  obtain ⟨t', ht'⟩ := rget_lt sh.U u hu
  have hix : ∀ x ∈ sh.U, ixOf x sh.U < sh.U.length := by
    intro x hx
    by_contra e
    have h1 : rget sh.U (ixOf x sh.U) = some x := rget_ixOf sh.U x hx
    have h2 : rget sh.U (ixOf x sh.U) = none := rget_oob_ge sh.U _ (by omega)
    rw [h2] at h1; simp at h1
  have one : ∀ {b : Nat}, b < sh.U.length -> ∀ q ∈ ([b] : List Nat), q < sh.U.length := by
    intro b hb q hq
    rw [List.mem_singleton] at hq
    cases hq
    exact hb
  have two : ∀ {b₁ b₂ : Nat}, b₁ < sh.U.length -> b₂ < sh.U.length ->
      ∀ q ∈ ([b₁, b₂] : List Nat), q < sh.U.length := by
    intro b₁ b₂ hb₁ hb₂ q hq
    rw [List.mem_cons] at hq
    rcases hq with hq | hq
    · cases hq; exact hb₁
    · rw [List.mem_singleton] at hq; cases hq; exact hb₂
  unfold dedInstsOf at h
  rw [ht'] at h
  simp only [List.mem_cons, List.mem_append, List.mem_filterMap] at h
  rcases h with h | ⟨a, ha, ham⟩
  · rcases h with h | h
    · subst h
      exact one hu
    · cases t' with
      | agent A => simp at h; subst h; simp
      | key k =>
          cases k with
          | pub A => simp at h; subst h; simp
          | _ => simp at h
      | pair x y =>
          rcases h5 : tIx sh x with ⟨b₁⟩|⟨b₁⟩
          · simp [h5] at h
          · rcases h6 : tIx sh y with ⟨b₂⟩|⟨b₂⟩
            · simp [h6] at h
            · simp [h5, h6] at h
              subst h
              exact two (tIx_lt h5) (tIx_lt h6)
      | encS m k =>
          rcases h5 : tIx sh m with ⟨b₁⟩|⟨b₁⟩
          · simp [h5] at h
          · rcases h6 : tIx sh (Term.key k) with ⟨b₂⟩|⟨b₂⟩
            · simp [h6] at h
            · simp [h5, h6] at h
              subst h
              exact two (tIx_lt h5) (tIx_lt h6)
      | encA m ag =>
          rcases h5 : tIx sh m with ⟨b₁⟩|⟨b₁⟩
          · simp [h5] at h
          · simp [h5] at h
            subst h
            exact one (tIx_lt h5)
      | hash m =>
          rcases h5 : tIx sh m with ⟨b₁⟩|⟨b₁⟩
          · simp [h5] at h
          · simp [h5] at h
            subst h
            exact one (tIx_lt h5)
      | _ => simp at h
  · cases a with
    | pair x y =>
        by_cases h1 : x = t'
        · simp at ham
          rw [if_pos h1] at ham
          simp at ham
          subst ham
          exact one (hix (Term.pair x y) ha)
        · by_cases h2 : y = t'
          · simp at ham
            rw [if_neg h1, if_pos h2] at ham
            simp at ham
            subst ham
            exact one (hix (Term.pair x y) ha)
          · simp at ham
            rw [if_neg h1, if_neg h2] at ham
            simp at ham
    | encS m k =>
        by_cases h1 : m = t'
        · simp at ham
          rcases ham with ⟨h3, ham⟩
          rcases h5 : tIx sh (Term.key k) with ⟨b₂⟩|⟨b₂⟩
          · rw [h5] at ham
            simp at ham
          · simp [h5] at ham
            subst ham
            exact two (hix (Term.encS m k) ha) (tIx_lt h5)
        · simp at ham
          rcases ham with ⟨h3, _⟩
          exact absurd h3 h1
    | encA m ag =>
        by_cases h1 : m = t'
        · simp at ham
          rcases ham with ⟨h3, ham⟩
          rcases h5 : tIx sh (Term.key (Key.priv ag)) with ⟨b₂⟩|⟨b₂⟩
          · rw [h5] at ham
            simp at ham
          · simp [h5] at ham
            subst ham
            exact two (hix (Term.encA m ag) ha) (tIx_lt h5)
        · simp at ham
          rcases ham with ⟨h3, _⟩
          exact absurd h3 h1
    | _ => simp at ham


/-- **Every decoded step is a transition of the operational semantics.**  Let a be a
satisfying assignment of the encoding, let C be a configuration that agrees with a at step
i (in the sense of ProtSat.Encoding.Agrees), and assume the universe hypothesis.  Then the
event the assignment selects at step i is an instance of ProtSat.Rel from C, and the
configuration decoded at step i+1 is exactly the one Rel prescribes.

This is the soundness half of the encoding correspondence (specification 8A).  The proof
reads each clause group back as a semantic fact: the step clauses give the successor, the
deduction clauses plus kn_sound give the attacker's one-step derivation, the delivery
clauses give that a received message is known, the evaluation clauses give that an
expression evaluates to the value its Tseitin group selected, and the freshness clauses
give the side condition of ProtSat.Rel.rFresh.  Nothing here uses the solver: the argument
is about satisfying assignments, which is what makes the certificate checker of
ProtSat.Certificate independent. -/
theorem rel_agrees (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B))
    {i : Nat} (hi : i < B.steps) {C : Cfg} (hag : Agrees P B a C i) :
    Rel P C (decEv (shapeOf P B) P a i) (decStep P B a C i) ∧
      Agrees P B a (decStep P B a C i) (i + 1) := by
  rcases ev_cases hi h with h0 | ⟨q, hq, hk⟩ | ⟨n, hn, hk⟩
  · -- ---- the idle step ----
    have hev : decEv (shapeOf P B) P a i = Ev.idle := by
      rw [decEv_code hi h, h0]
      simp
    have hstep : decStep P B a C i = C := by unfold decStep; rw [hev]
    have hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false := by
      intro r hr
      by_contra e
      have := decCode_of_evAct hi h (lt_shS hr) (by simpa [evAct] using e)
      omega
    have hlearn : decLearn (shapeOf P B) P a i = none := by
      rw [decLearn_code hi h, h0]
      simp
    refine ⟨?_, ?_⟩
    · rw [hev, hstep]
      exact Rel.rIdle P C
    · rw [hstep]
      exact agrees_of_noact h hi hno hag hlearn
  · -- ---- session q acts ----
    have haq : a (evAct (shapeOf P B) i q) = true := evAct_eq_of_code hi h hq hk
    have hnS : q < (shapeOf P B).nS1 := lt_nS1_of_evAct hi h hq haq
    have hc : decodePc (shapeOf P B) a i q < shPc (shapeOf P B) :=
      decodePc_lt (Nat.le_of_lt hi) hq h
    have hpc0 : a (vpc (shapeOf P B) i q (decodePc (shapeOf P B) a i q)) = true :=
      decodePc_true (Nat.le_of_lt hi) hq h
    have hev : decEv (shapeOf P B) P a i = Ev.act q (decDeliver (shapeOf P B) a i q)
        (decNonce (shapeOf P B) a i q) := decEv_act_of_code hi h hq hk
    have hno : ∀ r, r < (shapeOf P B).nS1 → r ≠ q →
        a (evAct (shapeOf P B) i r) = false :=
      fun r hr hne => evAct_false_of_other h hi hq (lt_shS hr) hne hk
    have hpcq : pcOf C q = decodePc (shapeOf P B) a i q := hag.1 q hnS
    have hlenC : C.sess.length = (shapeOf P B).nS1 := hag.2.2.2.2
    cases hact : P.actionAt q (decodePc (shapeOf P B) a i q) with
    | none => exact absurd hact (some_actionAt_of_evAct hi hq h haq)
    | some act =>
      cases act with
      | fresh x N =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.fresh x N) =
              ((List.range (shD (shapeOf P B))).flatMap fun d =>
                  freshStepClauses (shapeOf P B) i q (decodePc (shapeOf P B) a i q) x d)
                ++ [actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                      [neg (vfr (shapeOf P B) i q (shD (shapeOf P B) - 1))]] := by
            simp [actionClauses]
          obtain ⟨d, hd, hdlt, hvfr⟩ := decodeFr_val hi hq h
          -- the dummy nonce alternative is excluded, so the choice is a real domain nonce
          have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vfr (shapeOf P B) i q (shD (shapeOf P B) - 1))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.fresh x N) hact, hred]
            exact List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _))
          have h1 := step_body hi hq hc h haq hpc0 hcl
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
          have hd2 : d < (shapeOf P B).D.length := by
            by_contra e
            have hs : shD (shapeOf P B) = (shapeOf P B).D.length + 1 := rfl
            have h2 : d = shD (shapeOf P B) - 1 := by
              rw [hs]
              omega
            rw [h2] at hvfr
            exact absurd hvfr (by simpa using h1)
          obtain ⟨N', hN'⟩ := rget_lt (shapeOf P B).D d hd2
          have hdN : decNonce (shapeOf P B) a i q = N' := by
            unfold decNonce; simp [hd, hN']
          have hD : N' ∈ P.nonceDomain := by
            rw [← D_eq]; exact rget_mem (shapeOf P B).D d N' hd2 hN'
          have hUn : Term.nonce N' ∈ (shapeOf P B).U := nonceDomain_mem_univ hD
          have hxlt : x < shV (shapeOf P B) := lt_shV_of_written hact (by simp [Action.written])
          -- the fresh step clause writes the nonce into the store slot
          have hcl2 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vfr (shapeOf P B) i q d),
                pos (vst (shapeOf P B) (i + 1) q x
                  (uIdx (shapeOf P B) (some (Term.nonce N'))))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.fresh x N) hact, hred]
            refine List.mem_append_right _ (List.mem_append_left _
              (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hdlt, ?_⟩))
            rw [freshStepClauses, hN']
            exact List.Mem.head _
          have h2 := step_body hi hq hc h haq hpc0 hcl2
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvfr,
            Bool.not_true, pos_eval] at h2
          have hwt : decSt (shapeOf P B) a (i + 1) q x = some (Term.nonce N') := by
            unfold decSt decVal
            have h3 : (stOh (shapeOf P B) (i + 1) q x).decode a =
                some (uIdx (shapeOf P B) (some (Term.nonce N'))) :=
              Oh.decode_of_true (sat_stOh (Nat.succ_le_of_lt hi) hq hxlt h)
                (List.mem_range.mpr (uIdx_lt' (shapeOf P B) (some (Term.nonce N')))) h2
            simp [h3, valAt_uIdx_some (shapeOf P B) hUn]
          -- the nonce is unused: neither in a store nor known
          have hnu : nonceUsed C N' = false := by
            by_contra e
            have htrue : nonceUsed C N' = true := by
              cases h : nonceUsed C N' with
              | true => rfl
              | false => exact absurd h e
            rw [nonceUsed, Bool.or_eq_true] at htrue
            rcases htrue with h1 | h2
            · obtain ⟨st, hst, hf⟩ := List.any_eq_true.mp h1
              obtain ⟨r, hr, heq⟩ := mem_rget C.sess st hst
              have hr' : r < (shapeOf P B).nS1 := by rw [← hlenC]; exact hr
              have hs : storeOf C r = st.store := by
                unfold storeOf sessAt
                rw [heq]
                rfl
              rw [← hs] at hf
              have hmem : Term.nonce N' ∈ storeVals (storeOf C r) := by simpa using hf
              have := (hag.storeVals_iff hr' (Term.nonce N')).mp hmem
              obtain ⟨x', hx', he⟩ := this
              have hv : a (vst (shapeOf P B) i r x'
                  (uIdx (shapeOf P B) (some (Term.nonce N')))) = true :=
                decSt_some_vst (Nat.le_of_lt hi) (lt_shS hr') hx' h hUn he
              have hcl3 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                  [neg (vfr (shapeOf P B) i q d),
                    neg (vst (shapeOf P B) i r x'
                      (uIdx (shapeOf P B) (some (Term.nonce N'))))] ∈
                  freshClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
                rw [freshClausesAt, hact]
                refine List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hdlt, ?_⟩
                rw [freshUseClauses, hN']
                refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨r,
                  List.mem_range.mpr (lt_shS hr'), List.mem_map.mpr ⟨x', List.mem_range.mpr hx', rfl⟩⟩)
              have h3 := fresh_body hi hq hc h haq hpc0 hcl3
              simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvfr,
                Bool.not_true] at h3
              exact absurd (hv ▸ bool_not_true h3) (by simp)
            · have hk' : Term.nonce N' ∈ C.kn := by simpa using h2
              rw [hag.2.2.1] at hk'
              have hv : a (vkn (shapeOf P B) i
                  (uIdx (shapeOf P B) (some (Term.nonce N')))) = true :=
                kn_complete h (uIdx_lt_of_mem hUn)
                  (valAt_uIdx_some (shapeOf P B) hUn) i (Nat.le_of_lt hi) hk'
              have hcl4 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                  [neg (vfr (shapeOf P B) i q d),
                    neg (vkn (shapeOf P B) i (uIdx (shapeOf P B) (some (Term.nonce N'))))] ∈
                  freshClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
                rw [freshClausesAt, hact]
                refine List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hdlt, ?_⟩
                rw [freshUseClauses, hN']
                exact List.mem_append_right _ (List.Mem.head _)
              have h4 := fresh_body hi hq hc h haq hpc0 hcl4
              simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvfr,
                Bool.not_true] at h4
              exact absurd (hv ▸ bool_not_true h4) (by simp)
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succStore C q x (Term.nonce N') := by
            unfold decStep; simp [hev, hpcq, hact, hdN]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep, hdN]
            exact Rel.rFresh (by rw [hpcq]; exact hact) hD hnu
          rw [hstep]
          refine ⟨pcOf_succ_act h hi hag hq hk (pcOf_succStore' C q x (Term.nonce N')
              (by rw [hlenC]; exact hnS)) (fun r hr hne => pcOf_succStore_other C q r x _ hne),
            decSt_succ_write h hi hag hq hk hact rfl hwt,
            (decKn_succ_none h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
            storeWF_succ_write h hi hag hq hxlt hk,
            by rw [sessLength_succStore, hag.2.2.2.2]⟩
      | send a' e =>
          have hmem : e ∈ allExprs P := mem_allExprs_send hact
          obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt hmem (Nat.le_of_lt hi) hq h
          have hdec : decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) v := by
            unfold decXe decVal; rw [hv]
          -- a send cannot evaluate to the unset value
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.send a' e) =
              [sendRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e)]
                ++ mapMsg (shapeOf P B) (fun w =>
                    sendPublishClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q)
                      (eIdx P e) w) := by
            simp [actionClauses]
          have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vxe (shapeOf P B) i q (eIdx P e) ((shapeOf P B).U.length))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.send a' e) hact, hred]
            exact List.mem_append_right _ (List.mem_append_left _ (List.Mem.head _))
          have h1 := step_body hi hq hc h haq hpc0 hcl
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
          have hvlt' : v < (shapeOf P B).U.length := by
            have hs : shVal (shapeOf P B) = (shapeOf P B).U.length + 1 := rfl
            by_contra e2
            have hv2 : v = (shapeOf P B).U.length := by
              rw [hs] at hvlt
              omega
            rw [hv2] at hvv
            exact absurd (hvv ▸ bool_not_true h1) (by simp)
          obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U v hvlt'
          have hdec' : decXe (shapeOf P B) P a i q e = some t := by
            rw [hdec]
            exact ht
          -- the value the Tseitin group selected is the value of the expression in the store
          have h2 : ∀ x, x ∈ e.vars ->
              Expr.lookup x (storeOf C q) = Expr.lookup x (decodeStore (shapeOf P B) a i q) := by
            intro x hx
            have hxv : x < shV (shapeOf P B) := lt_shV_of_mem hmem hx
            show readVar x (storeOf C q) = readVar x (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q x hnS hxv, readVar_decodeStore hxv]
          have heval : Expr.eval e (storeOf C q) = some t := by
            have h3 : decXe (shapeOf P B) P a i q e =
                Expr.eval e (decodeStore (shapeOf P B) a i q) :=
              decXe_eq hU h (Nat.le_of_lt hi) hq e hmem
            have h4 : Expr.eval e (decodeStore (shapeOf P B) a i q) = some t := by
              rw [← h3, hdec']
            rw [← h4]
            exact Expr.eval_congr h2
          have hact2 : P.actionAt q (pcOf C q) = some (Action.send a' e) := by
            rw [hpcq]; exact hact
          -- the send publishes the value it sends
          have hlearn : decLearn (shapeOf P B) P a i = some t := by
            simp [decLearn_act hi h hq hk, hact, hdec']
          have hstep : decStep P B a C i = succSend C q t := by
            unfold decStep; simp [hev, hpcq, hact, heval]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rSend hact2 heval
          rw [hstep]
          have hst : ∀ r x, readVar x (storeOf (succSend C q t) r) = readVar x (storeOf C r) := by
            intro r x
            by_cases hne : r = q
            · subst hne; rw [storeOf_succSend_same]
            · rw [storeOf_succSend_other C q r t hne]
          have hwf : ∀ r, r < (shapeOf P B).nS1 →
              StoreWF (shapeOf P B) (storeOf (succSend C q t) r) := by
            intro r hr
            by_cases hne : r = q
            · subst hne; rw [storeOf_succSend_same]; exact hag.2.2.2.1 r hr
            · rw [storeOf_succSend_other C q r t hne]; exact hag.2.2.2.1 r hr
          refine ⟨pcOf_succ_act h hi hag hq hk
              (pcOf_succSend' C q t (by rw [hlenC]; exact hnS))
              (fun r hr hne => pcOf_succSend_other C q r _ hne),
            decSt_succ_keep h hi hag hq hk hact rfl _ hst, ?_, hwf,
            by rw [sessLength_succSend, hag.2.2.2.2]⟩
          · rw [decKnSeq_succ, kn_succSend, hag.2.2.1]
            simp [hlearn]
      | recv a' x =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.recv a' x) = (eachVal (shapeOf P B) fun w =>
              if w < (shapeOf P B).U.length then
                [recvStoreClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) w x,
                  recvKnowClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) w x]
              else [recvRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) w]) := by
            simp [actionClauses]
          obtain ⟨u, hu, hult, hudl⟩ := decodeDl_val hi hq h
          have hxlt : x < shV (shapeOf P B) := lt_shV_of_written hact (by simp [Action.written])
          by_cases hurlt : u < (shapeOf P B).U.length
          · -- the delivered value is a real universe message
            obtain ⟨m, hm⟩ := rget_lt (shapeOf P B).U u hurlt
            have hdl : decDeliver (shapeOf P B) a i q = m := by
              unfold decDeliver decVal
              rw [hu]
              show Option.getD (rget (shapeOf P B).U u) (Term.nonce 0) = m
              rw [hm]
              rfl
            -- it is known to the attacker
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vdl (shapeOf P B) i q u), pos (vkn (shapeOf P B) i u)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.recv a' x) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hult, ?_⟩)
              rw [if_pos hurlt]
              exact List.Mem.tail _ (List.Mem.head _)
            have h1 := step_body hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hudl,
              Bool.not_true, pos_eval] at h1
            have hkn : m ∈ C.kn := by
              rw [hag.2.2.1]
              exact kn_sound h hm i (Nat.le_of_lt hi) h1
            -- and it lands in the store slot
            have hcl2 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vdl (shapeOf P B) i q u), pos (vst (shapeOf P B) (i + 1) q x u)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.recv a' x) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hult, ?_⟩)
              rw [if_pos hurlt]
              exact List.Mem.head _
            have h2 := step_body hi hq hc h haq hpc0 hcl2
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hudl,
              Bool.not_true, pos_eval] at h2
            have hwt : decSt (shapeOf P B) a (i + 1) q x = some m := by
              unfold decSt decVal
              have h5 : (stOh (shapeOf P B) (i + 1) q x).decode a = some u :=
                Oh.decode_of_true (sat_stOh (Nat.succ_le_of_lt hi) hq hxlt h)
                  (List.mem_range.mpr hult) h2
              rw [h5]
              show rget (shapeOf P B).U u = some m
              exact hm
            have hlearn : decLearn (shapeOf P B) P a i = none :=
              decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
            have hstep : decStep P B a C i = succStore C q x m := by
              unfold decStep; simp [hev, hdl, hpcq, hact]
            refine ⟨?_, ?_⟩
            · rw [hev, hstep, hdl]
              exact Rel.rRecv (by rw [hpcq]; exact hact) hkn
            rw [hstep]
            refine ⟨pcOf_succ_act h hi hag hq hk
                (pcOf_succStore' C q x m (by rw [hlenC]; exact hnS))
                (fun r hr hne => pcOf_succStore_other C q r x _ hne),
              decSt_succ_write h hi hag hq hk hact rfl hwt,
              (decKn_succ_none h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
              storeWF_succ_write h hi hag hq hxlt hk,
              by rw [sessLength_succStore, hag.2.2.2.2]⟩
          · -- the delivery group cannot select the unset value
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vdl (shapeOf P B) i q u)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.recv a' x) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hult, ?_⟩)
              rw [if_neg hurlt]
              exact List.Mem.head _
            have h1 := step_body hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
            exact absurd (hudl ▸ bool_not_true h1) (by simp)
      | assign x e =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.assign x e) = (eachVal (shapeOf P B) fun w =>
              if w < (shapeOf P B).U.length then
                [assignClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e) w x]
              else [assignRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e) w]) := by
            simp [actionClauses]
          have hmem : e ∈ allExprs P := mem_allExprs_assign hact
          have hxlt : x < shV (shapeOf P B) := lt_shV_of_written hact (by simp [Action.written])
          obtain ⟨v, hv, hvlt, hvv⟩ := decodeXe_lt hmem (Nat.le_of_lt hi) hq h
          have hdec : decXe (shapeOf P B) P a i q e = valAt (shapeOf P B) v := by
            unfold decXe decVal; rw [hv]
          have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vxe (shapeOf P B) i q (eIdx P e) ((shapeOf P B).U.length))] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.assign x e) hact, hred, eachVal]
            refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨(shapeOf P B).U.length,
                List.mem_range.mpr (lt_shVal (Nat.le_refl _)), ?_⟩)
            rw [if_neg (by omega : ¬ ((shapeOf P B).U.length < (shapeOf P B).U.length))]
            exact List.Mem.head _
          have h1 := step_body hi hq hc h haq hpc0 hcl
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or, neg_eval] at h1
          have hvlt' : v < (shapeOf P B).U.length := by
            have hs : shVal (shapeOf P B) = (shapeOf P B).U.length + 1 := rfl
            by_contra e2
            have hv2 : v = (shapeOf P B).U.length := by
              rw [hs] at hvlt
              omega
            rw [hv2] at hvv
            exact absurd (hvv ▸ bool_not_true h1) (by simp)
          obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U v hvlt'
          have hdec' : decXe (shapeOf P B) P a i q e = some t := by
            rw [hdec]
            exact ht
          have h2 : ∀ y, y ∈ e.vars ->
              Expr.lookup y (storeOf C q) = Expr.lookup y (decodeStore (shapeOf P B) a i q) := by
            intro y hy
            have hyv : y < shV (shapeOf P B) := lt_shV_of_mem hmem hy
            show readVar y (storeOf C q) = readVar y (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q y hnS hyv, readVar_decodeStore hyv]
          have heval : Expr.eval e (storeOf C q) = some t := by
            have h3 : decXe (shapeOf P B) P a i q e =
                Expr.eval e (decodeStore (shapeOf P B) a i q) :=
              decXe_eq hU h (Nat.le_of_lt hi) hq e hmem
            have h4 : Expr.eval e (decodeStore (shapeOf P B) a i q) = some t := by
              rw [← h3, hdec']
            rw [← h4]
            exact Expr.eval_congr h2
          have hcl2 : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
              [neg (vxe (shapeOf P B) i q (eIdx P e) v), pos (vst (shapeOf P B) (i + 1) q x v)] ∈
              stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
            rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.assign x e) hact, hred, eachVal]
            refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hvlt, ?_⟩)
            rw [if_pos hvlt']
            exact List.Mem.head _
          have h3 := step_body hi hq hc h haq hpc0 hcl2
          simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hvv,
            Bool.not_true, pos_eval] at h3
          have hwt : decSt (shapeOf P B) a (i + 1) q x = some t := by
            unfold decSt decVal
            have h5 : (stOh (shapeOf P B) (i + 1) q x).decode a = some v :=
              Oh.decode_of_true (sat_stOh (Nat.succ_le_of_lt hi) hq hxlt h)
                (List.mem_range.mpr hvlt) h3
            rw [h5]
            show rget (shapeOf P B).U v = some t
            exact ht
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succStore C q x t := by
            unfold decStep; simp [hev, hpcq, hact, heval]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rAssign (by rw [hpcq]; exact hact) heval
          rw [hstep]
          refine ⟨pcOf_succ_act h hi hag hq hk
              (pcOf_succStore' C q x t (by rw [hlenC]; exact hnS))
              (fun r hr hne => pcOf_succStore_other C q r x _ hne),
            decSt_succ_write h hi hag hq hk hact rfl hwt,
            (decKn_succ_none h hag hlearn : C.kn = decKnSeq (shapeOf P B) P a (i + 1)),
            storeWF_succ_write h hi hag hq hxlt hk,
            by rw [sessLength_succStore, hag.2.2.2.2]⟩
      | check e₁ e₂ =>
          have hred : actionClauses (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
              (Action.check e₁ e₂) =
              [checkRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e₁),
                checkRealClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q) (eIdx P e₂)]
                ++ (eachVal (shapeOf P B) fun w =>
                    (List.range (shVal (shapeOf P B))).filterMap fun z =>
                      if w == z then none
                      else some (checkEqClause (shapeOf P B) i q
                        (decodePc (shapeOf P B) a i q) (eIdx P e₁) (eIdx P e₂) w z)) := by
            simp [actionClauses]
          obtain ⟨hm₁, hm₂⟩ := mem_allExprs_check hact
          obtain ⟨v₁, hde₁, hvl₁, hvar₁⟩ := decodeXe_lt hm₁ (Nat.le_of_lt hi) hq h
          obtain ⟨v₂, hde₂, hvl₂, hvar₂⟩ := decodeXe_lt hm₂ (Nat.le_of_lt hi) hq h
          have hs : shVal (shapeOf P B) = (shapeOf P B).U.length + 1 := rfl
          -- both sides denote real messages
          have hr₁ : a (vxe (shapeOf P B) i q (eIdx P e₁) ((shapeOf P B).U.length)) = false := by
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vxe (shapeOf P B) i q (eIdx P e₁) ((shapeOf P B).U.length))] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.check e₁ e₂) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_append_left _ ?_)
              exact List.Mem.head _
            have h1 := step_body hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or,
              neg_eval] at h1
            exact bool_not_true h1
          have hr₂ : a (vxe (shapeOf P B) i q (eIdx P e₂) ((shapeOf P B).U.length)) = false := by
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vxe (shapeOf P B) i q (eIdx P e₂) ((shapeOf P B).U.length))] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.check e₁ e₂) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_append_left _ ?_)
              exact List.Mem.tail _ (List.Mem.head _)
            have h1 := step_body hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or,
              neg_eval] at h1
            exact bool_not_true h1
          have hv₁ : v₁ < (shapeOf P B).U.length := by
            by_contra e
            have h1 : v₁ = (shapeOf P B).U.length := by
              rw [hs] at hvl₁
              omega
            rw [h1] at hvar₁
            exact absurd (hvar₁ ▸ hr₁) (by simp)
          have hv₂ : v₂ < (shapeOf P B).U.length := by
            by_contra e
            have h1 : v₂ = (shapeOf P B).U.length := by
              rw [hs] at hvl₂
              omega
            rw [h1] at hvar₂
            exact absurd (hvar₂ ▸ hr₂) (by simp)
          -- and they denote the same message
          have heqv : v₁ = v₂ := by
            by_contra e
            have hcl : actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                [neg (vxe (shapeOf P B) i q (eIdx P e₁) v₁),
                  neg (vxe (shapeOf P B) i q (eIdx P e₂) v₂)] ∈
                stepClausesAt (shapeOf P B) P i q (decodePc (shapeOf P B) a i q) := by
              rw [stepClausesAt_some (shapeOf P B) P i q (decodePc (shapeOf P B) a i q)
                (Action.check e₁ e₂) hact, hred, eachVal]
              refine List.mem_append_right _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨v₁, List.mem_range.mpr hvl₁, ?_⟩))
              show actGuard (shapeOf P B) i q (decodePc (shapeOf P B) a i q) ++
                  [neg (vxe (shapeOf P B) i q (eIdx P e₁) v₁),
                    neg (vxe (shapeOf P B) i q (eIdx P e₂) v₂)] ∈
                (List.range (shVal (shapeOf P B))).filterMap fun z =>
                  if v₁ == z then none
                  else some (checkEqClause (shapeOf P B) i q (decodePc (shapeOf P B) a i q)
                    (eIdx P e₁) (eIdx P e₂) v₁ z)
              refine List.mem_filterMap.mpr ⟨v₂, List.mem_range.mpr hvl₂, ?_⟩
              rw [if_neg (by intro h; exact e (by simpa using h))]
              rfl
            have h1 := step_body hi hq hc h haq hpc0 hcl
            simp only [Clause.eval_cons, clause_eval_nil, Bool.or_false, Bool.false_or,
              neg_eval, hvar₁, hvar₂, Bool.not_true] at h1
            exact absurd h1 (by simp)
          subst heqv
          obtain ⟨t, ht⟩ := rget_lt (shapeOf P B).U v₁ hv₁
          have hdec₁ : decXe (shapeOf P B) P a i q e₁ = some t := by
            unfold decXe decVal
            rw [hde₁]
            show rget (shapeOf P B).U v₁ = some t
            exact ht
          have hdec₂ : decXe (shapeOf P B) P a i q e₂ = some t := by
            unfold decXe decVal
            rw [hde₂]
            show rget (shapeOf P B).U v₁ = some t
            exact ht
          have hc₁ : ∀ x, x ∈ Expr.vars e₁ ->
              Expr.lookup x (storeOf C q) = Expr.lookup x (decodeStore (shapeOf P B) a i q) := by
            intro x hx
            have hxv : x < shV (shapeOf P B) := lt_shV_of_mem hm₁ hx
            show readVar x (storeOf C q) = readVar x (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q x hnS hxv, readVar_decodeStore hxv]
          have hc₂ : ∀ x, x ∈ Expr.vars e₂ ->
              Expr.lookup x (storeOf C q) = Expr.lookup x (decodeStore (shapeOf P B) a i q) := by
            intro x hx
            have hxv : x < shV (shapeOf P B) := lt_shV_of_mem hm₂ hx
            show readVar x (storeOf C q) = readVar x (decodeStore (shapeOf P B) a i q)
            rw [hag.2.1 q x hnS hxv, readVar_decodeStore hxv]
          have he₁ : Expr.eval e₁ (storeOf C q) = some t := by
            have h3 : decXe (shapeOf P B) P a i q e₁ =
                Expr.eval e₁ (decodeStore (shapeOf P B) a i q) :=
              decXe_eq hU h (Nat.le_of_lt hi) hq e₁ hm₁
            have h4 : Expr.eval e₁ (decodeStore (shapeOf P B) a i q) = some t := by
              rw [← h3, hdec₁]
            rw [← h4]
            exact Expr.eval_congr hc₁
          have he₂ : Expr.eval e₂ (storeOf C q) = some t := by
            have h3 : decXe (shapeOf P B) P a i q e₂ =
                Expr.eval e₂ (decodeStore (shapeOf P B) a i q) :=
              decXe_eq hU h (Nat.le_of_lt hi) hq e₂ hm₂
            have h4 : Expr.eval e₂ (decodeStore (shapeOf P B) a i q) = some t := by
              rw [← h3, hdec₂]
            rw [← h4]
            exact Expr.eval_congr hc₂
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rCheck (by rw [hpcq]; exact hact) he₁ he₂
          · rw [hstep]
            exact agrees_succ_advance h hi hag hq hk hact rfl hlearn

      | secret e =>
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rSecret (by rw [hpcq]; exact hact)
          rw [hstep]
          exact agrees_succ_advance h hi hag hq hk hact rfl hlearn
      | claim tg peer v =>
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rClaim (by rw [hpcq]; exact hact)
          rw [hstep]
          exact agrees_succ_advance h hi hag hq hk hact rfl hlearn
      | commit tg peer v =>
          have hlearn : decLearn (shapeOf P B) P a i = none :=
            decLearn_none_of_not_send hi h hq hk hact (by intro a' e heq; cases heq)
          have hstep : decStep P B a C i = succAdvance C q := by
            unfold decStep; simp [hev, hpcq, hact]
          refine ⟨?_, ?_⟩
          · rw [hev, hstep]
            exact Rel.rCommit (by rw [hpcq]; exact hact)
          rw [hstep]
          exact agrees_succ_advance h hi hag hq hk hact rfl hlearn
  · -- ---- the attacker fires deduction instance n ----
    obtain ⟨ins, hins0⟩ := rget_lt (dedInsts (shapeOf P B)) n hn
    have hins : instAt (shapeOf P B) n = some ins := hins0
    have hev : a (evDed (shapeOf P B) i n) = true := by
      have : a (vev (shapeOf P B) i (decCode P B a i)) = true := decCode_true hi h
      rw [hk] at this
      exact this
    have hno : ∀ r, r < (shapeOf P B).nS1 → a (evAct (shapeOf P B) i r) = false := by
      intro r hr
      by_contra e
      have hlt : r < shS (shapeOf P B) := lt_shS hr
      have := decCode_of_evAct hi h hlt (by simpa [evAct] using e)
      have hpos : 0 < shS (shapeOf P B) := by unfold shS; omega
      omega
    cases hval : valAt (shapeOf P B) ins.concl with
    | none =>
        have hev' : decEv (shapeOf P B) P a i = Ev.idle := by
          rw [decEv_code hi h, hk,
            show (1 + shS (shapeOf P B) + n - 1 - shS (shapeOf P B)) = n by omega]
          simp [hins, hval]
        have hstep : decStep P B a C i = C := by unfold decStep; rw [hev']
        have hlearn : decLearn (shapeOf P B) P a i = none := by
          rw [decLearn_ded hi h hn ins hins hk, hval]
        refine ⟨?_, ?_⟩
        · rw [hev', hstep]
          exact Rel.rIdle P C
        · rw [hstep]
          exact agrees_of_noact h hi hno hag hlearn
    | some t =>
        have hev' : decEv (shapeOf P B) P a i = Ev.ded t := by
          rw [decEv_code hi h, hk,
            show (1 + shS (shapeOf P B) + n - 1 - shS (shapeOf P B)) = n by omega]
          simp [hins, hval]
        have hstep : decStep P B a C i = succDed C t := by unfold decStep; rw [hev']
        have hlearn : decLearn (shapeOf P B) P a i = some t := by
          rw [decLearn_ded hi h hn ins hins hk, hval]
        obtain ⟨u, hu, him⟩ := mem_dedInsts hins
        have hprem : instPremises (shapeOf P B) ins C.kn := by
          unfold instPremises
          intro p hp
          have hcl : [neg (evDed (shapeOf P B) i n), pos (vkn (shapeOf P B) i p)] ∈
              dedClausesAt (shapeOf P B) i n := by
            rw [dedClausesAt, hins]
            exact List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
          have hsat := sat_ded h _ (mem_ded hi hn hcl)
          simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_false, Bool.false_or, neg_eval, hev,
            Bool.not_true, pos_eval] at hsat
          have hprange : p < (shapeOf P B).U.length := dedInstsOf_prem_lt hu him p hp
          obtain ⟨q, hq⟩ := rget_lt (shapeOf P B).U p hprange
          refine ⟨q, ?_, hq⟩
          rw [hag.2.2.1]
          exact kn_sound h hq i (Nat.le_of_lt hi) hsat
        have hone : OneStep C.kn t := dedInst_oneStep him hprem hval
        refine ⟨?_, ?_⟩
        · rw [hev', hstep]
          exact Rel.rDed hone
        · rw [hstep]
          refine agrees_of_frame h hi hag hno ?_ ?_ ?_ ?_ ?_
          · intro r hr; exact pcOf_succDed C r t
          · intro r x hr hx; exact readVar_succDed C r x t
          · rw [decKnSeq_succ, kn_succDed, hag.2.2.1, hlearn]
            show decKnSeq (shapeOf P B) P a i ++ [t] = decKnSeq (shapeOf P B) P a i ++ [t]
            rfl
          · intro r hr; exact hag.2.2.2.1 r hr
          · rw [sessLength_succDed, hag.2.2.2.2]
