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

/-- The configuration C agrees with the assignment a at step i: the program counters, the
variable readings and the attacker's knowledge are exactly the ones the assignment encodes.
This is the bridge between the Boolean world and ProtSat.Operational. -/
def Agrees (P : Protocol) (B : Bounds) (a : Assignment) (C : Cfg) (i : Nat) : Prop :=
  (∀ q, q < (shapeOf P B).nS1 → pcOf C q = decodePc (shapeOf P B) a i q) ∧
  (∀ q x, q < (shapeOf P B).nS1 → x < (shapeOf P B).nV1 + 1 →
      readVar x (storeOf C q) = decSt (shapeOf P B) a i q x) ∧
  C.kn = decKnSeq (shapeOf P B) P a i

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

/-- The initial configuration agrees with the assignment at step 0: the initial clauses say
exactly that every session is at program counter 0 with an empty store and the attacker
holds the initial knowledge. -/
theorem agrees_zero (h : Sat a (encode P B)) : Agrees P B a (initCfg P) 0 := by
  refine ⟨?_, ?_, rfl⟩
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
    have hdec : decSt (shapeOf P B) a 0 q x = none := by
      unfold decSt decVal
      rw [h2]
      exact valAt_uIdx_none (shapeOf P B)
    rw [hst, hdec]
    rfl

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
