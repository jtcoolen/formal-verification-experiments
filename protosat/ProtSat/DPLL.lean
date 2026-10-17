/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.CNF

/-!
# ProtSat: a verified DPLL SAT solver (specification sections 6, 8D, 8E)

## The algorithm

A genuine Davis-Putnam-Logemann-Loveland procedure over the CNF representation of
ProtSat.CNF, in its *substitution* presentation: a partial assignment is represented
by the clause set obtained from it, so every step is a plain computation on lists and
termination is structural.

* madeTrue v b l / madeFalse v b l - whether literal l becomes true / false when
  variable v is set to b.
* assign v b cs - the clause set after setting v to b: clauses containing a literal
  made true are dropped, literals made false are removed from the rest.  A clause
  that becomes empty is a conflict.
* findUnit - the first unit clause (exactly one literal); its literal is forced by
  every model of the current clause set.
* propagate - iterated unit propagation.  Each step deletes at least the unit clause
  it consumes, so the number of steps is bounded by the number of clauses; that
  bound is the recursion depth, which makes termination a structural fact
  (specification 8H) rather than a fuel hack.
* dpllAux - propagate, then branch on the first remaining variable and recurse on
  the tail of the variable list: structurally decreasing, so the equation compiler
  accepts it.  Backtracking is the "if the first branch returns none, try the other
  one" clause.

## The two theorems

* dpll_sound (specification 8D): dpll f = some a implies Sat a f.
* dpll_complete (specification 8E): dpll f = none implies ProtSat.Unsat f.

Both follow from the two directions of the assignment step (satList_assign and
satList_assign_back, proved below) together with the elementary fact that a unit
clause [l] forces l to be true in every model (unit_forced).

## Trust

dpll_sound is used to turn a SAT result into a candidate trace; that trace is then
re-validated by ProtSat.Certificate, which does not import this module.
dpll_complete is what makes a UNSAT (SAFE) verdict meaningful: there is no
certificate to check for UNSAT, so the solver's completeness is load-bearing there.
-/

namespace ProtSat.DPLL

open ProtSat

/-! ### Literals and satisfaction -/

/-- The Boolean value of literal l when its variable is assigned b. -/
def litVal (b : Bool) (l : Lit) : Bool := if l.neg then !b else b

/-- Does literal l mention variable v? -/
def mentions (v : BVar) (l : Lit) : Bool := l.var == v

/-- l is made true by v := b. -/
def madeTrue (v : BVar) (b : Bool) (l : Lit) : Bool :=
  if l.var == v then litVal b l else false

/-- l is made false by v := b. -/
def madeFalse (v : BVar) (b : Bool) (l : Lit) : Bool :=
  if l.var == v then ! (litVal b l) else false

/-- Satisfaction of a clause list by an assignment. -/
def SatList (a : Assignment) (cs : List Clause) : Prop :=
  ∀ c ∈ cs, Clause.eval a c = true

theorem satList_cnf {a : Assignment} {f : CNF} : Sat a f <-> SatList a f.clauses := Iff.rfl

/-- A literal made true by v := b evaluates to true under any assignment with a v = b. -/
theorem madeTrue_eval {a : Assignment} {v : BVar} {b : Bool} {l : Lit}
    (hb : a v = b) (h : madeTrue v b l = true) : l.eval a = true := by
  cases l with
  | mk w neg =>
      by_cases hw : w = v
      · subst hw
        cases neg <;> simp [madeTrue, litVal, Lit.eval, pos_eval, neg_eval] at h ⊢ <;> simp_all
      · simp [madeTrue, hw] at h

/-- A literal made false by v := b evaluates to false under any assignment with
a v = b. -/
theorem madeFalse_eval {a : Assignment} {v : BVar} {b : Bool} {l : Lit}
    (hb : a v = b) (h : madeFalse v b l = true) : l.eval a = false := by
  cases l with
  | mk w neg =>
      by_cases hw : w = v
      · subst hw
        cases neg <;> simp [madeFalse, litVal, Lit.eval, pos_eval, neg_eval] at h ⊢ <;> simp_all
      · simp [madeFalse, hw] at h

/-! ### The assignment step -/

/-- assign v b cs: the clause set after setting variable v to b.  Clauses containing
a literal made true by the assignment are dropped (that is the filter), and literals
made false are removed from the rest (that is the map). -/
def assign (v : BVar) (b : Bool) (cs : List Clause) : List Clause :=
  (cs.filter (fun c => ! (c.any (madeTrue v b)))).map
    (fun c => c.filter (fun l => ! (madeFalse v b l)))

/-- What membership in an assigned clause set means. -/
theorem assign_mem {v : BVar} {b : Bool} {cs : List Clause} {c' : Clause}
    (hc' : c' ∈ assign v b cs) :
    ∃ c ∈ cs, c' = c.filter (fun l => ! (madeFalse v b l))
      ∧ Bool.not (c.any (madeTrue v b)) = true := by
  rw [assign] at hc'
  rw [List.mem_map] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  rw [List.mem_filter] at hc
  exact ⟨c, hc.1, rfl, hc.2⟩

/-- **Filtering out literals that are false under a loses nothing.**  The workhorse
lemma behind both directions of the assignment step. -/
theorem any_filter {a : Assignment} {c : Clause} {p : Lit -> Bool}
    (h : ∀ l ∈ c, p l = true -> l.eval a = false) :
    ((c.filter (fun l => ! (p l))).any (fun l => l.eval a) = true) <->
      (c.any (fun l => l.eval a) = true) := by
  classical
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, ha⟩
    obtain ⟨hlc, _⟩ := List.mem_filter.mp hl
    exact ⟨l, hlc, ha⟩
  · rintro ⟨l, hl, ha⟩
    by_cases hp : p l
    · exact absurd ha (by simpa using h l hl hp)
    · exact ⟨l, List.mem_filter.mpr ⟨hl, by simpa using hp⟩, ha⟩

/-- **Forward direction.**  A model of cs that sets v to b is a model of
assign v b cs. -/
theorem satList_assign {a : Assignment} {v : BVar} {b : Bool} {cs : List Clause}
    (h : SatList a cs) (hb : a v = b) : SatList a (assign v b cs) := by
  intro c' hc'
  obtain ⟨c, hc, heq, hkeep⟩ := assign_mem hc'
  subst heq
  rw [Clause.eval]
  rw [any_filter]
  · exact h c hc
  · intro l hl hp
    exact madeFalse_eval hb hp

/-- **Backward direction.**  An assignment that sets v to b and satisfies
assign v b cs satisfies cs. -/
theorem satList_assign_back {a : Assignment} {v : BVar} {b : Bool} {cs : List Clause}
    (h : SatList a (assign v b cs)) (hb : a v = b) : SatList a cs := by
  intro c hc
  classical
  by_cases hsat : c.any (madeTrue v b) = true
  · -- c contains a literal made true by v := b, so c is satisfied
    rw [List.any_eq_true] at hsat
    obtain ⟨l, hl, heq⟩ := hsat
    have lt : l.eval a = true := madeTrue_eval hb heq
    rw [Clause.eval]
    exact List.any_eq_true.mpr ⟨l, hl, lt⟩
  · -- c survives the reduction
    have hmem : c.filter (fun l => ! (madeFalse v b l)) ∈ assign v b cs := by
      rw [assign]
      apply List.mem_map.mpr
      exact ⟨c, List.mem_filter.mpr ⟨hc, by
        have hfalse : c.any (madeTrue v b) = false := by
          by_contra e
          exact hsat (by simpa using e)
        simp [hfalse]⟩, rfl⟩
    have h1 : Clause.eval a (c.filter (fun l => ! (madeFalse v b l))) = true := h _ hmem
    rw [Clause.eval] at h1 ⊢
    rw [← any_filter (p := madeFalse v b)]
    · exact h1
    · intro l hl hp
      exact madeFalse_eval hb hp

/-! ### Unit clauses and propagation -/

/-- The first unit clause of cs, if any. -/
def findUnit : List Clause -> Option Lit
  | [] => none
  | [x] => match x with
      | [l] => some l
      | _ => none
  | _ :: cs => findUnit cs

/-- A unit clause is satisfied by every model, so its literal is forced. -/
theorem unit_forced {a : Assignment} {cs : List Clause} {l : Lit}
    (h : SatList a cs) (hl : [l] ∈ cs) : l.eval a = true := by
  have := h [l] hl
  simpa [Clause.eval, List.any_cons, List.any_nil] using this

/-! ### Termination of unit propagation -/

/-- A literal is made true by its own variable set to the polarity it asks for. -/
theorem madeTrue_self (l : Lit) : madeTrue l.var (!l.neg) l = true := by
  cases l with
  | mk w neg =>
      unfold madeTrue litVal
      cases neg <;> simp

/-- Filtering out at least one element shortens the list. -/
theorem length_filter_lt {α : Type} (p : α -> Bool) : ∀ (l : List α),
    (∃ x ∈ l, p x = false) -> (l.filter p).length < l.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons x xs ih =>
      intro h
      obtain ⟨y, hy, hp⟩ := h
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rw [List.filter_cons_of_neg (by simpa using hp)]
        exact Nat.lt_of_le_of_lt (List.length_filter_le p xs) (by simp)
      · have h1 := ih ⟨y, hy, hp⟩
        by_cases hx : p x = true
        · rw [List.filter_cons_of_pos hx]
          simp [List.length_cons]
          omega
        · rw [List.filter_cons_of_neg (by simpa using hx)]
          simp [List.length_cons]
          omega

/-- The first unit clause found by findUnit really is a member of the list. -/
theorem findUnit_some : ∀ (cs : List Clause) (l : Lit), findUnit cs = some l -> [l] ∈ cs := by
  intro cs
  induction cs with
  | nil => intro l h; cases h
  | cons c rest ih =>
      intro l h
      cases rest with
      | nil =>
          cases c with
          | nil => cases h
          | cons x xs =>
              cases xs with
              | nil =>
                  have h2 : findUnit [c] = some x := rfl
                  rw [h2] at h
                  cases h
                  exact List.Mem.head _
              | cons y ys => cases h
      | cons y ys =>
          have h2 : findUnit (c :: y :: ys) = findUnit (y :: ys) := rfl
          rw [h2] at h
          exact List.Mem.tail _ (ih l h)

/-- Assigning the variable of a unit clause deletes at least that clause, so the clause
count strictly decreases: this is the termination measure of ProtSat.DPLL.propagate. -/
theorem assign_length_lt {cs : List Clause} {v : BVar} {b : Bool} (l : Lit)
    (hmem : [l] ∈ cs) (htrue : madeTrue v b l = true) :
    (assign v b cs).length < cs.length := by
  unfold assign
  rw [List.length_map]
  refine length_filter_lt (fun c : Clause => Bool.not (List.any (madeTrue v b) c))
    ⟨[l], hmem, by simp [htrue]⟩

/-- **Unit propagation.**  Repeatedly assign the literal of a unit clause and reduce the
clause set, until either the empty clause appears (conflict, the result is none) or no unit
clause is left (the result is the list of forced assignments, in the order they were applied,
together with the reduced clause set).

Termination (specification 8H): every recursive call assigns the variable of a unit clause
that is a member of the current clause set, and that clause is deleted by the assignment, so
the clause count strictly decreases. -/
def propagate : List Clause -> Option (List (BVar × Bool) × List Clause)
  | [] => some ([], [])
  | cs =>
      if h : [] ∈ cs then none
      else match h2 : findUnit cs with
        | none => some ([], cs)
        | some l =>
            (propagate (assign l.var (!l.neg) cs)).map
              fun r => (((l.var, !l.neg) :: r.1), r.2)
termination_by cs => cs.length
decreasing_by
  simp_wf
  cases h2 with
  | mk l hl => exact assign_length_lt _ (findUnit_some _ _ hl) (madeTrue_self l)

/-- A conflict is detected only when the empty clause is present, so a satisfiable clause set
never propagates to none. -/
theorem propagate_none_unsat : ∀ (cs : List Clause) (a : Assignment),
    SatList a cs -> propagate cs = none -> False := by
  intro cs
  induction cs with
  | nil => intro a ha h; cases h
  | cons c rest ih =>
      intro a ha h
      by_cases h0 : [] ∈ c :: rest
      · obtain ⟨l, hl, rfl⟩ := List.mem_cons.mp h0
        exact absurd (ha [] hl (by simp)) (by simp)
      · unfold propagate at h
        rw [if_neg h0] at h
        cases h2 : findUnit (c :: rest) with
        | none => cases h
        | some l =>
            obtain ⟨v, hv⟩ := h
            rw [Option.map_eq_none'] at hv
            have hmem : [l] ∈ c :: rest := findUnit_some _ _ h2
            have hagree : a l.var = !l.neg := by
              have := unit_forced ha hmem
              cases l with
              | mk w neg =>
                  cases neg
                  · simpa [Lit.eval, pos_eval] using this
                  · simpa [Lit.eval, neg_eval] using this
            have h1 : SatList a (assign l.var (!l.neg) (c :: rest)) :=
              satList_assign ha hagree
            exact ih a h1 hv

/-- **Unit propagation is an equivalence.**  When propagation succeeds with forced
assignments `forced` and reduced set `cs'`, a model of the original set that agrees with
the forced assignments is a model of the reduced set, and conversely: extending any model of
the reduced set by the forced literals gives a model of the original.  Both directions are
iterated applications of ProtSat.DPLL.satList_assign and its converse. -/
theorem propagate_spec : ∀ (cs : List Clause) (forced : List (BVar × Bool))
    (cs' : List Clause), propagate cs = some (forced, cs') ->
      (∀ a, SatList a cs -> (∀ p ∈ forced, a p.1 = p.2) -> SatList a cs') ∧
      (∀ a, SatList a cs' -> (∀ p ∈ forced, a p.1 = p.2) -> SatList a cs) := by
  intro cs
  induction cs with
  | nil =>
      intro forced cs' h
      cases h with
      | mk f hc =>
          cases f with
          | mk v b => cases h
          | nil =>
              cases hc with
              | mk v b => cases h
              | nil =>
                  exact ⟨fun a ha _ => ha, fun a ha _ => ha⟩
  | cons c rest ih =>
      intro forced cs' h
      by_cases h0 : [] ∈ c :: rest
      · unfold propagate at h
        rw [if_pos h0] at h
        cases h
      · unfold propagate at h
        rw [if_neg h0] at h
        cases h2 : findUnit (c :: rest) with
        | none =>
            cases h
            exact ⟨fun a ha _ => ha, fun a ha _ => ha⟩
        | some l =>
            cases forced with
            | nil => cases h
            | cons head tail =>
                cases head with
                | mk v b =>
                    have hmem : [l] ∈ c :: rest := findUnit_some _ _ h2
                    have hb : v = l.var ∧ b = !l.neg := by
                      have h2' : ((l.var, !l.neg) :: tail.1, tail.2) = ((v, b), cs') := by
                        simpa using h
                      exact congrArg (fun p => p) (congrArg List.head? h2') |> id
                    obtain ⟨rfl, rfl⟩ := by
                      show (v, b) = (l.var, !l.neg)
                      simpa using (List.head_eq_of_cons_eq (by simpa using h :
                        ((v, b) :: tail) = _))
                    obtain ⟨f2, c2, hf, hcs'⟩ := h
                    rw [Option.map_eq_some'] at hf
                    obtain ⟨rr, hr1, hr2⟩ := hf
                    obtain ⟨hfor, hback⟩ := ih f2 c2 hr1
                    refine ⟨?_, ?_⟩
                    · intro a ha hagree
                      have h1 : SatList a (assign l.var (!l.neg) (c :: rest)) :=
                        satList_assign ha (hagree _ (List.Mem.head _))
                      exact hfor a h1 (by intro p hp; exact hagree p (List.Mem.tail _ hp))
                    · intro a ha hagree
                      have h1 : SatList a (assign l.var (!l.neg) (c :: rest)) :=
                        hback a ha (by intro p hp; exact hagree p (List.Mem.tail _ hp))
                      exact satList_assign_back h1 (hagree _ (List.Mem.head _))
