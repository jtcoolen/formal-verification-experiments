/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.CNF
import Mathlib.Data.Option.Basic

/-!
# ProtSat: a verified DPLL SAT solver (specification sections 6, 8D, 8E, 8H)

## The algorithm

A genuine Davis-Putnam-Logemann-Loveland procedure over the propositional representation
of ProtSat.CNF, in its *substitution* presentation: setting a variable replaces the clause
set by the clause set of the restricted formula, so every step is a plain computation on
lists and every lemma below is about lists.

* madeTrue v b l / madeFalse v b l - whether literal l becomes true / false under v := b.
* assign v b cs - the clause set after v := b: clauses with a literal made true are
  dropped, literals made false are deleted from the rest.  A clause that loses all its
  literals becomes the empty clause, which is how a *conflict* is represented.
* findUnit - the first unit clause; its literal is true in every model of the set, so
  assigning it loses no model (unit_forced).
* propagate - iterated unit propagation, written with an explicit fuel equal to the number
  of clauses.  Every propagation step deletes at least the unit clause it consumes
  (assign_length_lt), so the fuel always suffices to reach a fixpoint (propagate_noUnit):
  termination is structural, as specification 8H requires.
* dpllAux cs vs asg - propagate, then branch on the first still-undecided variable of vs
  and recurse on the tail.  *Backtracking* is the "if the first polarity returns none, try
  the other one" clause.  Recursion is structural on vs.
* dpll f - dpllAux at the variable list of f (duplicates removed) and the empty decision
  list.

## The two theorems (specification 8D and 8E)

* dpll_sound : dpll f = some asg -> Sat (asgVal asg) f.
  If DPLL returns SAT, the assignment it returns satisfies the CNF.
* dpll_complete : dpll f = none -> Unsat f.
  If DPLL returns UNSAT, the CNF really is unsatisfiable.

Both are consequences of exactly two facts, each proved once and then iterated:

* satList_assign / satList_assign_back - restriction is an equivalence between the models
  of the restricted set that agree with the decision and the models of the original set;
* unit_forced - a unit clause is satisfied by every model.

## Trust

dpll_sound is what turns a SAT verdict into a candidate trace; that trace is then
re-validated by ProtSat.Certificate, which does not import this module at all.
dpll_complete is what makes a SAFE verdict meaningful: there is no certificate to check
for UNSAT, so the solver's completeness is the only thing standing between "the solver
found nothing" and "there is nothing to find" (specification 8G).
-/

namespace ProtSat.DPLL

open ProtSat

/-! ### 1. Literals and the restriction step -/

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

/-- Satisfaction of a clause list by an assignment: every clause has a true literal.
This is ProtSat.Sat without the CNF wrapper, which keeps the statements below readable. -/
def SatList (a : Assignment) (cs : List Clause) : Prop :=
  ∀ c ∈ cs, Clause.eval a c = true

/-- The two presentations agree. -/
theorem satList_cnf {a : Assignment} {f : CNF} : Sat a f <-> SatList a f.clauses := Iff.rfl

/-- A literal made true by v := b evaluates to true under any assignment with a v = b. -/
theorem madeTrue_eval {a : Assignment} {v : BVar} {b : Bool} {l : Lit}
    (hb : a v = b) (h : madeTrue v b l = true) : l.eval a = true := by
  cases l with
  | mk w neg =>
      by_cases hw : w = v
      · subst hw
        cases neg <;> simp [madeTrue, litVal, Lit.eval] at h ⊢ <;> simp_all
      · simp [madeTrue, hw] at h

/-- A literal made false by v := b evaluates to false under any assignment with a v = b. -/
theorem madeFalse_eval {a : Assignment} {v : BVar} {b : Bool} {l : Lit}
    (hb : a v = b) (h : madeFalse v b l = true) : l.eval a = false := by
  cases l with
  | mk w neg =>
      by_cases hw : w = v
      · subst hw
        cases neg <;> simp [madeFalse, litVal, Lit.eval] at h ⊢ <;> simp_all
      · simp [madeFalse, hw] at h

/-- **Restriction.** assign v b cs is the clause set of the formula obtained from cs by
setting v := b: a clause with a literal made true is satisfied and disappears, and in the
remaining clauses the literals made false are removed (a clause that loses all its
literals becomes the empty clause, i.e. a conflict). -/
def assign (v : BVar) (b : Bool) (cs : List Clause) : List Clause :=
  (cs.filter (fun c => ! (c.any (madeTrue v b)))).map
    (fun c => c.filter (fun l => ! (madeFalse v b l)))

/-- What membership in a restricted clause set means: it comes from a surviving clause. -/
theorem assign_mem {v : BVar} {b : Bool} {cs : List Clause} {c' : Clause}
    (hc' : c' ∈ assign v b cs) :
    ∃ c ∈ cs, c' = c.filter (fun l => ! (madeFalse v b l))
      ∧ Bool.not (c.any (madeTrue v b)) = true := by
  rw [assign] at hc'
  rw [List.mem_map] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  rw [List.mem_filter] at hc
  exact ⟨c, hc.1, rfl, hc.2⟩

/-- **Deleting literals that are false under a changes no clause's value.**  The workhorse
lemma behind both directions of the restriction step. -/
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

/-- **Restriction is sound.**  A model of cs that sets v to b is a model of assign v b cs.
This direction is what the *completeness* of DPLL (8E) uses: a model of the original
problem survives into the branch it belongs to. -/
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

/-- **Restriction is complete.**  An assignment that sets v to b and satisfies
assign v b cs satisfies cs.  This is the direction the *soundness* of DPLL (8D) needs: a
model of the restricted problem lifts to a model of the original one. -/
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
  · -- c survives the restriction
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

/-- Restricting drops at least the clauses that are already satisfied, so the clause count
never grows; and it never grows the set of variables. -/
theorem length_assign_le (v : BVar) (b : Bool) (cs : List Clause) :
    (assign v b cs).length ≤ cs.length := by
  unfold assign
  rw [List.length_map]
  exact List.length_filter_le _ _

/-! ### 2. Unit clauses -/

/-- The literal of a unit clause, if the clause is a unit clause. -/
def unitLit : Clause -> Option Lit
  | [l] => some l
  | _ => none

/-- A clause whose unitLit is some l is exactly the singleton clause [l]. -/
theorem unitLit_some {c : Clause} {l : Lit} (h : unitLit c = some l) : c = [l] := by
  cases c with
  | nil => cases h
  | cons x xs =>
      cases xs with
      | nil => simpa [unitLit] using h
      | cons y ys => cases h

/-- Every Option is none or some: the case split we are allowed to do on a definition
application without confusing the dependent-elimination machinery. -/
theorem option_cases {α : Type} (o : Option α) : o = none ∨ ∃ a, o = some a := by
  cases h : o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

/-- The first unit clause of a clause list. -/
def findUnit : List Clause -> Option Lit
  | [] => none
  | c :: cs => match unitLit c with
    | some l => some l
    | none => findUnit cs

/-- If findUnit succeeds, the unit clause really is a member of the list. -/
theorem findUnit_some : ∀ (cs : List Clause) (l : Lit), findUnit cs = some l -> [l] ∈ cs := by
  intro cs
  induction cs with
  | nil => intro l h; cases h
  | cons c rest ih =>
      intro l h
      have h2 : findUnit (c :: rest) =
          match unitLit c with
          | some l' => some l'
          | none => findUnit rest := rfl
      rw [h2] at h
      cases h1 : unitLit c with
      | some l' =>
          rw [h1] at h
          have hl' : l' = l := by simpa using h
          have hc : c = [l'] := unitLit_some h1
          rw [hc, hl']
          exact List.Mem.head _
      | none =>
          rw [h1] at h
          exact List.Mem.tail _ (ih l h)

/-- No unit clause means no clause is a unit clause. -/
theorem findUnit_none : ∀ (cs : List Clause), findUnit cs = none ->
    ∀ c ∈ cs, unitLit c = none := by
  intro cs
  induction cs with
  | nil => intro h c hc; cases hc
  | cons c rest ih =>
      intro h x hx
      rw [List.mem_cons] at hx
      have h2 : findUnit (c :: rest) = match unitLit c with
          | some l => some l
          | none => findUnit rest := rfl
      rw [h2] at h
      rcases option_cases (unitLit c) with hun | ⟨l, hun⟩
      · have hrest : findUnit rest = none := by simpa [hun] using h
        rcases hx with hxeq | hx
        · subst hxeq
          exact hun
        · exact ih hrest x hx
      · rw [hun] at h
        cases h

/-- Mapping over an Option: if the result is some b, the preimage was some a with f a = b. -/
theorem option_map_some {α β : Type} (f : α -> β) {o : Option α} {b : β}
    (h : Option.map f o = some b) : ∃ a, o = some a ∧ f a = b :=
  match o with
  | none => by cases h
  | some a => ⟨a, rfl, Option.some.inj h⟩

/-- The two ways findUnit can end, with the membership fact attached.  Having this as a
single lemma is what keeps the case splits below out of dependent-elimination trouble. -/
theorem findUnit_cases (cs : List Clause) :
    findUnit cs = none ∨ ∃ l, findUnit cs = some l ∧ [l] ∈ cs := by
  cases h : findUnit cs with
  | none => exact Or.inl rfl
  | some l => exact Or.inr ⟨l, rfl, findUnit_some cs l h⟩

/-- The value a model must give to the variable of a satisfied literal. -/
theorem lit_eval_iff (a : Assignment) (l : Lit) : l.eval a = true <-> a l.var = !l.neg := by
  cases l with
  | mk v neg =>
      cases neg
      · simp [Lit.eval]
      · simp [Lit.eval]

/-- **A unit clause is forced.**  Every model of the clause set satisfies the literal of a
unit clause; this is the correctness property of unit propagation. -/
theorem unit_forced {a : Assignment} {cs : List Clause} {l : Lit}
    (h : SatList a cs) (hl : [l] ∈ cs) : l.eval a = true := by
  have := h [l] hl
  simpa [Clause.eval, List.any_cons, List.any_nil] using this

/-! ### 3. The variables of a clause set -/

/-- The variables occurring in a clause list, duplicates kept: only membership is ever
used. -/
def litVars : List Clause -> List BVar
  | [] => []
  | c :: cs => c.map Lit.var ++ litVars cs

/-- Reading a variable out of a clause list is the same as reading it out of one of the
clauses. -/
theorem mem_litVars {cs : List Clause} {u : BVar} :
    u ∈ litVars cs <-> ∃ c ∈ cs, u ∈ c.map Lit.var := by
  induction cs with
  | nil => simp [litVars]
  | cons c rest ih =>
      simp only [litVars, List.mem_append, ih]
      constructor
      · rintro (h | h)
        · exact ⟨c, List.Mem.head _, h⟩
        · obtain ⟨c', hc', h⟩ := h; exact ⟨c', List.Mem.tail _ hc', h⟩
      · rintro ⟨c', hc', h⟩
        rw [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · left; exact h
        · right; exact ⟨c', hc', h⟩

/-- A clause that has a literal contributes that literal's variable. -/
theorem mem_litVars_of_mem {cs : List Clause} {c : Clause} (hc : c ∈ cs) {l : Lit}
    (hl : l ∈ c) : l.var ∈ litVars cs := by
  rw [mem_litVars]
  exact ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-- A literal on v is made true exactly when it is not made false: under v := b a literal
has only two possible fates. -/
theorem madeTrue_iff_not_madeFalse (v : BVar) (b : Bool) (l : Lit) (hl : l.var = v) :
    madeTrue v b l = true <-> Bool.not (madeFalse v b l) = true := by
  cases l with
  | mk w neg =>
      subst hl
      cases neg <;> cases b <;> simp [madeTrue, madeFalse, litVal]

/-- Restriction only ever removes variables, and it always removes the variable it
restricts. -/
theorem mem_litVars_assign {v : BVar} {b : Bool} {cs : List Clause} {u : BVar}
    (hu : u ∈ litVars (assign v b cs)) : u ∈ litVars cs ∧ u ≠ v := by
  obtain ⟨c', hc', hc''⟩ := mem_litVars.mp hu
  obtain ⟨c, hc, heq, hkeep⟩ := assign_mem hc'
  rw [heq] at hc''
  obtain ⟨l, hl, hvar⟩ := List.mem_map.mp hc''
  rw [List.mem_filter] at hl
  refine ⟨?_, ?_⟩
  · rw [mem_litVars]
    exact ⟨c, hc, List.mem_map.mpr ⟨l, hl.1, hvar⟩⟩
  · by_cases hv : l.var = v
    · -- l.var = v and l survived the restriction, so l is true under v := b, so its clause
      -- would have been deleted by the restriction instead.
      have hmt : madeTrue v b l = true := (madeTrue_iff_not_madeFalse v b l hv).mpr hl.2
      have hany : c.any (madeTrue v b) = true := List.any_eq_true.mpr ⟨l, hl.1, hmt⟩
      simp [hany] at hkeep
    · intro h
      exact absurd (hvar.trans h) hv

/-! ### 4. Unit propagation -/

/-- One fuelled step of unit propagation: if the empty clause is present the branch is a
conflict (none); if a unit clause is present its literal is forced and propagation
continues on the restricted set with one unit of fuel spent; otherwise a fixpoint has been
reached and the result is the decisions taken so far together with the reduced clause set.

The fuel is not a soundness device: every propagation step deletes at least the unit clause
it consumes (assign_length_lt), so the fuel cs.length always suffices (propagate_noUnit).
Writing it as an explicit parameter is what makes the recursion - and hence every lemma
about it - structural, which is what specification 8H asks for. -/
def propagateGo : Nat -> List Clause -> Option (List (BVar × Bool) × List Clause)
  | 0, cs => if [] ∈ cs then none else some ([], cs)
  | n + 1, cs =>
      if [] ∈ cs then none
      else match findUnit cs with
        | none => some ([], cs)
        | some l => (propagateGo n (assign l.var (!l.neg) cs)).map
              fun r => ((l.var, !l.neg) :: r.1, r.2)

/-- Propagation with the fuel that is always enough: the number of clauses. -/
def propagate (cs : List Clause) : Option (List (BVar × Bool) × List Clause) :=
  propagateGo cs.length cs

@[simp] theorem propagateGo_zero (cs : List Clause) :
    propagateGo 0 cs = if [] ∈ cs then none else some ([], cs) := rfl

@[simp] theorem propagateGo_succ (n : Nat) (cs : List Clause) :
    propagateGo (n + 1) cs =
      if [] ∈ cs then none
      else match findUnit cs with
        | none => some ([], cs)
        | some l => (propagateGo n (assign l.var (!l.neg) cs)).map
              fun r => ((l.var, !l.neg) :: r.1, r.2) := rfl

@[simp] theorem propagate_eq (cs : List Clause) :
    propagate cs = propagateGo cs.length cs := rfl

/-- A literal is made true by its own variable set to the polarity it asks for. -/
theorem madeTrue_self (l : Lit) : madeTrue l.var (!l.neg) l = true := by
  simp [madeTrue, litVal]

/-- Filtering out at least one element shortens the list. -/
theorem length_filter_lt {alpha : Type} (p : alpha -> Bool) : ∀ (l : List alpha),
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
          simp only [List.length_cons]
          omega
        · rw [List.filter_cons_of_neg (by simpa using hx)]
          simp only [List.length_cons]
          omega

/-- **Each propagation step deletes a clause.**  This is the termination measure of unit
propagation (specification 8H). -/
theorem assign_length_lt {cs : List Clause} {v : BVar} {b : Bool} (l : Lit)
    (hmem : [l] ∈ cs) (htrue : madeTrue v b l = true) :
    (assign v b cs).length < cs.length := by
  unfold assign
  rw [List.length_map]
  refine length_filter_lt (fun c : Clause => Bool.not (c.any (madeTrue v b))) cs
    ⟨[l], hmem, by simp [htrue]⟩


/-- **Conflict detection is sound.**  If propagation reports a conflict then the clause set
has no model at all: either the empty clause is present (a clause has been falsified
completely), or restricting by a forced literal already leaves no model. -/
theorem propagateGo_none_unsat : ∀ (n : Nat) (cs : List Clause),
    propagateGo n cs = none -> ¬ ∃ a : Assignment, SatList a cs := by
  intro n
  induction n with
  | zero =>
      intro cs h
      by_cases h0 : [] ∈ cs
      · rintro ⟨a, ha⟩
        exact absurd (ha [] h0) (by simp [Clause.eval])
      · rw [propagateGo_zero, if_neg h0] at h
        cases h
  | succ n ih =>
      intro cs h
      by_cases h0 : [] ∈ cs
      · rintro ⟨a, ha⟩
        exact absurd (ha [] h0) (by simp [Clause.eval])
      · rw [propagateGo_succ, if_neg h0] at h
        rcases findUnit_cases cs with hfu | ⟨l, hfu, hmem⟩
        · simp only [hfu] at h
          cases h
        · simp only [hfu] at h
          rcases option_cases (propagateGo n (assign l.var (!l.neg) cs)) with hnone | ⟨r, hr⟩
          · intro ⟨a, ha⟩
            have hv : a l.var = !l.neg := by
              rw [← lit_eval_iff]
              exact unit_forced ha hmem
            exact ih (assign l.var (!l.neg) cs) hnone ⟨a, satList_assign ha hv⟩
          · rw [hr] at h
            cases h

/-- **Unit propagation is a model equivalence.**  When propagation succeeds with decisions
forced and reduced set cs':
* back: a model of cs' that agrees with the decisions is a model of cs;
* fwd: a model of cs is a model of cs';
* agr: a model of cs agrees with the decisions.
Together: the models of cs are *exactly* the models of cs' that agree with forced.  This is
the whole content of unit propagation; everything else in this module is built from it
together with satList_assign / satList_assign_back. -/
theorem propagateGo_spec : ∀ (n : Nat) (cs : List Clause) (forced : List (BVar × Bool))
    (cs' : List Clause), propagateGo n cs = some (forced, cs') ->
      (∀ a, SatList a cs' -> (∀ p ∈ forced, a p.1 = p.2) -> SatList a cs) ∧
      (∀ a, SatList a cs -> SatList a cs') ∧
      (∀ a, SatList a cs -> ∀ p ∈ forced, a p.1 = p.2) := by
  intro n
  induction n with
  | zero =>
      intro cs forced cs' h
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_zero, if_pos h0] at h; cases h
      · rw [propagateGo_zero, if_neg h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨fun a ha _ => ha, fun a ha => ha,
          fun _ _ p hp => absurd hp (by intro h; cases h)⟩
  | succ n ih =>
      intro cs forced cs' h
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_succ, if_pos h0] at h; cases h
      · rw [propagateGo_succ, if_neg h0] at h
        rcases findUnit_cases cs with hfu | ⟨l, hfu, hmem⟩
        · simp only [hfu] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨fun a ha _ => ha, fun a ha => ha,
            fun _ _ p hp => absurd hp (by intro h; cases h)⟩
        · simp only [hfu] at h
          obtain ⟨rr, hrr, heq⟩ := option_map_some _ h
          obtain ⟨hf, hc2⟩ := Prod.mk.inj heq
          subst hf
          subst hc2
          obtain ⟨back, fwd, agr⟩ := ih _ rr.1 rr.2 hrr
          have hforced : ∀ a, SatList a cs -> a l.var = !l.neg := by
            intro a ha
            rw [← lit_eval_iff]
            exact unit_forced ha hmem
          refine ⟨?_, ?_, ?_⟩
          · -- lift a model of the reduced set through this restriction step
            intro a ha hagree
            have h1 : SatList a (assign l.var (!l.neg) cs) :=
              back a ha (by intro p hp; exact hagree p (List.Mem.tail _ hp))
            exact satList_assign_back h1 (hagree (l.var, !l.neg) (List.Mem.head _))
          · -- restrict a model of cs and appeal to the induction hypothesis
            intro a ha
            exact fwd a (satList_assign ha (hforced a ha))
          · intro a ha p hp
            rw [List.mem_cons] at hp
            rcases hp with hpeq | hp
            · subst hpeq
              exact hforced a ha
            · exact agr a (satList_assign ha (hforced a ha)) p hp

/-- **Variable bookkeeping for propagation.**  The reduced set uses only variables of the
original set; none of the decided variables occurs in the reduced set (this is what keeps
the decision list consistent); every decided variable did occur in the original set; the
decisions are mutually consistent; and no empty clause survives. -/
theorem propagateGo_vars : ∀ (n : Nat) (cs : List Clause) (forced : List (BVar × Bool))
    (cs' : List Clause), propagateGo n cs = some (forced, cs') ->
      (∀ v ∈ litVars cs', v ∈ litVars cs) ∧
      (∀ v ∈ litVars cs', ∀ p ∈ forced, p.1 ≠ v) ∧
      (∀ p ∈ forced, p.1 ∈ litVars cs) ∧
      (∀ p ∈ forced, ∀ q ∈ forced, p.1 = q.1 -> p.2 = q.2) ∧
      [] ∉ cs' := by
  intro n
  induction n with
  | zero =>
      intro cs forced cs' h
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_zero, if_pos h0] at h; cases h
      · rw [propagateGo_zero, if_neg h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨fun _ hx => hx, fun _ _ _ hp => absurd hp (by intro h; cases h),
          fun p hp => absurd hp (by intro h; cases h),
          fun p hp _ _ _ => absurd hp (by intro h; cases h), h0⟩
  | succ n ih =>
      intro cs forced cs' h
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_succ, if_pos h0] at h; cases h
      · rw [propagateGo_succ, if_neg h0] at h
        rcases findUnit_cases cs with hfu | ⟨l, hfu, hmem⟩
        · simp only [hfu] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨fun _ hx => hx, fun _ _ _ hp => absurd hp (by intro h; cases h),
            fun p hp => absurd hp (by intro h; cases h),
            fun p hp _ _ _ => absurd hp (by intro h; cases h), h0⟩
        · simp only [hfu] at h
          obtain ⟨rr, hrr, heq⟩ := option_map_some _ h
          obtain ⟨hf, hc2⟩ := Prod.mk.inj heq
          subst hf
          subst hc2
          obtain ⟨sub, disj, occ, consf, nonil⟩ := ih _ rr.1 rr.2 hrr
          have hlvar : l.var ∈ litVars cs := mem_litVars_of_mem hmem (by simp)
          have hassign : ∀ u ∈ litVars (assign l.var (!l.neg) cs),
              u ∈ litVars cs ∧ u ≠ l.var := fun u hu => mem_litVars_assign hu
          refine ⟨?_, ?_, ?_, ?_, nonil⟩
          · intro u hu
            exact (hassign u (sub u hu)).1
          · intro u hu p hp
            rw [List.mem_cons] at hp
            rcases hp with hpeq | hp
            · subst hpeq
              exact Ne.symm (hassign u (sub u hu)).2
            · exact disj u hu p hp
          · intro p hp
            rw [List.mem_cons] at hp
            rcases hp with hpeq | hp
            · subst hpeq
              exact hlvar
            · exact (hassign p.1 (occ p hp)).1
          · intro p hp q hq hvar
            rw [List.mem_cons] at hp hq
            rcases hp with hpeq | hp
            · subst hpeq
              rcases hq with hqeq | hq
              · subst hqeq
                rfl
              · exact absurd hvar (Ne.symm ((hassign q.1 (occ q hq)).2))
            · rcases hq with hqeq | hq
              · subst hqeq
                exact absurd hvar ((hassign p.1 (occ p hp)).2)
              · exact consf p hp q hq hvar

/-- The propagate-level corollaries, at fuel cs.length. -/
theorem propagate_back {cs : List Clause} {forced : List (BVar × Bool)} {cs' : List Clause}
    (h : propagate cs = some (forced, cs')) :
    ∀ a, SatList a cs' -> (∀ p ∈ forced, a p.1 = p.2) -> SatList a cs :=
    (propagateGo_spec cs.length cs forced cs' h).1

theorem propagate_fwd {cs : List Clause} {forced : List (BVar × Bool)} {cs' : List Clause}
    (h : propagate cs = some (forced, cs')) :
    ∀ a, SatList a cs -> SatList a cs' := (propagateGo_spec cs.length cs forced cs' h).2.1

theorem propagate_agr {cs : List Clause} {forced : List (BVar × Bool)} {cs' : List Clause}
    (h : propagate cs = some (forced, cs')) :
    ∀ a, SatList a cs -> ∀ p ∈ forced, a p.1 = p.2 :=
    (propagateGo_spec cs.length cs forced cs' h).2.2

theorem propagate_none_unsat {cs : List Clause} (h : propagate cs = none) :
    ¬ ∃ a : Assignment, SatList a cs := propagateGo_none_unsat cs.length cs h

theorem propagate_vars {cs : List Clause} {forced : List (BVar × Bool)} {cs' : List Clause}
    (h : propagate cs = some (forced, cs')) :
    (∀ v ∈ litVars cs', v ∈ litVars cs) ∧
      (∀ v ∈ litVars cs', ∀ p ∈ forced, p.1 ≠ v) ∧
      (∀ p ∈ forced, p.1 ∈ litVars cs) ∧
      (∀ p ∈ forced, ∀ q ∈ forced, p.1 = q.1 -> p.2 = q.2) ∧ [] ∉ cs' :=
    propagateGo_vars cs.length cs forced cs' h

/-- Each propagation step deletes at least one clause, so the number of decisions plus the
number of surviving clauses never exceeds the original number of clauses. -/
theorem propagateGo_length_le : ∀ (n : Nat) (cs : List Clause) (forced : List (BVar × Bool))
    (cs' : List Clause), propagateGo n cs = some (forced, cs') ->
    cs'.length + forced.length ≤ cs.length := by
  intro n
  induction n with
  | zero =>
      intro cs forced cs' h
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_zero, if_pos h0] at h; cases h
      · rw [propagateGo_zero, if_neg h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        simp
  | succ n ih =>
      intro cs forced cs' h
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_succ, if_pos h0] at h; cases h
      · rw [propagateGo_succ, if_neg h0] at h
        rcases findUnit_cases cs with hfu | ⟨l, hfu, hmem⟩
        · simp only [hfu] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          simp
        · simp only [hfu] at h
          obtain ⟨rr, hrr, heq⟩ := option_map_some _ h
          obtain ⟨hf, hc2⟩ := Prod.mk.inj heq
          subst hf
          subst hc2
          have hlt : (assign l.var (!l.neg) cs).length < cs.length :=
            assign_length_lt l hmem (madeTrue_self l)
          have := ih _ rr.1 rr.2 hrr
          simp only [List.length_cons] at this ⊢
          omega

/-- **The fuel always suffices: propagation saturates.**  If the decisions taken use up
strictly less fuel than was available then no unit clause survives; with the fuel
cs.length this always holds, because each decision deletes a clause. -/
theorem propagateGo_noUnit : ∀ (n : Nat) (cs : List Clause) (forced : List (BVar × Bool))
    (cs' : List Clause), propagateGo n cs = some (forced, cs') ->
    forced.length < n -> ∀ c ∈ cs', unitLit c = none := by
  intro n
  induction n with
  | zero => intro cs forced cs' h hlt; exact absurd hlt (by omega)
  | succ n ih =>
      intro cs forced cs' h hlt
      by_cases h0 : [] ∈ cs
      · rw [propagateGo_succ, if_pos h0] at h; cases h
      · rw [propagateGo_succ, if_neg h0] at h
        rcases findUnit_cases cs with hfu | ⟨l, hfu, hmem⟩
        · simp only [hfu] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact findUnit_none _ hfu
        · simp only [hfu] at h
          obtain ⟨rr, hrr, heq⟩ := option_map_some _ h
          obtain ⟨hf, hc2⟩ := Prod.mk.inj heq
          subst hf
          subst hc2
          simp only [List.length_cons] at hlt
          exact ih _ rr.1 rr.2 hrr (by omega)

/-- No unit clause survives ProtSat.DPLL.propagate: the fuel cs.length is always enough,
because every propagation step deletes at least one clause (assign_length_lt), so the
number of decisions is bounded by the number of clauses.  This is the saturation half of
specification 8H for the propagation phase. -/
theorem propagate_noUnit {cs : List Clause} {forced : List (BVar × Bool)} {cs' : List Clause}
    (h : propagate cs = some (forced, cs')) : ∀ c ∈ cs', unitLit c = none := by
  have hlen := propagateGo_length_le cs.length cs forced cs' h
  by_cases hlt : forced.length < cs.length
  · exact propagateGo_noUnit cs.length cs forced cs' h hlt
  · -- all the fuel was spent, so every clause was deleted: cs' is empty
    cases cs' with
    | nil => intro c hc; cases hc
    | cons x xs =>
        have hlen' := propagateGo_length_le cs.length cs forced (x :: xs) h
        simp only [List.length_cons] at hlen'
        omega

/-! ### 5. Decision lists and the assignment they denote -/

/-- A decision list is consistent when no variable is decided twice with different values.
The invariants maintained by dpllAux below make this true of every list the solver returns,
which is what lets a returned list denote an assignment at all. -/
def Consistent (asg : List (BVar × Bool)) : Prop :=
  ∀ p ∈ asg, ∀ q ∈ asg, p.1 = q.1 → p.2 = q.2

/-- The total assignment denoted by a decision list: the first decision for a variable wins
and undecided variables are false. -/
def asgVal : List (BVar × Bool) -> BVar -> Bool
  | [], _ => false
  | (w, b) :: rest, v => if v = w then b else asgVal rest v

theorem asgVal_cons_eq (v : BVar) (b : Bool) (rest : List (BVar × Bool)) :
    asgVal ((v, b) :: rest) v = b := by
  simp [asgVal]

theorem asgVal_cons_ne {w v : BVar} {b : Bool} (rest : List (BVar × Bool)) (h : v ≠ w) :
    asgVal ((w, b) :: rest) v = asgVal rest v := by
  rw [asgVal, if_neg h]

/-- A consistent decision list denotes an assignment that respects all of its decisions. -/
theorem asgVal_mem : ∀ (asg : List (BVar × Bool)) (v : BVar) (b : Bool),
    (v, b) ∈ asg -> Consistent asg -> asgVal asg v = b := by
  intro asg
  induction asg with
  | nil => intro v b h _; cases h
  | cons p rest ih =>
      intro v b hp hc
      obtain ⟨w, c⟩ := p
      rw [List.mem_cons] at hp
      rcases hp with hpeq | hp
      · obtain ⟨rfl, rfl⟩ := hpeq
        exact asgVal_cons_eq v b rest
      · have hi := ih v b hp (by
          intro x hx y hy hxy
          exact hc x (List.Mem.tail _ hx) y (List.Mem.tail _ hy) hxy)
        by_cases hvw : v = w
        · have hc' : c = b :=
            hc (w, c) (List.Mem.head _) (v, b) (List.Mem.tail _ hp) (by rw [hvw])
          rw [hvw]
          exact (asgVal_cons_eq w c rest).trans hc'
        · exact asgVal_cons_ne rest hvw |>.trans hi

/-- Appending two consistent decision lists whose variable sets are disjoint is consistent. -/
theorem consistent_append {x y : List (BVar × Bool)} (hx : Consistent x) (hy : Consistent y)
    (hd : ∀ p ∈ x, ∀ q ∈ y, p.1 ≠ q.1) : Consistent (x ++ y) := by
  intro p hp q hq hvar
  rw [List.mem_append] at hp hq
  rcases hp with hpx | hpy
  · rcases hq with hqx | hqy
    · exact hx p hpx q hqx hvar
    · exact absurd hvar (hd p hpx q hqy)
  · rcases hq with hqx | hqy
    · exact absurd hvar.symm (hd q hqx p hpy)
    · exact hy p hpy q hqy hvar

/-- Adding a decision for a variable that is not yet decided preserves consistency. -/
theorem consistent_cons {v : BVar} {b : Bool} {asg : List (BVar × Bool)} (h : Consistent asg)
    (hv : ∀ q ∈ asg, q.1 ≠ v) : Consistent ((v, b) :: asg) := by
  intro p hp q hq hvar
  rw [List.mem_cons] at hp hq
  rcases hp with hpeq | hp
  · subst hpeq
    rcases hq with hqeq | hq
    · subst hqeq
      rfl
    · exact absurd hvar (Ne.symm (hv q hq))
  · rcases hq with hqeq | hq
    · subst hqeq
      exact absurd hvar (hv p hp)
    · exact h p hp q hq hvar

/-- **No variable of the clause set is already decided.**  This invariant is what makes the
decision list consistent: neither propagation nor branching ever decides a variable twice,
because a restriction deletes every literal of the variable it decides. -/
def NoAssigned (cs : List Clause) (asg : List (BVar × Bool)) : Prop :=
  ∀ v ∈ litVars cs, ∀ p ∈ asg, p.1 ≠ v

/-- **Every variable of the clause set is available as a branching variable.**  This is what
makes UNSAT results meaningful: when the solver has branched on all of vs and still has an
unsatisfied clause left, that clause can only be the empty clause. -/
def VarsIn (cs : List Clause) (vs : List BVar) : Prop :=
  ∀ v ∈ litVars cs, v ∈ vs

/-- The variables decided by a decision list. -/
def decVars (asg : List (BVar × Bool)) : List BVar := asg.map Prod.fst

theorem mem_decVars {asg : List (BVar × Bool)} {v : BVar} :
    v ∈ decVars asg ↔ ∃ b, (v, b) ∈ asg := by
  rw [decVars, List.mem_map]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨w, b⟩ := p
    have hw : w = v := by simpa using h
    subst hw
    exact ⟨b, hp⟩
  · rintro ⟨b, hb⟩
    exact ⟨(v, b), hb, rfl⟩

/-! ### 6. The solver -/

/-- **The DPLL search.**  dpllAux cs vs asg searches for a model of the clause set cs,
having already decided asg, using the variables in vs as branching candidates.

At each step:
1. unit propagation reduces cs to cs' and adds the forced decisions (conflict: none);
2. if no branching variable is left, cs' must be empty for the branch to succeed;
3. otherwise the first variable of vs that is still undecided is branched on: the true
   polarity is tried first and the false polarity only if it fails - that is backtracking.

Recursion is structural on vs, so the solver terminates by construction (specification 8H).
The list asg is the accumulated decisions; the caller guarantees that no clause of cs
mentions a decided variable (NoAssigned) and that every variable of cs is in vs (VarsIn). -/
def dpllAux : List Clause -> List BVar -> List (BVar × Bool) -> Option (List (BVar × Bool))
  | cs, [], asg =>
      match propagate cs with
      | none => none
      | some (forced, cs') => if cs' = [] then some (forced ++ asg) else none
  | cs, v :: rest, asg =>
      match propagate cs with
      | none => none
      | some (forced, cs') =>
          if v ∈ decVars (forced ++ asg) then dpllAux cs' rest (forced ++ asg)
          else match dpllAux (assign v true cs') rest ((v, true) :: forced ++ asg) with
               | some r => some r
               | none => dpllAux (assign v false cs') rest ((v, false) :: forced ++ asg)

theorem dpllAux_nil (cs : List Clause) (asg : List (BVar × Bool)) :
    dpllAux cs [] asg = match propagate cs with
      | none => none
      | some (forced, cs') => if cs' = [] then some (forced ++ asg) else none := rfl

theorem dpllAux_cons (cs : List Clause) (v : BVar) (rest : List BVar)
    (asg : List (BVar × Bool)) :
    dpllAux cs (v :: rest) asg = match propagate cs with
      | none => none
      | some (forced, cs') =>
          if v ∈ decVars (forced ++ asg) then dpllAux cs' rest (forced ++ asg)
          else match dpllAux (assign v true cs') rest ((v, true) :: forced ++ asg) with
               | some r => some r
               | none => dpllAux (assign v false cs') rest ((v, false) :: forced ++ asg) := rfl
/-- **Soundness of the search (specification 8D, the induction).**  If the search succeeds
then the decisions it returns extend the decisions it was given, they are consistent, and
every total assignment respecting them satisfies the original clause set.

The proof is an induction on the list of branching variables.  The three things unit
propagation gives (propagate_back, propagate_fwd, propagate_agr) and the two things a
restriction step gives (satList_assign, satList_assign_back) are the only model-theoretic
facts used; the invariants NoAssigned and VarsIn are what make the branch variable
available and the decision list consistent at every step. -/
theorem dpllAux_sound : ∀ (vs : List BVar) (cs : List Clause)
    (asg asg' : List (BVar × Bool)),
    NoAssigned cs asg -> VarsIn cs vs -> Consistent asg ->
    dpllAux cs vs asg = some asg' ->
      (∀ p ∈ asg, p ∈ asg') ∧
      (∀ a, (∀ p ∈ asg', a p.1 = p.2) -> SatList a cs) ∧
      Consistent asg' := by
  intro vs
  induction vs with
  | nil =>
      intro cs asg asg' hno hvars hcons h
      rw [dpllAux_nil] at h
      rcases option_cases (propagate cs) with hp | ⟨pf, hp⟩
      · simp only [hp] at h
        cases h
      ·
          obtain ⟨forced, cs'⟩ := pf
          simp only [hp] at h
          obtain ⟨vsub, vdisj, vocc, vcons, vnonil⟩ := propagate_vars hp
          by_cases hce : cs' = []
          · rw [if_pos hce] at h
            obtain rfl := Option.some.inj h
            refine ⟨fun p hp => List.mem_append.mpr (Or.inr hp), ?_,
              consistent_append vcons hcons (by
                intro p hp' q hq e
                exact hno p.1 (vocc p hp') q hq e.symm)⟩
            · intro a ha
              refine propagate_back hp a (by
                intro c hc
                rw [hce] at hc
                simp at hc) ?_
              intro p hp'
              exact ha p (List.mem_append.mpr (Or.inl hp'))
          · rw [if_neg hce] at h
            cases h
  | cons v rest ih =>
      intro cs asg asg' hno hvars hcons h
      rw [dpllAux_cons] at h
      rcases option_cases (propagate cs) with hp | ⟨pf, hp⟩
      · simp only [hp] at h
        cases h
      ·
          obtain ⟨forced, cs'⟩ := pf
          simp only [hp] at h
          obtain ⟨vsub, vdisj, vocc, vcons, vnonil⟩ := propagate_vars hp
          have hno1 : NoAssigned cs' (forced ++ asg) := by
            intro u hu p hp2
            rcases List.mem_append.mp hp2 with hpf | hpa
            · exact vdisj u hu p hpf
            · exact hno u (vsub u hu) p hpa
          have hcons1 : Consistent (forced ++ asg) :=
            consistent_append vcons hcons (by
              intro p hp' q hq e
              exact hno p.1 (vocc p hp') q hq e.symm)
          have hvars1 : VarsIn cs' (v :: rest) := by
            intro u hu
            exact hvars u (vsub u hu)
          by_cases hv : v ∈ decVars (forced ++ asg)
          · -- v was already decided by propagation: no clause of cs' mentions it, so the
            -- branch is skipped and nothing is lost.
            rw [if_pos hv] at h
            obtain ⟨b, hb⟩ := mem_decVars.mp hv
            have hvars' : VarsIn cs' rest := by
              intro u hu
              have hu' : u ∈ v :: rest := hvars1 u hu
              rcases List.mem_cons.mp hu' with hueq | hu'
              · exact absurd hueq.symm (hno1 u hu (v, b) hb)
              · exact hu'
            obtain ⟨hext, hback, hcons'⟩ := ih cs' (forced ++ asg) asg' hno1 hvars' hcons1 h
            refine ⟨(by intro p hp; exact hext p (List.mem_append.mpr (Or.inr hp))), ?_, hcons'⟩
            · intro a ha
              refine propagate_back hp a (hback a ha) ?_
              intro p hp'
              exact ha p (hext p (List.mem_append.mpr (Or.inl hp')))
          · rw [if_neg hv] at h
            have hvn : ∀ q ∈ forced ++ asg, q.1 ≠ v := by
              intro q hq he
              apply hv
              rw [decVars, List.mem_map]
              exact ⟨q, hq, he⟩
            have hno2 (bb : Bool) : NoAssigned (assign v bb cs') ((v, bb) :: forced ++ asg) := by
              intro u hu p hp
              rcases List.mem_cons.mp hp with hpeq | hp
              · subst hpeq
                exact Ne.symm ((mem_litVars_assign hu).2)
              · rcases List.mem_append.mp hp with hp | hp
                · exact hno1 u ((mem_litVars_assign hu).1) p
                    (List.mem_append.mpr (Or.inl hp))
                · exact hno u (vsub u ((mem_litVars_assign hu).1)) p hp
            have hvars2 (bb : Bool) : VarsIn (assign v bb cs') rest := by
              intro u hu
              obtain ⟨hu1, hu2⟩ := mem_litVars_assign hu
              have hv' : u ∈ v :: rest := hvars1 u hu1
              rcases List.mem_cons.mp hv' with hueq | hv'
              · exact absurd hueq hu2
              · exact hv'
            have hcons2 (bb : Bool) : Consistent ((v, bb) :: forced ++ asg) :=
              consistent_cons hcons1 hvn
            rcases option_cases (dpllAux (assign v true cs') rest ((v, true) :: forced ++ asg))
                with h1 | ⟨r, hr⟩
            · -- the true polarity failed: backtracking, so the false one produced asg'
              simp only [h1] at h
              obtain ⟨hext, hback, hcons'⟩ :=
                ih (assign v false cs') ((v, false) :: forced ++ asg) asg'
                  (hno2 false) (hvars2 false) (hcons2 false) h
              refine ⟨?_, ?_, hcons'⟩
              · intro p hp
                exact hext p (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hp))))
              · intro a ha
                have hvb : a v = false := ha (v, false) (hext (v, false) (List.Mem.head _))
                have h2 : SatList a cs' := satList_assign_back (hback a ha) hvb
                refine propagate_back hp a h2 ?_
                intro p hp'
                exact ha p (hext p (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hp')))))
            · -- the true polarity succeeded
              obtain ⟨hext, hback, hcons'⟩ :=
                ih (assign v true cs') ((v, true) :: forced ++ asg) r (hno2 true) (hvars2 true)
                  (hcons2 true) hr
              simp only [hr] at h
              obtain rfl := Option.some.inj h
              refine ⟨?_, ?_, hcons'⟩
              · intro p hp
                exact hext p (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hp))))
              · intro a ha
                have hvb : a v = true := ha (v, true) (hext (v, true) (List.Mem.head _))
                have h2 : SatList a cs' := satList_assign_back (hback a ha) hvb
                refine propagate_back hp a h2 ?_
                intro p hp'
                exact ha p (hext p (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hp')))))

/-- **Completeness of the search (specification 8E, the induction).**  If the search fails
then no model of the clause set agrees with the decisions already taken.

The two invariants do the real work: when no branching variable is left, every clause of the
reduced set is empty (VarsIn), and since propagation reported no conflict, the reduced set
must be empty - so the branch would have succeeded.  When a branching variable is left, a
model of the reduced set agrees with one of the two polarities, so one of the two branches
would have succeeded. -/
theorem dpllAux_complete : ∀ (vs : List BVar) (cs : List Clause) (asg : List (BVar × Bool)),
    dpllAux cs vs asg = none -> NoAssigned cs asg -> VarsIn cs vs ->
    ∀ a, SatList a cs -> (∀ p ∈ asg, a p.1 = p.2) -> False := by
  intro vs
  induction vs with
  | nil =>
      intro cs asg h hno hvars a ha hagree
      rw [dpllAux_nil] at h
      rcases option_cases (propagate cs) with hp | ⟨pf, hp⟩
      · exact propagate_none_unsat hp ⟨a, ha⟩
      ·
          obtain ⟨forced, cs'⟩ := pf
          simp only [hp] at h
          obtain ⟨vsub, vdisj, vocc, vcons, vnonil⟩ := propagate_vars hp
          by_cases hce : cs' = []
          · rw [if_pos hce] at h; cases h
          · rw [if_neg hce] at h
            -- no variable occurs in cs (VarsIn cs []), so every clause of cs' is empty, and
            -- since propagation found no conflict there is no empty clause: cs' is empty.
            cases cs' with
            | nil => exact absurd rfl hce
            | cons c rest =>
                have hc : c ∈ c :: rest := List.Mem.head _
                have hc0 : c = [] := by
                  by_contra e
                  cases c with
                  | nil => exact absurd rfl e
                  | cons l ls =>
                      have hu : l.var ∈ litVars cs :=
                        vsub l.var (mem_litVars_of_mem hc (List.Mem.head _))
                      exact absurd (hvars l.var hu) (by simp)
                exact vnonil (hc0 ▸ hc)
  | cons v rest ih =>
      intro cs asg h hno hvars a ha hagree
      rw [dpllAux_cons] at h
      rcases option_cases (propagate cs) with hp | ⟨pf, hp⟩
      · exact propagate_none_unsat hp ⟨a, ha⟩
      ·
          obtain ⟨forced, cs'⟩ := pf
          simp only [hp] at h
          obtain ⟨vsub, vdisj, vocc, vcons, vnonil⟩ := propagate_vars hp
          have hno1 : NoAssigned cs' (forced ++ asg) := by
            intro u hu p hp2
            rcases List.mem_append.mp hp2 with hpf | hpa
            · exact vdisj u hu p hpf
            · exact hno u (vsub u hu) p hpa
          have hvars1 : VarsIn cs' (v :: rest) := by
            intro u hu
            exact hvars u (vsub u hu)
          have hagr : ∀ p ∈ forced ++ asg, a p.1 = p.2 := by
            intro p hp2
            rcases List.mem_append.mp hp2 with hpf | hpa
            · exact propagate_agr hp a ha p hpf
            · exact hagree p hpa
          have hcs' : SatList a cs' := propagate_fwd hp a ha
          by_cases hv : v ∈ decVars (forced ++ asg)
          · rw [if_pos hv] at h
            obtain ⟨b, hb⟩ := mem_decVars.mp hv
            have hvars' : VarsIn cs' rest := by
              intro u hu
              have hu' : u ∈ v :: rest := hvars1 u hu
              rcases List.mem_cons.mp hu' with hueq | hu'
              · exact absurd hueq.symm (hno1 u hu (v, b) hb)
              · exact hu'
            exact ih cs' (forced ++ asg) h hno1 hvars' a hcs' hagr
          · rw [if_neg hv] at h
            have hvn : ∀ q ∈ forced ++ asg, q.1 ≠ v := by
              intro q hq he
              apply hv
              rw [decVars, List.mem_map]
              exact ⟨q, hq, he⟩
            have hno2 (bb : Bool) : NoAssigned (assign v bb cs') ((v, bb) :: forced ++ asg) := by
              intro u hu p hp
              rcases List.mem_cons.mp hp with hpeq | hp
              · subst hpeq
                exact Ne.symm ((mem_litVars_assign hu).2)
              · rcases List.mem_append.mp hp with hp | hp
                · exact hno1 u ((mem_litVars_assign hu).1) p
                    (List.mem_append.mpr (Or.inl hp))
                · exact hno u (vsub u ((mem_litVars_assign hu).1)) p hp
            have hvars2 (bb : Bool) : VarsIn (assign v bb cs') rest := by
              intro u hu
              obtain ⟨hu1, hu2⟩ := mem_litVars_assign hu
              have hv' : u ∈ v :: rest := hvars1 u hu1
              rcases List.mem_cons.mp hv' with hueq | hv'
              · exact absurd hueq hu2
              · exact hv'
            -- the model agrees with whichever polarity a v has, so one branch has a model
            rcases option_cases (dpllAux (assign v true cs') rest ((v, true) :: forced ++ asg))
                with h1 | ⟨r, hr⟩
            · simp only [h1] at h
              cases hvb : a v with
              | true =>
                  refine ih (assign v true cs') ((v, true) :: forced ++ asg) h1 (hno2 true)
                    (hvars2 true) a (satList_assign hcs' hvb) ?_
                  intro p hp
                  rcases List.mem_cons.mp hp with hpeq | hp
                  · subst hpeq
                    exact hvb
                  · exact hagr p hp
              | false =>
                  refine ih (assign v false cs') ((v, false) :: forced ++ asg) h (hno2 false)
                    (hvars2 false) a (satList_assign hcs' hvb) ?_
                  intro p hp
                  rcases List.mem_cons.mp hp with hpeq | hp
                  · subst hpeq
                    exact hvb
                  · exact hagr p hp
            · simp only [hr] at h
              cases h


/-! ### 7. The top-level solver -/

/-- **The solver.**  dpll f propagates and branches over the variables that occur in f,
each of them at most once (duplicates removed), starting from no decisions.  It returns the
list of decisions of the model it found, or none. -/
def dpll (f : CNF) : Option (List (BVar × Bool)) :=
  dpllAux f.clauses (List.eraseDups (litVars f.clauses)) []

/-- **Specification 8D.**  If DPLL returns SAT, the resulting assignment satisfies the
generated CNF. -/
theorem dpll_sound {f : CNF} {asg : List (BVar × Bool)} (h : dpll f = some asg) :
    Sat (asgVal asg) f := by
  obtain ⟨_hext, hback, hcons⟩ := dpllAux_sound (List.eraseDups (litVars f.clauses))
    f.clauses [] asg
    (by intro v hv p hp; cases hp)
    (by intro v hv; exact List.mem_eraseDups.mpr hv)
    (by intro p hp; cases hp) h
  rw [satList_cnf]
  intro c hc
  exact hback (asgVal asg) (by intro p hp; exact asgVal_mem asg p.1 p.2 hp hcons) c hc

/-- **Specification 8E.**  If DPLL returns UNSAT, the generated CNF is unsatisfiable. -/
theorem dpll_complete {f : CNF} (h : dpll f = none) : ProtSat.Unsat f := by
  rintro ⟨a, ha⟩
  exact dpllAux_complete (List.eraseDups (litVars f.clauses)) f.clauses [] h
    (by intro v hv p hp; cases hp)
    (by intro v hv; exact List.mem_eraseDups.mpr hv) a ha (by intro p hp; cases hp)

/-- DPLL is a decision procedure: it answers SAT exactly on the satisfiable formulas. -/
theorem satisfiable_iff_dpll (f : CNF) : ProtSat.Satisfiable f <-> (dpll f).isSome := by
  constructor
  · intro h
    by_contra e
    have hnone : dpll f = none := by
      cases h' : dpll f with
      | none => rfl
      | some asg =>
          have hs : (dpll f).isSome := by simp [h']
          exact absurd hs e
    exact (dpll_complete hnone) h
  · intro h
    cases h' : dpll f with
    | none => rw [h'] at h; simp [Option.isSome] at h
    | some asg => exact ⟨asgVal asg, dpll_sound h'⟩

/-! ### 8. Executable examples (all checked by the kernel with decide) -/

/-- Unit propagation decides this one: ¬x0 forces x0 ∨ x1 to x1, which forces x1. -/
def demoUnit : CNF := ⟨[[pos 0, pos 1], [neg 0], [pos 1, pos 2]]⟩

/-- The solver succeeds on demoUnit. -/
theorem demoUnit_sat : (dpll demoUnit).isSome := by decide

/-- Hence demoUnit is satisfiable - specification 8D on a concrete input. -/
theorem demoUnit_satisfiable : ProtSat.Satisfiable demoUnit :=
    (satisfiable_iff_dpll demoUnit).mpr demoUnit_sat

/-- (x0) ∧ (¬x0): propagation restricts x0 to true, the second clause becomes empty, and
the conflict is reported. -/
def demoConflict : CNF := ⟨[[pos 0], [neg 0]]⟩

/-- Hence demoConflict is unsatisfiable - specification 8E on a concrete input. -/
theorem demoConflict_unsat : ProtSat.Unsat demoConflict := dpll_complete (by decide)

/-- A formula with no unit clause at all: only branching can solve it, and both polarities
of x0 lead to a conflict. -/
def demoBranch : CNF := ⟨[[pos 0, pos 1], [neg 0, pos 1], [pos 0, neg 1], [neg 0, neg 1]]⟩

/-- Branching plus conflict detection proves demoBranch unsatisfiable. -/
theorem demoBranch_unsat : ProtSat.Unsat demoBranch := dpll_complete (by decide)

/-- A satisfiable formula that needs branching: x1 is forced by the pair of clauses, but
no unit clause is present initially. -/
def demoBranchSat : CNF := ⟨[[pos 0, pos 1], [neg 0, pos 1]]⟩

theorem demoBranchSat_satisfiable : ProtSat.Satisfiable demoBranchSat :=
    (satisfiable_iff_dpll demoBranchSat).mpr (by decide)

-- The decisions the solver returns for demoBranchSat.
#eval dpll demoBranchSat

-- The decisions the solver returns for demoUnit.
#eval dpll demoUnit

end ProtSat.DPLL

