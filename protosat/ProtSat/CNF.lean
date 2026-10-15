/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import Mathlib.Data.List.Basic

/-!
# ProtSat: conjunctive normal form, assignments, and the encoding combinators

This module is the *only* propositional vocabulary shared by the rest of the
development.  It is deliberately tiny and completely explicit:

* a variable is a natural number;
* a literal is a variable plus a negation flag;
* a clause is a disjunction of literals;
* a CNF formula is a conjunction of clauses;
* an assignment is a function Nat -> Bool.

Everything else in the project either (i) *produces* clauses (ProtSat.Encode),
(ii) *searches* for a satisfying assignment (ProtSat.DPLL), or (iii) *ignores*
this module entirely.  Point (iii) matters: ProtSat.Certificate is the independent
attack-certificate checker demanded by section 7 of the specification, and it does
not import this module, so it cannot accidentally trust the encoding.

## Why the combinators here carry iff theorems

The specification demands "a genuine Tseitin-style encoding or another
compositional CNF translation with proved correctness".  Compositionality is
provided by the theorems sat_atLeastOne, sat_atMostOne, sat_exactlyOne, sat_notDef,
sat_andDef, sat_orDef: each is an *if and only if* between "the clauses generated
for this gate are satisfied" and "the Boolean equation defining the gate holds".
A translation assembled from these combinators therefore comes with a correctness
proof by construction, which is what ProtSat.Encode exploits.
-/

namespace ProtSat

/-! ### The basic objects -/

/-- A Boolean variable is a natural number.  ProtSat.Encode owns the map from
variables to semantic roles. -/
abbrev BVar := Nat

/-- A literal: a variable, possibly negated.  Using a structure rather than an
integer keeps every proof below free of integer arithmetic. -/
structure Lit where
  var : BVar
  neg : Bool
  deriving Repr, DecidableEq

/-- The positive literal of variable v. -/
def pos (v : BVar) : Lit := ⟨v, false⟩

/-- The negative literal of variable v. -/
def neg (v : BVar) : Lit := ⟨v, true⟩

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
structure CNF where
  clauses : List Clause
  deriving Repr

/-- An assignment maps every variable to a Boolean value. -/
abbrev Assignment := BVar -> Bool

/-- Evaluate a literal under an assignment. -/
def Lit.eval (a : Assignment) (l : Lit) : Bool :=
  if l.neg then !a l.var else a l.var

/-- Evaluate a clause (a disjunction) under an assignment. -/
def Clause.eval (a : Assignment) (c : Clause) : Bool := c.any (fun l => l.eval a)

/-- The propositional satisfaction relation: every clause is true.  Stated as a
Prop (not a Bool) so that the soundness and completeness theorems of sections 8A,
8B, 8D and 8E can talk about it without decidability detours. -/
def Sat (a : Assignment) (f : CNF) : Prop :=
  ∀ c ∈ f.clauses, Clause.eval a c = true

/-- A formula is satisfiable. -/
def Satisfiable (f : CNF) : Prop := ∃ a, Sat a f

/-- A formula is unsatisfiable. -/
def Unsat (f : CNF) : Prop := ¬ Satisfiable f

instance : Append CNF where
  append f g := ⟨f.clauses ++ g.clauses⟩

@[simp] theorem pos_eval (a : Assignment) (v : BVar) : (pos v).eval a = a v := by
  simp [Lit.eval, pos]

@[simp] theorem neg_eval (a : Assignment) (v : BVar) : (neg v).eval a = !a v := by
  simp [Lit.eval, neg]

theorem clause_eval_any (a : Assignment) (c : Clause) :
    Clause.eval a c = true ↔ ∃ l ∈ c, l.eval a = true := by
  rw [Clause.eval, List.any_eq_true]

/-- The empty clause is unsatisfied by every assignment: this is how a DPLL
conflict is represented. -/
theorem clause_eval_nil (a : Assignment) : Clause.eval a [] = false := by
  simp [Clause.eval]

theorem Clause.eval_cons (a : Assignment) (l : Lit) (c : Clause) :
    Clause.eval a (l :: c) = (l.eval a || Clause.eval a c) := by
  simp [Clause.eval, List.any_cons]

/-- Conjoining formulas splits satisfaction. -/
theorem sat_append {f g : CNF} {a : Assignment} :
    Sat a (f ++ g) ↔ (Sat a f ∧ Sat a g) := by
  constructor
  · intro h
    refine ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

/-- A single clause as a formula. -/
def clauseOf (cl : Clause) : CNF := ⟨[cl]⟩

theorem sat_clauseOf {a : Assignment} {cl : Clause} :
    Sat a (clauseOf cl) ↔ Clause.eval a cl = true := by
  simp [Sat, clauseOf]

/-! ### Exactly-one (one-hot) constraints -/

/-- atLeastOne vs is the single clause saying that some variable of vs is true. -/
def atLeastOne (vs : List BVar) : CNF := clauseOf (vs.map pos)

/-- atMostOne vs says no two distinct variables of vs are true at the same time.
One clause per ordered pair of distinct variables; duplicated clauses are
harmless for satisfiability and keep the proof below free of case splits. -/
def atMostOne (vs : List BVar) : CNF :=
  ⟨vs.flatMap fun v => vs.filterMap fun w => if v ≠ w then some [neg v, neg w] else none⟩

/-- exactlyOne vs is the one-hot constraint: precisely one variable of vs is true.

The one-hot encoding is the backbone of ProtSat.Encode: every component of a
protocol configuration (program counter, local-store slot, attacker-knowledge
atom, authentication pebble) is represented by a group of variables of which
exactly one is true. -/
def exactlyOne (vs : List BVar) : CNF := atLeastOne vs ++ atMostOne vs

/-- The disjunction of the positive literals of a list of variables holds exactly
when one of those variables is assigned true. -/
theorem clause_eval_map_pos (a : Assignment) (vs : List BVar) :
    Clause.eval a (vs.map pos) = true ↔ ∃ v ∈ vs, a v = true := by
  induction vs with
  | nil => simp [Clause.eval]
  | cons v rest ih =>
      rw [List.map_cons, Clause.eval_cons, Bool.or_eq_true, ih]
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨v, List.Mem.head _, by show (pos v).eval a = true; rw [pos_eval]; exact h⟩
        · obtain ⟨w, hw, ha⟩ := h
          exact ⟨w, List.Mem.tail _ hw, ha⟩
      · rintro ⟨w, hw, ha⟩
        rw [List.mem_cons] at hw
        rcases hw with h | hw
        · left; show (pos v).eval a = true; rw [pos_eval, ← h]; exact ha
        · right; exact ⟨w, hw, ha⟩

theorem sat_atLeastOne {a : Assignment} {vs : List BVar} :
    Sat a (atLeastOne vs) ↔ ∃ v ∈ vs, a v = true := by
  rw [atLeastOne, sat_clauseOf, clause_eval_map_pos]

/-- The shape of the clauses generated by atMostOne: one clause per ordered pair
of *distinct* variables of the group. -/
theorem mem_atMostOne_clauses {vs : List BVar} {cl : Clause}
    (h : cl ∈ (vs.flatMap fun v =>
      vs.filterMap fun w => if v ≠ w then some [neg v, neg w] else none)) :
    ∃ v w : BVar, v ∈ vs ∧ w ∈ vs ∧ v ≠ w ∧ cl = [neg v, neg w] := by
  rw [List.mem_flatMap] at h
  obtain ⟨v, hv, h2⟩ := h
  rw [List.mem_filterMap] at h2
  obtain ⟨w, hw, h3⟩ := h2
  by_cases hne : v = w
  · subst hne; simp at h3
  · rw [if_pos hne] at h3
    exact ⟨v, w, hv, hw, hne, (Option.some.inj h3).symm⟩

theorem sat_atMostOne {a : Assignment} {vs : List BVar} :
    Sat a (atMostOne vs) ↔ ∀ v ∈ vs, ∀ w ∈ vs, a v = true -> a w = true -> v = w := by
  rw [atMostOne, Sat]
  constructor
  · intro h v hv w hw ha hb
    by_contra e
    have hcl : [neg v, neg w] ∈
        (vs.flatMap fun x => vs.filterMap fun y => if x ≠ y then some [neg x, neg y] else none) := by
      rw [List.mem_flatMap]
      refine ⟨v, hv, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨w, hw, by simpa using e⟩
    have htrue : Clause.eval a [neg v, neg w] = true := h _ hcl
    have hfalse : Clause.eval a [neg v, neg w] = false := by
      simp only [Clause.eval, List.any_cons, List.any_nil, neg_eval]
      rw [ha, hb]
      rfl
    rw [hfalse] at htrue
    exact absurd htrue (by decide)
  · intro h cl hcl
    obtain ⟨v, w, hv, hw, hne, heq⟩ := mem_atMostOne_clauses hcl
    subst heq
    by_cases hv' : a v = true
    . by_cases hw' : a w = true
      . exact absurd (h v hv w hw hv' hw') hne
      . simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hv', hw']
    . simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hv']

/-- **The one-hot characterisation.**  A satisfying assignment of exactlyOne vs
selects a *unique* element of vs.  This is the lemma every decoding function in
ProtSat.Encode starts from. -/
theorem sat_exactlyOne {a : Assignment} {vs : List BVar} :
    Sat a (exactlyOne vs) ↔ ∃! v, v ∈ vs ∧ a v = true := by
  rw [exactlyOne, sat_append, sat_atLeastOne, sat_atMostOne]
  constructor
  · rintro ⟨⟨v, hv, ha⟩, huniq⟩
    exact ⟨v, ⟨hv, ha⟩, fun w hw => huniq w hw.1 v hv hw.2 ha⟩
  · rintro ⟨v, ⟨hv, ha⟩, hu⟩
    refine ⟨⟨v, hv, ha⟩, fun v' hv' w hw' ha' hb' => ?_⟩
    exact (hu v' ⟨hv', ha'⟩).trans (hu w ⟨hw', hb'⟩).symm

/-! ### Tseitin definitional combinators

Each combinator below introduces one fresh variable and returns the clauses that
*define* it.  The accompanying theorem says the clauses are satisfied exactly when
the defining equation holds; that is what makes the overall translation a Tseitin
transformation rather than an ad-hoc clause dump.  Each proof is a truth table:
case-split on the relevant Boolean values, then let simp evaluate the concrete
clause list. -/

/-- z := not x.  The clauses are written as an explicit list so that membership in
them is decidable by reflection, which is what makes the proofs below short. -/
def notDef (z x : BVar) : CNF := ⟨[[neg z, neg x], [pos z, pos x]]⟩

theorem sat_notDef {a : Assignment} {z x : BVar} :
    Sat a (notDef z x) ↔ a z = !a x := by
  constructor
  · intro h
    have h1 : Clause.eval a [neg z, neg x] = true := h _ (by simp [notDef])
    have h2 : Clause.eval a [pos z, pos x] = true := h _ (by simp [notDef])
    simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval] at h1 h2
    by_cases hx : a x = true <;> by_cases hz : a z = true <;> simp_all
  · intro h cl hcl
    simp only [notDef] at hcl
    simp at hcl
    rcases hcl with rfl | rfl
    · simp only [Clause.eval, List.any_cons, List.any_nil, neg_eval]
      by_cases hx : a x = true <;> simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> simp_all

/-- z := x and y. -/
def andDef (z x y : BVar) : CNF :=
  ⟨[[neg z, pos x], [neg z, pos y], [pos z, neg x, neg y]]⟩

theorem sat_andDef {a : Assignment} {z x y : BVar} :
    Sat a (andDef z x y) ↔ a z = (a x && a y) := by
  constructor
  · intro h
    have h1 : Clause.eval a [neg z, pos x] = true := h _ (by simp [andDef])
    have h2 : Clause.eval a [neg z, pos y] = true := h _ (by simp [andDef])
    have h3 : Clause.eval a [pos z, neg x, neg y] = true := h _ (by simp [andDef])
    simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval] at h1 h2 h3
    by_cases hx : a x = true <;> by_cases hy : a y = true <;> by_cases hz : a z = true <;>
      simp_all
  · intro h cl hcl
    simp only [andDef] at hcl
    simp at hcl
    rcases hcl with rfl | rfl | rfl
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> by_cases hz : a z = true <;> simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hy : a y = true <;> by_cases hz : a z = true <;> simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> by_cases hy : a y = true <;> by_cases hz : a z = true <;>
        simp_all

/-- z := x or y. -/
def orDef (z x y : BVar) : CNF :=
  ⟨[[neg z, pos x, pos y], [pos z, neg x], [pos z, neg y]]⟩

theorem sat_orDef {a : Assignment} {z x y : BVar} :
    Sat a (orDef z x y) ↔ a z = (a x || a y) := by
  constructor
  · intro h
    have h1 : Clause.eval a [neg z, pos x, pos y] = true := h _ (by simp [orDef])
    have h2 : Clause.eval a [pos z, neg x] = true := h _ (by simp [orDef])
    have h3 : Clause.eval a [pos z, neg y] = true := h _ (by simp [orDef])
    simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval] at h1 h2 h3
    by_cases hx : a x = true <;> by_cases hy : a y = true <;> by_cases hz : a z = true <;>
      simp_all
  · intro h cl hcl
    simp only [orDef] at hcl
    simp at hcl
    rcases hcl with rfl | rfl | rfl
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> by_cases hy : a y = true <;> by_cases hz : a z = true <;>
        simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> by_cases hz : a z = true <;> simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hy : a y = true <;> by_cases hz : a z = true <;> simp_all

/-- z := (x implies y). -/
def impDef (z x y : BVar) : CNF :=
  ⟨[[neg z, neg x, pos y], [pos z, pos x], [pos z, neg y]]⟩

theorem sat_impDef {a : Assignment} {z x y : BVar} :
    Sat a (impDef z x y) ↔ a z = (!a x || a y) := by
  constructor
  · intro h
    have h1 : Clause.eval a [neg z, neg x, pos y] = true := h _ (by simp [impDef])
    have h2 : Clause.eval a [pos z, pos x] = true := h _ (by simp [impDef])
    have h3 : Clause.eval a [pos z, neg y] = true := h _ (by simp [impDef])
    simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval] at h1 h2 h3
    by_cases hx : a x = true <;> by_cases hy : a y = true <;> by_cases hz : a z = true <;>
      simp_all
  · intro h cl hcl
    simp only [impDef] at hcl
    simp at hcl
    rcases hcl with rfl | rfl | rfl
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> by_cases hy : a y = true <;> by_cases hz : a z = true <;>
        simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hx : a x = true <;> by_cases hz : a z = true <;> simp_all
    · simp only [Clause.eval, List.any_cons, List.any_nil, pos_eval, neg_eval]
      by_cases hy : a y = true <;> by_cases hz : a z = true <;> simp_all

/-- A clause asserting that at least one of the given literals holds.  Used for
the "support" constraints of the attacker-knowledge encoding: if a message is
known then it was known before, or it was observed, or a rule instance fired. -/
def orClause (ls : List Lit) : CNF := clauseOf ls

theorem sat_orClause {a : Assignment} {ls : List Lit} :
    Sat a (orClause ls) ↔ ls.any (fun l => l.eval a) = true := sat_clauseOf

end ProtSat
