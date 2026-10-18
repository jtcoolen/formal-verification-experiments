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

/-- Each half of a conjunction is satisfied. -/
theorem sat_append_left {f g : CNF} {a : Assignment} (h : Sat a (f ++ g)) : Sat a f :=
  fun c hc => h c (List.mem_append_left _ hc)

theorem sat_append_right {f g : CNF} {a : Assignment} (h : Sat a (f ++ g)) : Sat a g :=
  fun c hc => h c (List.mem_append_right _ hc)

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

/-! ### Clause-list combinators

The encoding generates most of its clauses as explicit lists of literal lists.  The
combinators below let a whole clause family be written as one List (List Lit) and give the
single lemma needed to discharge it: exhibit one literal of the clause that the assignment
makes true. -/

/-- A list of clauses as a formula. -/
def cnfOf (l : List (List Lit)) : CNF := ⟨l⟩

theorem sat_cnfOf {a : Assignment} {l : List (List Lit)} :
    Sat a (cnfOf l) <-> ∀ cl ∈ l, Clause.eval a cl = true := by
  simp [Sat, cnfOf]

/-- A clause is satisfied as soon as one of its literals is. -/
theorem clause_eval_holds {a : Assignment} {cl : Clause} (l : Lit) (h1 : l ∈ cl)
    (h2 : Lit.eval a l = true) : Clause.eval a cl := by
  rw [clause_eval_any]; exact ⟨l, h1, h2⟩

/-- Adding a literal to a clause preserves satisfaction. -/
theorem clause_eval_cons_of {a : Assignment} {l : Lit} {cl : Clause}
    (h : Clause.eval a cl = true) : Clause.eval a (l :: cl) = true := by
  rw [Clause.eval_cons, h, Bool.or_true]

/-- Dropping a false literal preserves satisfaction of a clause. -/
theorem clause_eval_cons_false {a : Assignment} {l : Lit} {cl : Clause}
    (h : Clause.eval a (l :: cl) = true) (hl : l.eval a = false) :
    Clause.eval a cl = true := by
  rw [Clause.eval_cons, hl, Bool.false_or] at h; exact h

/-- Dropping a prefix of false literals preserves satisfaction of a clause. -/
theorem clause_eval_append_of_false {a : Assignment} : ∀ (ant : List Lit) (cl : Clause),
    Clause.eval a (ant ++ cl) = true ->
    (∀ l ∈ ant, l.eval a = false) -> Clause.eval a cl = true := by
  intro ant
  induction ant with
  | nil => intro cl h _; simpa using h
  | cons l rest ih =>
      intro cl h hall
      rw [List.cons_append] at h
      exact ih cl (clause_eval_cons_false h (hall l (List.Mem.head _)))
        (fun l' hl' => hall l' (List.Mem.tail _ hl'))

/-- A disjunction splits over an append. -/
theorem Clause.eval_append {a : Assignment} : ∀ (xs ys : Clause),
    Clause.eval a (xs ++ ys) = (Clause.eval a xs || Clause.eval a ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [Clause.eval]
  | cons x rest ih =>
      intro ys
      rw [List.cons_append, Clause.eval_cons, ih, Clause.eval_cons, Bool.or_assoc]

/-- The complement of a literal. -/
def Lit.flip (l : Lit) : Lit := ⟨l.var, !l.neg⟩

@[simp] theorem Lit.flip_eval (a : Assignment) (l : Lit) : l.flip.eval a = !l.eval a := by
  cases l with
  | mk v n => cases n <;> simp [Lit.flip, Lit.eval]

/-- A clause made of the complements of true literals is unsatisfied. -/
theorem clause_eval_map_flip_false {a : Assignment} : ∀ (ls : List Lit),
    (∀ l ∈ ls, l.eval a = true) -> Clause.eval a (ls.map Lit.flip) = false := by
  intro ls
  induction ls with
  | nil => intro _; simp [Clause.eval]
  | cons l rest ih =>
      intro h
      rw [List.map_cons, Clause.eval_cons]
      have hl : l.eval a = true := h l (List.Mem.head _)
      rw [Lit.flip_eval, hl, Bool.not_true, Bool.false_or]
      exact ih (fun l' hl' => h l' (List.Mem.tail _ hl'))

/-- **Definition of a conjunction by a fresh variable.**  andNDef aux ls is the standard
Tseitin definition of aux <-> (l1 and ... and ln): one clause (not aux or l_i) per
literal, plus the single clause (aux or not l_1 or ... or not l_n).  ProtSat.Encode uses
it for the conjunctions that make up a violation condition. -/
def andNDefClauses (aux : BVar) (ls : List Lit) : List Clause :=
  (ls.map fun l => [neg aux, l]) ++ [pos aux :: ls.map Lit.flip]

def andNDef (aux : BVar) (ls : List Lit) : CNF := ⟨andNDefClauses aux ls⟩

theorem mem_andNDef_left {aux : BVar} {ls : List Lit} {l : Lit} (h : l ∈ ls) :
    [neg aux, l] ∈ (andNDef aux ls).clauses :=
  List.mem_append_left _ (List.mem_map.mpr ⟨l, h, rfl⟩)

theorem mem_andNDef_right {aux : BVar} {ls : List Lit} :
    (pos aux :: ls.map Lit.flip) ∈ (andNDef aux ls).clauses :=
  List.mem_append_right _ (List.Mem.head _)

/-- If every literal of ls is true and the clause (aux or not-ls) holds, aux is true. -/
theorem aux_true_of_andN {a : Assignment} {aux : BVar} : ∀ (ls : List Lit),
    Clause.eval a (pos aux :: ls.map Lit.flip) = true ->
    (∀ l ∈ ls, l.eval a = true) -> a aux = true := by
  intro ls
  induction ls with
  | nil =>
      intro h _
      simpa [Clause.eval, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, pos_eval]
        using h
  | cons l rest ih =>
      intro h hall
      by_cases haux : a aux = true
      · exact haux
      · have h1 : Clause.eval a (Lit.flip l :: rest.map Lit.flip) = true :=
          clause_eval_cons_false h (by simp [pos_eval, haux])
        have hl : l.eval a = true := hall l (List.Mem.head _)
        have h2 : Clause.eval a (rest.map Lit.flip) = true :=
          clause_eval_cons_false h1 (by simp [Lit.flip_eval, hl])
        exact ih (clause_eval_cons_of h2) (fun l' hl' => hall l' (List.Mem.tail _ hl'))

theorem sat_andNDef {a : Assignment} {aux : BVar} {ls : List Lit} :
    Sat a (andNDef aux ls) <->
      ((a aux = true -> (∀ l ∈ ls, l.eval a = true)) ∧
       ((∀ l ∈ ls, l.eval a = true) -> a aux = true)) := by
  constructor
  · intro h
    refine ⟨fun haux l hls => ?_, fun hall => ?_⟩
    · have h1 := h _ (mem_andNDef_left hls)
      rw [Clause.eval_cons, neg_eval, haux, Bool.not_true, Bool.false_or, Clause.eval,
        List.any_cons, List.any_nil, Bool.or_false] at h1
      exact h1
    · exact aux_true_of_andN ls (h _ mem_andNDef_right) hall
  · rintro ⟨h1, h2⟩ cl hcl
    rw [andNDef, andNDefClauses, List.mem_append, List.mem_map, List.mem_singleton] at hcl
    rcases hcl with h | h
    · obtain ⟨l, hl, rfl⟩ := h
      by_cases haux : a aux = true
      · exact clause_eval_holds l (List.Mem.tail _ (List.Mem.head _)) (h1 haux l hl)
      · exact clause_eval_holds (neg aux) (List.Mem.head _) (by simp [neg_eval, haux])
    · rcases h with rfl
      by_cases haux : a aux = true
      · exact clause_eval_holds (pos aux) (List.Mem.head _) haux
      · by_cases hall : ∀ l ∈ ls, l.eval a = true
        · exact absurd (h2 hall) haux
        · push_neg at hall
          obtain ⟨l, hl, hfalse⟩ := hall
          refine clause_eval_holds l.flip
            (List.Mem.tail _ (List.mem_map.mpr ⟨l, hl, rfl⟩)) ?_
          have : l.eval a = false := by
            cases h : l.eval a <;> simp_all
          rw [Lit.flip_eval, this, Bool.not_false]

/-! ### A linear-size at-most-one encoding

The one-hot groups of ProtSat.Encode range over the whole message universe, so the pairwise
encoding above produces quadratically many clauses per group and the generated CNF becomes
unusable on any realistic protocol.  The encoding below is the standard sequential counter:
three clauses and one auxiliary variable per position.  It is a genuine Tseitin-style
extension: the auxiliary variables are defined by the clauses, and ProtSat.OneHot only ever
needs the direction "the clauses hold => at most one of the group is true". -/

/-- Sequential at-most-one clauses for the variables vs, with auxiliary flag variables given
by s : Nat -> BVar.  The intended reading of s j is "one of vs[0], ..., vs[j] is true", and
for every j with j + 1 < vs.length the clauses are

  (-vs[j]   v  s_j)      an entry forces its own flag,
  (-vs[j+1] v -s_j)      the next entry refutes the flag,
  (-s_j     v  s_{j+1})  flags are monotone (present when there is a next flag).

If two entries vs[i] and vs[j] with i < j were both true, the first would force s_i, the
chain would force s_{j-1}, and the second would refute it. -/
def atMostOneSeq : List BVar -> (Nat -> BVar) -> List Clause
  | x :: y :: [], s => [[neg x, pos (s 0)], [neg y, neg (s 0)]]
  | x :: y :: (w :: rest), s =>
      [neg x, pos (s 0)] :: [neg y, neg (s 0)] :: [neg (s 0), pos (s 1)]
        :: atMostOneSeq (y :: w :: rest) (fun j => s (j + 1))
  | _, _ => []

@[simp] theorem atMostOneSeq_nil (s : Nat -> BVar) : atMostOneSeq [] s = [] := rfl
@[simp] theorem atMostOneSeq_single (x : BVar) (s : Nat -> BVar) : atMostOneSeq [x] s = [] := rfl
@[simp] theorem atMostOneSeq_two (x y : BVar) (s : Nat -> BVar) :
    atMostOneSeq [x, y] s = [[neg x, pos (s 0)], [neg y, neg (s 0)]] := rfl
@[simp] theorem atMostOneSeq_three (x y w : BVar) (rest : List BVar) (s : Nat -> BVar) :
    atMostOneSeq (x :: y :: w :: rest) s =
      [neg x, pos (s 0)] :: [neg y, neg (s 0)] :: [neg (s 0), pos (s 1)]
        :: atMostOneSeq (y :: w :: rest) (fun j => s (j + 1)) := rfl

/-- The clauses of the tail are clauses of the whole list. -/
theorem mem_atMostOneSeq_tail (x y w : BVar) (rest : List BVar) (s : Nat -> BVar)
    {cl : Clause} (h : cl ∈ atMostOneSeq (y :: w :: rest) (fun j => s (j + 1))) :
    cl ∈ atMostOneSeq (x :: y :: w :: rest) s := by
  rw [atMostOneSeq_three]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil]
  exact Or.inr (Or.inr (Or.inr h))

/-- A Boolean cannot be both true and false. -/
theorem bool_ne {b : Bool} (h₁ : b = true) (h₂ : b = false) : False := by
  cases h : b <;> simp_all

/-- A satisfied two-literal clause with a false first literal has a true second one. -/
theorem clause2_mp {a : Assignment} {l₁ l₂ : Lit} (h : Clause.eval a [l₁, l₂] = true)
    (h₁ : l₁.eval a = false) : l₂.eval a = true := by
  have h2 : l₁.eval a = true ∨ l₂.eval a = true := by
    simpa [Clause.eval, List.any_cons, List.any_nil] using h
  rcases h2 with h2 | h2
  · exact False.elim (bool_ne h2 h₁)
  · exact h2

/-- A literal is false exactly when its variable has the opposite value. -/
theorem lit_neg_false (a : Assignment) (v : BVar) (hv : a v = true) : (neg v).eval a = false := by
  simp [neg_eval, hv]

/-- The strengthened invariant used by the correctness proof: at most one variable of the
list is true, the first variable implies the first flag, and every later variable refutes
it. -/
def AmoInv (a : Assignment) (vs : List BVar) (s : Nat -> BVar) : Prop :=
  (∀ x ∈ vs, ∀ y ∈ vs, a x = true -> a y = true -> x = y) ∧
  (match vs with
   | x :: y :: rest =>
       (a x = true -> a (s 0) = true) ∧ (∀ z ∈ y :: rest, a z = true -> a (s 0) = false)
   | _ => True)

/-- **The sequential encoding really says at-most-one** (its soundness). -/
theorem atMostOneSeq_correct : ∀ (vs : List BVar) (s : Nat -> BVar) (a : Assignment),
    (∀ cl ∈ atMostOneSeq vs s, Clause.eval a cl = true) -> AmoInv a vs s := by
  intro vs
  induction vs with
  | nil =>
      intro s a _
      refine ⟨fun x hx => absurd hx (by simp), trivial⟩
  | cons x rest ih =>
      intro s a h
      cases rest with
      | nil =>
          refine ⟨fun p hp q hq hpa hqa => ?_, trivial⟩
          rw [List.mem_cons] at hp hq
          rcases hp with rfl | hp
          · rcases hq with rfl | hq
            · rfl
            · exact absurd hq (by simp_all)
          · exact absurd hp (by simp_all)
      | cons y rest' =>
          cases rest' with
          | nil =>
              -- vs = [x, y]: the two clauses relate x, y and the flag s 0
              have hc1 : Clause.eval a [neg x, pos (s 0)] = true :=
                h _ (by rw [atMostOneSeq_two]; simp)
              have hc2 : Clause.eval a [neg y, neg (s 0)] = true :=
                h _ (by rw [atMostOneSeq_two]; simp [List.mem_cons])
              have hx1 : a x = true -> a (s 0) = true := fun hx =>
                clause2_mp hc1 (lit_neg_false a x hx)
              have hy1 : a y = true -> a (s 0) = false := fun hy => by
                simpa [neg_eval] using clause2_mp hc2 (lit_neg_false a y hy)
              have htail0 : ∀ z ∈ [y], a z = true -> a (s 0) = false := by
                intro z hz hza
                have hzy : z = y := by simpa using hz
                rw [hzy] at hza
                exact hy1 hza
              refine ⟨fun p hp q hq hpa hqa => ?_, ⟨hx1, htail0⟩⟩
              · rw [List.mem_cons] at hp hq
                rcases hp with hpeq | hp
                · rcases hq with hqeq | hq
                  · exact hpeq.trans hqeq.symm
                  · exact False.elim (bool_ne (hx1 (hpeq ▸ hpa)) (htail0 q hq hqa))
                · rcases hq with hqeq | hq
                  · exact False.elim (bool_ne (hx1 (hqeq ▸ hqa)) (htail0 p hp hpa))
                  · exact (List.mem_singleton.mp hp).trans (List.mem_singleton.mp hq).symm

          | cons w rest'' =>
              have hsub : ∀ cl ∈ atMostOneSeq (y :: w :: rest'') (fun j => s (j + 1)),
                  Clause.eval a cl = true := fun cl hcl =>
                h cl (mem_atMostOneSeq_tail x y w rest'' s hcl)
              obtain ⟨hamo, hflag⟩ := ih (fun j => s (j + 1)) a hsub
              obtain ⟨hyf, hzr⟩ := hflag
              have hc1 : Clause.eval a [neg x, pos (s 0)] = true :=
                h _ (by rw [atMostOneSeq_three]; simp)
              have hc2 : Clause.eval a [neg y, neg (s 0)] = true :=
                h _ (by rw [atMostOneSeq_three]; simp [List.mem_cons])
              have hc3 : Clause.eval a [neg (s 0), pos (s 1)] = true :=
                h _ (by rw [atMostOneSeq_three]; simp [List.mem_cons])
              have hx1 : a x = true -> a (s 0) = true := fun hx =>
                clause2_mp hc1 (lit_neg_false a x hx)
              have hy0 : a y = true -> a (s 0) = false := fun hy => by
                simpa [neg_eval] using clause2_mp hc2 (lit_neg_false a y hy)
              have hs01 : a (s 0) = true -> a (s 1) = true := fun h0 => by
                simpa using clause2_mp hc3 (lit_neg_false a (s 0) h0)
              have htail0 : ∀ z ∈ y :: w :: rest'', a z = true -> a (s 0) = false := by
                intro z hz hza
                rcases List.mem_cons.mp hz with hzeq | hz
                · rw [hzeq] at hza
                  exact hy0 hza
                · cases h : a (s 0) with
                  | true => exact False.elim (bool_ne (hs01 h) (hzr z hz hza))
                  | false => rfl
              refine ⟨fun p hp q hq hpa hqa => ?_, ⟨hx1, htail0⟩⟩
              · rw [List.mem_cons] at hp hq
                rcases hp with hpeq | hp
                · rcases hq with hqeq | hq
                  · exact hpeq.trans hqeq.symm
                  · exact False.elim (bool_ne (hx1 (hpeq ▸ hpa)) (htail0 q hq hqa))
                · rcases hq with hqeq | hq
                  · exact False.elim (bool_ne (hx1 (hqeq ▸ hqa)) (htail0 p hp hpa))
                  · exact hamo p hp q hq hpa hqa

/-- **At-most-one** is the consequence the one-hot groups need: no two variables of the list
are true at the same time. -/
theorem atMostOneSeq_amo {vs : List BVar} {s : Nat -> BVar} {a : Assignment}
    (h : ∀ cl ∈ atMostOneSeq vs s, Clause.eval a cl = true) :
    ∀ x ∈ vs, ∀ y ∈ vs, a x = true -> a y = true -> x = y :=
    (atMostOneSeq_correct vs s a h).1

end ProtSat
