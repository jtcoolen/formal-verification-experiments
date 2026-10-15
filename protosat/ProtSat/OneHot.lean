/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.CNF

/-!
# ProtSat: the one-hot abstraction and function-graph clauses

## Why this module exists

ProtSat.Encode has to say, in CNF, things like

    "the program counter of session q at step i is c"
    "session q's variable x holds the message t at step i"
    "the value of expression e at step i is v"
    "the successor configuration is the one the operational semantics prescribes"

Every one of those is an instance of a single pattern: a finite domain encoded
one-hot, and a function between two such domains encoded by its graph.  Proving the
pattern ONCE here, with full generality, is what makes the encoding theorems of
specification sections 8A and 8B feasible: each becomes an application of
decode_eq_iff, graph_correct or rel_correct rather than a fresh wall of clauses.

This is also what keeps the encoding honest as a *compositional* translation
(specification section 5): the clauses are generated from the semantic function being
encoded, and the theorems say the clauses hold exactly of the graph of that function.

## The workhorse theorems

* graph_correct: if the one-hot groups of x and y are properly filled and the graph
  clauses of f are satisfied, then the decoded y equals f applied to the decoded x.
  Soundness direction of every "next-state" clause of the encoding.
* graph_correct_back: conversely, if the decoded values satisfy y = f x then the graph
  clauses hold.  Completeness direction, used by specification 8B.
* rel_correct / rel_complete: the same for a relation, used for enabledness conditions.
-/

namespace ProtSat.OneHot

open ProtSat

/-! ### Decoding a one-hot group -/

/-- Read off which variable of a group is set to true, as a direct recursion over the
list of domain values. -/
def decodeGo : (vals : List α) -> (varOf : α -> BVar) -> Assignment -> Option α
  | [], _, _ => none
  | x :: xs, v, a => match a (v x) with
      | true => some x
      | false => decodeGo xs v a

/-- If x is in the group, its variable is true, and every true variable belongs to x,
then decode returns x. -/
theorem decodeGo_eq : ∀ (vals : List α) (varOf : α -> BVar) (a : Assignment) (x : α),
    x ∈ vals -> a (varOf x) = true ->
    (∀ y ∈ vals, a (varOf y) = true -> y = x) ->
    decodeGo vals varOf a = some x := by
  intro vals
  induction vals with
  | nil => intro varOf a x hx _ _; exact absurd hx (by simp)
  | cons b bs ih =>
      intro varOf a x hx hax hu
      cases hab : a (varOf b) with
      | true =>
          have hbx : b = x := hu b (List.Mem.head _) hab
          subst hbx
          rw [decodeGo, hab]
      | false =>
          rw [decodeGo, hab]
          refine ih varOf a x ?_ hax ?_
          · rcases (List.mem_cons.mp hx) with heq | hx
            · exact absurd (heq ▸ hax) (by simpa using hab)
            · exact hx
          · intro y hy hp
            exact hu y (List.Mem.tail _ hy) hp

/-- Whatever decode returns is a group member whose variable is true. -/
theorem decodeGo_some : ∀ (vals : List α) (varOf : α -> BVar) (a : Assignment) (x : α),
    decodeGo vals varOf a = some x -> x ∈ vals ∧ a (varOf x) = true := by
  intro vals
  induction vals with
  | nil => intro varOf a x h; cases h
  | cons b bs ih =>
      intro varOf a x h
      cases hab : a (varOf b) with
      | true =>
          rw [decodeGo, hab] at h
          cases h
          exact ⟨List.Mem.head _, hab⟩
      | false =>
          rw [decodeGo, hab] at h
          obtain ⟨hmem, htrue⟩ := ih varOf a x h
          exact ⟨List.Mem.tail _ hmem, htrue⟩

/-! ### One-hot groups -/

/-- A one-hot group over a finite domain α: a list of values, each mapped to its own
Boolean variable, with distinct values getting distinct variables, and the list
nonempty (so that the at-least-one clause is satisfiable). -/
structure Oh (α : Type) where
  vals : List α
  varOf : α -> BVar
  varInj : ∀ x ∈ vals, ∀ y ∈ vals, varOf x = varOf y -> x = y
  nonempty : vals ≠ []

/-- The one-hot clauses of a group: exactly one of its variables is true. -/
def Oh.clauses (o : Oh α) : CNF := exactlyOne (o.vals.map o.varOf)

/-- **The one-hot characterisation.**  A satisfying assignment selects a unique element
of the domain. -/
theorem Oh.clauses_unique {o : Oh α} {a : Assignment} (h : Sat a (o.clauses)) :
    ∃! x, x ∈ o.vals ∧ a (o.varOf x) = true := by
  rw [Oh.clauses, sat_exactlyOne] at h
  obtain ⟨v, hv, hu⟩ := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv.1
  refine ⟨x, ⟨hx, hv.2⟩, fun y hy => ?_⟩
  have := hu (o.varOf y) ⟨List.mem_map.mpr ⟨y, hy.1, rfl⟩, hy.2⟩
  exact o.varInj y hy.1 x hx this

/-- Decode the element selected by an assignment. -/
def Oh.decode (o : Oh α) (a : Assignment) : Option α :=
  decodeGo o.vals o.varOf a

/-- **Decoding is exact.**  Under the one-hot clauses, decode returns x exactly when x
is the selected element. -/
theorem Oh.decode_eq_iff {o : Oh α} {a : Assignment} (h : Sat a (o.clauses)) :
    o.decode a = some x <-> (x ∈ o.vals ∧ a (o.varOf x) = true) := by
  rw [Oh.decode]
  obtain ⟨z, hz, hu⟩ := clauses_unique h
  constructor
  · intro hx
    exact decodeGo_some o.vals o.varOf a x hx
  · intro ⟨hx, ha⟩
    have hzx : x = z := hu x ⟨hx, ha⟩
    subst hzx
    exact decodeGo_eq o.vals o.varOf a x hx ha
      (fun y hy hp => hu y ⟨hy, hp⟩)

/-- The decode of a satisfying assignment always succeeds. -/
theorem Oh.decode_some {o : Oh α} {a : Assignment} (h : Sat a (o.clauses)) :
    ∃ x, o.decode a = some x := by
  obtain ⟨x, hx, _⟩ := clauses_unique h
  exact ⟨x, (Oh.decode_eq_iff h).mpr ⟨hx.1, hx.2⟩⟩

/-- A group member whose variable is true is the decoded one. -/
theorem Oh.decode_of_true {o : Oh α} {a : Assignment} (h : Sat a (o.clauses))
    (hx : x ∈ o.vals) (ha : a (o.varOf x) = true) : o.decode a = some x :=
  (Oh.decode_eq_iff h).mpr ⟨hx, ha⟩

/-! ### Function-graph clauses -/

/-- The graph clauses of f : α → β between two one-hot groups: the assignment may not
select x in α and y in β unless y = f x.  One clause per forbidden pair; this is the
basic compositional step of the encoding. -/
def graphClauses {α : Type} {β : Type} [DecidableEq β] (f : α -> β) (o₁ : Oh α) (o₂ : Oh β) : CNF :=
  ⟨(o₁.vals.flatMap fun x =>
      (o₂.vals.filterMap fun y =>
        if f x = y then none else some [neg (o₁.varOf x), neg (o₂.varOf y)]))⟩

/-- The forbidden-pair clauses of f, spelled out as a membership statement. -/
theorem mem_graphClauses {α : Type} {β : Type} [DecidableEq β] {f : α -> β}
    {o₁ : Oh α} {o₂ : Oh β} {cl : Clause} :
    cl ∈ (graphClauses f o₁ o₂).clauses <->
      ∃ x ∈ o₁.vals, ∃ y ∈ o₂.vals, f x ≠ y ∧
        cl = [neg (o₁.varOf x), neg (o₂.varOf y)] := by
  constructor
  · intro h
    have h1 : cl ∈ (o₁.vals.flatMap fun x =>
        (o₂.vals.filterMap fun y =>
          if f x = y then none else some [neg (o₁.varOf x), neg (o₂.varOf y)])) := h
    rw [List.mem_flatMap] at h1
    obtain ⟨x, hx, h2⟩ := h1
    rw [List.mem_filterMap] at h2
    obtain ⟨y, hy, heq⟩ := h2
    by_cases hne : f x = y
    · rw [if_pos hne] at heq
      exact absurd heq (by simp)
    · rw [if_neg hne] at heq
      exact ⟨x, hx, y, hy, hne, (Option.some.inj heq.symm)⟩
  · rintro ⟨x, hx, y, hy, hne, rfl⟩
    have : [neg (o₁.varOf x), neg (o₂.varOf y)] ∈ (o₁.vals.flatMap fun u =>
        (o₂.vals.filterMap fun v =>
          if f u = v then none else some [neg (o₁.varOf u), neg (o₂.varOf v)])) := by
      rw [List.mem_flatMap]
      refine ⟨x, hx, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨y, hy, by simp [hne]⟩
    simpa [graphClauses] using this

/-- **Soundness of the graph encoding.**  If both groups are properly filled and the
graph clauses hold, the decoded β element is the image of the decoded α element. -/
theorem graph_correct {α : Type} {β : Type} [DecidableEq β] {f : α -> β} {o₁ : Oh α}
    {o₂ : Oh β} {a : Assignment}
    (h₁ : Sat a (o₁.clauses)) (h₂ : Sat a (o₂.clauses))
    (hg : Sat a (graphClauses f o₁ o₂)) :
    (o₁.decode a).map f = o₂.decode a := by
  obtain ⟨x, hx⟩ := Oh.decode_some h₁
  obtain ⟨y, hy⟩ := Oh.decode_some h₂
  obtain ⟨hxv, hxa⟩ := decodeGo_some o₁.vals o₁.varOf a x hx
  obtain ⟨hyv, hya⟩ := decodeGo_some o₂.vals o₂.varOf a y hy
  have hf : f x = y := by
    by_contra e
    have hmem : [neg (o₁.varOf x), neg (o₂.varOf y)] ∈ (graphClauses f o₁ o₂).clauses :=
      (mem_graphClauses).mpr ⟨x, hxv, y, hyv, e, rfl⟩
    have := hg _ hmem
    simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hxa, hya] at this
  subst hf
  rw [hx, Option.map_some, hy]

/-- **Completeness of the graph encoding.**  If the decoded values satisfy y = f x then
the graph clauses hold.  This is the direction used by specification 8B. -/
theorem graph_correct_back {α : Type} {β : Type} [DecidableEq β] {f : α -> β} {o₁ : Oh α}
    {o₂ : Oh β} {a : Assignment}
    (h₁ : Sat a (o₁.clauses)) (h₂ : Sat a (o₂.clauses))
    (h : (o₁.decode a).map f = o₂.decode a) : Sat a (graphClauses f o₁ o₂) := by
  intro cl hcl
  obtain ⟨x, hx, y, hy, hne, rfl⟩ := (mem_graphClauses).mp hcl
  simp only [Clause.eval, List.any_cons, List.any_nil, neg_eval]
  by_cases ax : a (o₁.varOf x) = true
  · by_cases ay : a (o₂.varOf y) = true
    · exfalso
      have hdx : o₁.decode a = some x := Oh.decode_of_true h₁ hx ax
      have hdy : o₂.decode a = some y := Oh.decode_of_true h₂ hy ay
      rw [hdx, hdy] at h
      exact hne (Option.some.inj h)
    · simp [ay]
  · simp [ax]

/-! ### Relation clauses -/

/-- A relation between two one-hot domains: the assignment may only select a related
pair.  Used for enabledness conditions (specification 8A). -/
def relClauses {α β : Type} (R : α -> β -> Prop) [DecidableRel R]
    (o₁ : Oh α) (o₂ : Oh β) : CNF :=
  ⟨(o₁.vals.flatMap fun x =>
      (o₂.vals.filterMap fun y =>
        if R x y then none else some [neg (o₁.varOf x), neg (o₂.varOf y)]))⟩

/-- Membership in the forbidden-pair clauses of a relation. -/
theorem mem_relClauses {α β : Type} {R : α -> β -> Prop} [DecidableRel R]
    {o₁ : Oh α} {o₂ : Oh β} {cl : Clause} :
    cl ∈ (relClauses R o₁ o₂).clauses <->
      ∃ x ∈ o₁.vals, ∃ y ∈ o₂.vals, ¬ R x y ∧
        cl = [neg (o₁.varOf x), neg (o₂.varOf y)] := by
  constructor
  · intro h
    have h1 : cl ∈ (o₁.vals.flatMap fun x =>
        (o₂.vals.filterMap fun y =>
          if R x y then none else some [neg (o₁.varOf x), neg (o₂.varOf y)])) := h
    rw [List.mem_flatMap] at h1
    obtain ⟨x, hx, h2⟩ := h1
    rw [List.mem_filterMap] at h2
    obtain ⟨y, hy, heq⟩ := h2
    by_cases hR : R x y
    · rw [if_pos hR] at heq
      exact absurd heq (by simp)
    · rw [if_neg hR] at heq
      exact ⟨x, hx, y, hy, hR, (Option.some.inj heq.symm)⟩
  · rintro ⟨x, hx, y, hy, hne, rfl⟩
    have : [neg (o₁.varOf x), neg (o₂.varOf y)] ∈ (o₁.vals.flatMap fun u =>
        (o₂.vals.filterMap fun v =>
          if R u v then none else some [neg (o₁.varOf u), neg (o₂.varOf v)])) := by
      rw [List.mem_flatMap]
      refine ⟨x, hx, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨y, hy, by simp [hne]⟩
    simpa [relClauses] using this

/-- **Soundness of the relation encoding.** -/
theorem rel_correct {α β : Type} {R : α -> β -> Prop} [DecidableRel R]
    {o₁ : Oh α} {o₂ : Oh β} {a : Assignment}
    (h₁ : Sat a (o₁.clauses)) (h₂ : Sat a (o₂.clauses))
    (hr : Sat a (relClauses R o₁ o₂)) :
    ∀ x y, o₁.decode a = some x -> o₂.decode a = some y -> R x y := by
  intro x y hdx hdy
  obtain ⟨hxv, hxa⟩ := decodeGo_some o₁.vals o₁.varOf a x hdx
  obtain ⟨hyv, hya⟩ := decodeGo_some o₂.vals o₂.varOf a y hdy
  by_contra e
  have hmem : [neg (o₁.varOf x), neg (o₂.varOf y)] ∈ (relClauses R o₁ o₂).clauses :=
    (mem_relClauses).mpr ⟨x, hxv, y, hyv, e, rfl⟩
  have := hr _ hmem
  simp [Clause.eval, List.any_cons, List.any_nil, neg_eval, hxa, hya] at this

/-- **Completeness of the relation encoding.** -/
theorem rel_complete {α β : Type} {R : α -> β -> Prop} [DecidableRel R]
    {o₁ : Oh α} {o₂ : Oh β} {a : Assignment}
    (h₁ : Sat a (o₁.clauses)) (h₂ : Sat a (o₂.clauses))
    (h : ∀ x y, o₁.decode a = some x -> o₂.decode a = some y -> R x y) :
    Sat a (relClauses R o₁ o₂) := by
  intro cl hcl
  obtain ⟨x, hx, y, hy, hne, rfl⟩ := (mem_relClauses).mp hcl
  simp only [Clause.eval, List.any_cons, List.any_nil, neg_eval]
  by_cases ax : a (o₁.varOf x) = true
  · by_cases ay : a (o₂.varOf y) = true
    · exfalso
      have hdx : o₁.decode a = some x := Oh.decode_of_true h₁ hx ax
      have hdy : o₂.decode a = some y := Oh.decode_of_true h₂ hy ay
      exact hne (h x y hdx hdy)
    · simp [ay]
  · simp [ax]

end ProtSat.OneHot
