/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

import ProtSat.CheckedSafe

/-!
# ProtSat: a prover that emits independently checkable refutations

## Why this module exists

`Resolution.checkProof` can *verify* a resolution refutation, and
`Resolution.encodingUnsat_of_proof` turns a checked refutation into the analyser's
`encodingUnsat` verdict without replaying any search. What was missing is the other half of the
evidence pipeline: nothing *produced* a refutation. Roadmap stage 6 asks for a search that emits
evidence and a small independent checker that decides; this module is the search.

The engine is saturation by resolution. Round 0 seeds the formula, one line per clause, each
justified by `Just.orig`. Every further round appends the resolvent of every ordered pair of
lines built so far, on every pivot the checker's own side conditions accept, and drops clauses
the list already carries. `refutationOf f k` reads off the lines up to the first empty clause.
Termination is by fuel, so the engine cannot loop; deduplication keeps the closure small enough
to evaluate at all.

The property that matters is not that the engine is clever but that its output is accepted by a
checker it shares no code with beyond the clause vocabulary:

```lean
refute_sound    : refutationOf f k = some p -> checkProof f p = true
refute_unsat    : refutationOf f k = some p -> ProtSat.Unsat f
refute_complete : Unsat f -> exists k p, refutationOf f k = some p
refute_answer   : refutationOf (encode P B) k = some p -> analyze P B = encodingUnsat
boundedSafe_of_refutation : ... -> refutationOf (encode q.protocol q.bounds) k = some p
                             -> boundedSafeGoals q
```

`refute_sound` is proved by showing every line the engine emits is `lineOK` with respect to the
lines before it (`AllOK`), and that a list of justified lines containing the empty clause is
accepted by `checkFrom`. `demo_refutation_checked` is the closed, kernel-checked statement that
this really happens on a formula: the engine's own 19-line output for `demoF`, accepted by
`decide`. `refute_complete` is Davis-Putnam elimination: `dpElim f v` (non-tautological clauses
not mentioning `v`, plus every resolvent on `v`) preserves satisfiability, so eliminating all
variables of an unsatisfiable formula leaves a variable-free unsatisfiable formula, which must
hold the empty clause - and every clause that elimination derives is a line of the saturation,
one round per eliminated variable.

## What this does not do

It is not a fast solver, and the gap is measured rather than asserted. On the real protocol
formula of `EndToEnd.qg` (291 clauses, 659 literal occurrences) fuel 1 yields 1150 lines and no
empty clause, fuel 2 yields 37167 lines and still no empty clause, and evaluating those two
rounds takes about 19 minutes of Lean evaluation. So there is no closed `decide` gate for `qg`:
the honest statement is `boundedSafe_of_refutation`, which takes the engine's
`refutationOf (encode q.protocol q.bounds) k = some p` as a hypothesis, and the closed gates are
the ones this module can actually evaluate (`demoF`). Completeness is a theorem about the
existence of fuel, not a claim that the fuel is reachable at protocol scale; subsumption, unit
propagation and polarity-based pivoting are what would close that gap, and none of them are here.

Nothing in this module is trusted by the checker: `checkProof` re-derives every line from the
formula, so a bug in the engine can make it fail to find a refutation but can never make the
checker accept a false one - `not_refutable_of_satisfiable` says a satisfiable formula has no
output at any fuel.
-/

namespace ProtSat.Refute

open ProtSat
open ProtSat.Resolution
open ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer
open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query
  BoundedExec Represent Serialize CheckedSafe

/-! ### Clauses, pivots, seed lines -/

/-- The clauses carried by a list of lines. -/
def clList : List Line -> List Clause := List.map Line.cl

@[simp] theorem clList_nil : clList [] = [] := rfl

theorem clList_cons (l : Line) (ls : List Line) : clList (l :: ls) = l.cl :: clList ls := rfl

theorem clList_append (a b : List Line) : clList a ++ clList b = clList (a ++ b) := by
  simp [clList, List.map_append]

/-- `v` occurs positively in `c`: the first side condition `lineOK` demands of a resolvent. -/
def hasPos (c : Clause) (v : BVar) : Bool := c.any fun l => l.var == v && !l.neg

/-- `v` occurs negatively in `c`: the second side condition `lineOK` demands of a resolvent. -/
def hasNeg (c : Clause) (v : BVar) : Bool := c.any fun l => l.var == v && l.neg

/-- The seed lines: clause `i` of the formula as line `i`, justified by `Just.orig i`. -/
def seed : List Clause -> Nat -> List Line
  | [], _ => []
  | c :: rest, i => { cl := c, why := Just.orig i } :: seed rest (i + 1)

/-! ### Indexing lemmas -/

/-- An index that reads back a value is in range. -/
theorem rget_lt_of_some {α : Type} : ∀ (l : List α) (i : Nat) (x : α),
    rget l i = some x -> i < l.length := by
  intro l
  induction l with
  | nil => intro i x h; exact absurd h (by simp [rget])
  | cons y ys ih =>
      intro i x h
      cases i with
      | zero => simp [List.length_cons]
      | succ i =>
          have h2 : rget ys i = some x := by simpa [rget] using h
          have := ih i x h2
          simp [List.length_cons]
          omega

/-- Reading below the end of the left half of an append is unaffected by the right half. -/
theorem rget_append_lt {α : Type} (l k : List α) (i : Nat) (h : i < l.length) :
    rget (l ++ k) i = rget l i := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      cases i with
      | zero => simp [rget]
      | succ i =>
          show rget (xs ++ k) i = rget xs i
          exact ih i (by simp [List.length_cons] at h; omega)

/-- Reading at offset `l.length + i` of an append reads the right half. -/
theorem rget_append {α : Type} (l k : List α) (i : Nat) :
    rget (l ++ k) (l.length + i) = rget k i := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
      rw [show (x :: xs).length + i = xs.length + i + 1 from by
        simp [List.length_cons]
        omega]
      simp [rget]
      exact ih i

/-- A membership is witnessed by an index into the same list. -/
theorem exists_rget_of_mem {α : Type} :
    ∀ (l : List α) (x : α), x ∈ l -> ∃ i, rget l i = some x := by
  intro l
  induction l with
  | nil => intro x h; exact absurd h (by simp)
  | cons y ys ih =>
      intro x h
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, by simp [rget]⟩
      · obtain ⟨i, hi⟩ := ih x h
        exact ⟨i + 1, by simp [rget, hi]⟩

/-! ### Building and transporting `lineOK` facts -/

/-- Clause `n` of the formula is a justified line, whatever the prefix. -/
theorem lineOK_orig_iff {f : CNF} {prev : List Clause} {n : Nat} {c : Clause} :
    (lineOK f prev { cl := c, why := Just.orig n } = true) <-> rget f.clauses n = some c := by
  simp [lineOK]

/-- A resolvent line is justified exactly when the two parents are in the prefix at the cited
indices, carry the pivot in opposite polarities, and the clause is the resolvent itself. -/
theorem lineOK_res_iff {f : CNF} {prev : List Clause} {i j : Nat} {v : BVar}
    {cl c₁ c₂ : Clause} (hi : rget prev i = some c₁) (hj : rget prev j = some c₂) :
    (lineOK f prev { cl := cl, why := Just.res i j v } = true) <->
      (hasPos c₁ v = true ∧ hasNeg c₂ v = true ∧ cl = resolve c₁ c₂ v) := by
  simp [lineOK, hasPos, hasNeg, hi, hj]

theorem lineOK_orig {f : CNF} {prev : List Clause} {n : Nat} {c : Clause}
    (h : rget f.clauses n = some c) : lineOK f prev { cl := c, why := Just.orig n } = true :=
  lineOK_orig_iff.mpr h

theorem lineOK_res {f : CNF} {prev : List Clause} {i j : Nat} {c₁ c₂ : Clause} {v : BVar}
    (hi : rget prev i = some c₁) (hj : rget prev j = some c₂)
    (hp : hasPos c₁ v = true) (hn : hasNeg c₂ v = true) :
    lineOK f prev { cl := resolve c₁ c₂ v, why := Just.res i j v } = true :=
  lineOK_res_iff hi hj |>.mpr ⟨hp, hn, rfl⟩

/-- A line justified by `prev` stays justified when clauses are appended after `prev`: a
justification only ever reads indices below `prev.length`. -/
theorem lineOK_ext {f : CNF} {prev extra : List Clause} {l : Line}
    (h : lineOK f prev l = true) : lineOK f (prev ++ extra) l = true := by
  cases l with
  | mk cl why =>
      cases why with
      | orig n => exact lineOK_orig_iff.mpr (lineOK_orig_iff.mp h)
      | res i j v =>
          cases hi : rget prev i with
          | none =>
              have hne : lineOK f prev { cl := cl, why := Just.res i j v } = false := by
                simp [lineOK, hi]
              rw [hne] at h
              exact absurd h (by decide)
          | some c₁ =>
              cases hj : rget prev j with
              | none =>
                  have hne : lineOK f prev { cl := cl, why := Just.res i j v } = false := by
                    simp [lineOK, hj]
                  rw [hne] at h
                  exact absurd h (by decide)
              | some c₂ =>
                  obtain ⟨hp, hn, hcl⟩ := lineOK_res_iff hi hj |>.mp h
                  rw [hcl]
                  have h1 : rget (prev ++ extra) i = some c₁ := by
                    rw [rget_append_lt prev extra i (rget_lt_of_some prev i c₁ hi), hi]
                  have h2 : rget (prev ++ extra) j = some c₂ := by
                    rw [rget_append_lt prev extra j (rget_lt_of_some prev j c₂ hj), hj]
                  exact (lineOK_res_iff h1 h2).mpr ⟨hp, hn, rfl⟩

/-! ### Every line justified -/

/-- `AllOK f base p`: every line of `p` is justified by `f` together with the clauses of the
lines before it, counting from the starting prefix `base`. This is the invariant `checkFrom`
walks, stated so that it can be built up block by block. -/
inductive AllOK : CNF -> List Clause -> List Line -> Prop
  | nil : ∀ (f : CNF) (base : List Clause), AllOK f base []
  | cons : ∀ (f : CNF) (base : List Clause) (l : Line) (rest : List Line),
      lineOK f base l = true -> AllOK f (base ++ [l.cl]) rest -> AllOK f base (l :: rest)

/-- Destructuring: the head line is justified by `base`, the tail by `base` plus its clause. -/
theorem AllOK_cons_inv {f : CNF} {base : List Clause} {l : Line} {rest : List Line}
    (h : AllOK f base (l :: rest)) :
    lineOK f base l = true ∧ AllOK f (base ++ [l.cl]) rest := by
  cases h
  exact ⟨‹lineOK f base l = true›, ‹AllOK f (base ++ [l.cl]) rest›⟩

/-- `baseOK f base p`: every line of `p` is justified by `f` and the prefix `base` alone,
ignoring the lines of `p` before it. Since a justification only reads indices below
`base.length`, this is enough to make all of `p` valid after `base`, and it composes by
concatenation - which is what makes the round structure easy to reason about. -/
def baseOK (f : CNF) (base : List Clause) (p : List Line) : Prop :=
  ∀ l, l ∈ p -> lineOK f base l = true

theorem baseOK_AllOK {f : CNF} {base : List Clause} {p : List Line} (h : baseOK f base p) :
    AllOK f base p := by
  induction p generalizing base with
  | nil => exact AllOK.nil f base
  | cons l rest ih =>
      refine AllOK.cons f base l rest (h l (by simp)) (ih ?_)
      intro m hm
      exact lineOK_ext (h m (by simp [hm]))

theorem baseOK_nil (f : CNF) (base : List Clause) : baseOK f base [] := by
  intro l h; exact absurd h (by simp)

theorem baseOK_append {f : CNF} {base : List Clause} {a b : List Line}
    (h1 : baseOK f base a) (h2 : baseOK f base b) : baseOK f base (a ++ b) := by
  intro l h
  rw [List.mem_append] at h
  rcases h with h | h
  · exact h1 l h
  · exact h2 l h

theorem baseOK_flatMap {f : CNF} {base : List Clause} (xs : List Nat) (g : Nat -> List Line)
    (h : ∀ i ∈ xs, baseOK f base (g i)) : baseOK f base (xs.flatMap g) := by
  induction xs with
  | nil => exact baseOK_nil f base
  | cons y rest ih =>
      have hfl : (y :: rest).flatMap g = g y ++ rest.flatMap g := rfl
      rw [hfl]
      refine baseOK_append (h y (by simp)) (ih (by simp_all))

/-- The seed lines are justified: line `i + j` of `seed fs i` is clause `j`. -/
theorem AllOK_seed (f : CNF) : ∀ (fs : List Clause) (i : Nat),
    (∀ j c, rget fs j = some c -> rget f.clauses (i + j) = some c) ->
    ∀ base, AllOK f base (seed fs i) := by
  intro fs
  induction fs with
  | nil => intro i _ base; exact AllOK.nil f base
  | cons c rest ih =>
      intro i h base
      have hseed : seed (c :: rest) i = { cl := c, why := Just.orig i } :: seed rest (i + 1) := rfl
      rw [hseed]
      refine AllOK.cons f _ _ _ (lineOK_orig ?_) (ih (i + 1) ?_ (base ++ [c]))
      · exact h 0 c rfl
      · intro j c' hc'
        have hget : rget (c :: rest) (j + 1) = some c' := by simp [rget, hc']
        have hthis := h (j + 1) c' hget
        rw [show i + 1 + j = i + (j + 1) from by omega]
        exact hthis

/-- Concatenation: a block justified after `base`, followed by a block justified after the
clauses of the first block, is justified after `base`. -/
theorem AllOK_append {f : CNF} {base : List Clause} {acc : List Line}
    (h1 : AllOK f base acc) :
    ∀ (new : List Line), AllOK f (base ++ clList acc) new -> AllOK f base (acc ++ new) := by
  induction h1 with
  | nil => intro new h2; simpa using h2
  | cons b l rest hok hall ih =>
      intro new h2
      refine AllOK.cons f b l (rest ++ new) hok (ih new ?_)
      simpa [clList_cons, List.append_assoc] using h2

/-! ### The saturation engine -/

/-- All resolvents of line `i` of `acc` with line `j`, one per positive occurrence of a pivot
in line `i` that line `j` refutes. Each is justified by `Just.res i j v`, citing exactly the
indices the checker will look up. -/
def resols (acc : List Line) (i j : Nat) : List Line :=
  match rget (clList acc) i, rget (clList acc) j with
  | some c₁, some c₂ =>
      (c₁.filter fun l => !l.neg).flatMap fun l =>
        if hasNeg c₂ l.var = true then
          [{ cl := resolve c₁ c₂ l.var, why := Just.res i j l.var }]
        else []
  | _, _ => []

theorem resols_some {acc : List Line} {i j : Nat} {c₁ c₂ : Clause}
    (hi : rget (clList acc) i = some c₁) (hj : rget (clList acc) j = some c₂) :
    resols acc i j = (c₁.filter fun x => !x.neg).flatMap fun x =>
      if hasNeg c₂ x.var = true then
        [{ cl := resolve c₁ c₂ x.var, why := Just.res i j x.var }]
      else [] := by
  unfold resols
  rw [hi, hj]

theorem resols_none1 {acc : List Line} {i j : Nat} (hi : rget (clList acc) i = none) :
    resols acc i j = [] := by
  unfold resols
  rw [hi]

theorem resols_none2 {acc : List Line} {i j : Nat} (hj : rget (clList acc) j = none) :
    resols acc i j = [] := by
  unfold resols
  cases rget (clList acc) i with
  | none => simp
  | some c₁ => rw [hj]

theorem mem_resols {acc : List Line} {i j : Nat} {l : Line} (h : l ∈ resols acc i j) :
    ∃ (c₁ c₂ : Clause) (v : BVar), rget (clList acc) i = some c₁ ∧
      rget (clList acc) j = some c₂ ∧ hasPos c₁ v = true ∧ hasNeg c₂ v = true ∧
      l = { cl := resolve c₁ c₂ v, why := Just.res i j v } := by
  cases hi : rget (clList acc) i with
  | none => exact absurd h (by rw [resols_none1 hi]; simp)
  | some c₁ =>
      cases hj : rget (clList acc) j with
      | none => exact absurd h (by rw [resols_none2 hj]; simp)
      | some c₂ =>
          rw [resols_some hi hj] at h
          rw [List.mem_flatMap] at h
          obtain ⟨a, ha, h2⟩ := h
          rw [List.mem_filter] at ha
          by_cases hv : hasNeg c₂ a.var = true
          · have hif : (if hasNeg c₂ a.var = true then
                  ([{ cl := resolve c₁ c₂ a.var, why := Just.res i j a.var }] : List Line)
                  else ([] : List Line))
                = ([{ cl := resolve c₁ c₂ a.var, why := Just.res i j a.var }] : List Line) := by
              simp [hv]
            rw [hif] at h2
            rw [List.mem_singleton] at h2
            subst h2
            refine ⟨c₁, c₂, a.var, rfl, rfl, ?_, hv, rfl⟩
            refine List.any_eq_true.mpr ⟨a, ha.1, ?_⟩
            simpa [hasPos] using ha.2
          · have hif : (if hasNeg c₂ a.var = true then
                  ([{ cl := resolve c₁ c₂ a.var, why := Just.res i j a.var }] : List Line)
                  else ([] : List Line)) = ([] : List Line) := by simp [hv]
            rw [hif] at h2
            exact absurd h2 (by simp)

theorem baseOK_resols (f : CNF) (acc : List Line) (i j : Nat) :
    baseOK f (clList acc) (resols acc i j) := by
  intro l hl
  obtain ⟨c₁, c₂, v, hi, hj, hp, hn, rfl⟩ := mem_resols hl
  exact lineOK_res hi hj hp hn

/-- Keep the lines whose clause is new: not already in `seen`, and not repeated further down the
candidate list. Recursion on the second argument, so this terminates on every input. -/
def novel (seen : List Clause) : List Line -> List Line
  | [] => []
  | l :: rest => if l.cl ∈ seen then novel seen rest else l :: novel (seen ++ [l.cl]) rest

theorem novel_nil (seen : List Clause) : novel seen [] = [] := rfl

theorem novel_cons (seen : List Clause) (l : Line) (rest : List Line) :
    novel seen (l :: rest) =
      if l.cl ∈ seen then novel seen rest else l :: novel (seen ++ [l.cl]) rest := rfl

theorem mem_novel : ∀ (seen : List Clause) (cand : List Line) (l : Line),
    l ∈ novel seen cand -> l ∈ cand := by
  intro seen cand l
  induction cand generalizing seen l with
  | nil => intro h; exact absurd h (by simp [novel_nil])
  | cons a rest ih =>
      intro h
      by_cases hm : a.cl ∈ seen
      · have h1 : novel seen (a :: rest) = novel seen rest := by simp [novel_cons, hm]
        rw [h1] at h
        exact List.Mem.tail a (ih seen l h)
      · have h1 : novel seen (a :: rest) = a :: novel (seen ++ [a.cl]) rest := by
          simp [novel_cons, hm]
        rw [h1] at h
        rw [List.mem_cons] at h
        rcases h with heq | hmem
        · subst heq
          exact List.Mem.head _
        · exact List.Mem.tail _ (ih (seen ++ [a.cl]) l hmem)

theorem baseOK_novel {f : CNF} {base : List Clause} (seen : List Clause) {cand : List Line}
    (h : baseOK f base cand) : baseOK f base (novel seen cand) := by
  intro l hl
  exact h l (mem_novel seen cand l hl)

/-- The raw resolvents of one round: every ordered pair of lines of `acc`, before deduplication. -/
def candidates (acc : List Line) : List Line :=
  (List.range acc.length).flatMap fun i =>
    (List.range acc.length).flatMap fun j => resols acc i j

/-- One saturation round: every resolvent of every ordered pair of lines of `acc`, minus the
clauses `acc` already carries. -/
def step (acc : List Line) : List Line :=
  novel (clList acc) (candidates acc)

theorem step_eq (acc : List Line) : step acc = novel (clList acc) (candidates acc) := rfl

theorem AllOK_step (f : CNF) (acc : List Line) : AllOK f (clList acc) (step acc) := by
  unfold step
  refine baseOK_AllOK (baseOK_novel _ (baseOK_flatMap _ _ ?_))
  intro i hi
  refine baseOK_flatMap _ _ (fun j _ => baseOK_resols f acc i j)

/-- **The saturation engine.** Round 0 seeds the formula as `Just.orig` lines; each further round
appends every resolvent of every ordered pair of the lines built so far, dropping clauses the
list already carries. Every new line cites only indices of lines that already exist, so the
output is a valid proof prefix at every fuel. -/
def saturate : Nat -> CNF -> List Line
  | 0, f => seed f.clauses 0
  | k + 1, f => saturate k f ++ step (saturate k f)

theorem AllOK_saturate (k : Nat) (f : CNF) : AllOK f [] (saturate k f) := by
  induction k with
  | zero =>
      refine AllOK_seed f f.clauses 0 (by intro j c hj; simpa using hj) []
  | succ k ih =>
      have h : saturate (k + 1) f = saturate k f ++ step (saturate k f) := rfl
      rw [h]
      refine AllOK_append ih (step (saturate k f)) ?_
      simpa using AllOK_step f (saturate k f)

/-! ### Reading a refutation off the saturation -/

/-- Does some line carry the empty clause? -/
def found : List Line -> Bool := fun ls => ls.any fun l => l.cl = []

theorem found_eq (ls : List Line) : found ls = true <-> ∃ l ∈ ls, l.cl = [] := by
  simp [found, List.any_eq_true]

theorem found_cons (l : Line) (rest : List Line) :
    found (l :: rest) = true <-> l.cl = [] ∨ found rest = true := by
  simp [found, List.any_cons]

/-- The lines up to and including the first one carrying the empty clause; `[]` if none does. -/
def uptoEmpty : List Line -> List Line
  | [] => []
  | l :: rest => if l.cl = [] then [l] else l :: uptoEmpty rest

theorem AllOK_uptoEmpty {f : CNF} :
    ∀ (base : List Clause) (p : List Line), AllOK f base p -> AllOK f base (uptoEmpty p) := by
  intro base p
  induction p generalizing base with
  | nil => intro _; exact AllOK.nil f base
  | cons l rest ih =>
      intro h
      obtain ⟨hok, hall⟩ := AllOK_cons_inv h
      by_cases hl : l.cl = []
      · have h1 : uptoEmpty (l :: rest) = [l] := by simp [uptoEmpty, hl]
        rw [h1]
        exact AllOK.cons f base l [] hok (AllOK.nil f _)
      · have h1 : uptoEmpty (l :: rest) = l :: uptoEmpty rest := by simp [uptoEmpty, hl]
        rw [h1]
        exact AllOK.cons f base l (uptoEmpty rest) hok (ih (base ++ [l.cl]) hall)

theorem uptoEmpty_found {p : List Line} (h : found p = true) :
    ∃ l ∈ uptoEmpty p, l.cl = [] := by
  induction p with
  | nil => exact absurd h (by simp [found])
  | cons l rest ih =>
      by_cases hl : l.cl = []
      · have h1 : uptoEmpty (l :: rest) = [l] := by simp [uptoEmpty, hl]
        rw [h1]
        exact ⟨l, by simp, hl⟩
      · have h1 : uptoEmpty (l :: rest) = l :: uptoEmpty rest := by simp [uptoEmpty, hl]
        rw [h1]
        have hf : found rest = true := by
          rw [found_cons] at h
          exact h.resolve_left hl
        obtain ⟨x, hx, he⟩ := ih hf
        exact ⟨x, List.Mem.tail _ hx, he⟩

/-- If every line is justified and some line carries the empty clause, the checker walks to that
line and accepts: the last line it needs is the empty one, and every line before it is justified
by the lines before it. -/
theorem checkFrom_true {f : CNF} : ∀ (p : List Line) (base : List Clause),
    AllOK f base p -> (∃ l ∈ p, l.cl = []) -> checkFrom f base p = true := by
  intro p
  induction p with
  | nil => intro base _ ⟨l, h, _⟩; exact absurd h (by simp)
  | cons q rest ih =>
      intro base h hex
      obtain ⟨h1, h2⟩ := AllOK_cons_inv h
      rw [checkFrom_cons, h1]
      by_cases hq : q.cl = []
      · simp [hq]
      · simp [hq]
        obtain ⟨l, hl, he⟩ := hex
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact absurd he hq
        · exact ih (base ++ [q.cl]) h2 ⟨l, hl', he⟩

/-- **The engine output is accepted by the checker.** -/
theorem uptoEmpty_checkProof {f : CNF} {p : List Line} (hall : AllOK f [] p)
    (hf : found p = true) : checkProof f (uptoEmpty p) = true :=
  checkFrom_true (uptoEmpty p) [] (AllOK_uptoEmpty [] p hall) (uptoEmpty_found hf)

/-- The refutation produced by `fuel` rounds of saturation: the lines up to the empty clause,
or `none` if that fuel did not reach it. -/
def refutationOf (f : CNF) (fuel : Nat) : Option (List Line) :=
  if found (saturate fuel f) = true then some (uptoEmpty (saturate fuel f)) else none

/-- **Soundness of the prover.** Whatever the engine hands back, the independent checker accepts
it as a refutation of `f`. Checking is a walk over the lines: no search is replayed. -/
theorem refute_sound {f : CNF} {k : Nat} {p : List Line} (h : refutationOf f k = some p) :
    checkProof f p = true := by
  by_cases hf : found (saturate k f) = true
  · have h1 : refutationOf f k = some (uptoEmpty (saturate k f)) := by
      unfold refutationOf
      simp [hf]
    rw [h1] at h
      -- h : some (uptoEmpty (saturate k f)) = some p
    obtain rfl := Option.some.inj h
    exact uptoEmpty_checkProof (AllOK_saturate k f) hf
  · have h1 : refutationOf f k = none := by
      unfold refutationOf
      simp [hf]
    rw [h1] at h
    exact absurd h (by simp)

/-- **Soundness, semantic form.** A refutation the engine produces really refutes the formula:
this is the checker's `checkProof_sound` applied to the engine's own output. -/
theorem refute_unsat {f : CNF} {k : Nat} {p : List Line} (h : refutationOf f k = some p) :
    ProtSat.Unsat f := checkProof_sound (refute_sound h)

/-- The engine finds a refutation exactly when the saturation reaches the empty clause. -/
theorem refutationOf_some_of_found {f : CNF} {k : Nat} (h : found (saturate k f) = true) :
    ∃ p, refutationOf f k = some p := by
  refine ⟨uptoEmpty (saturate k f), ?_⟩
  unfold refutationOf
  simp [h]

theorem refutationOf_none_of_not_found {f : CNF} {k : Nat} (h : found (saturate k f) = false) :
    refutationOf f k = none := by
  unfold refutationOf
  simp [h]

/-! ### Kernel-checked gate on the demo formula -/

/-- Two rounds of saturation refute the demo formula: the first derives `[pos 0, pos 0]` and
`[neg 0, neg 0]`, the second resolves those two away. -/
def demoRefut : List Line := (refutationOf demoF 2).getD []

/-- The engine refutes `demoF` and the checker accepts it: a closed, kernel-checked statement
about the producer, not only about the checker. -/
theorem demo_refutation_checked : checkProof demoF demoRefut = true := by decide

/-- So the engine's output refutes the demo formula. -/
theorem demoRefut_unsat : ProtSat.Unsat demoF := checkProof_sound demo_refutation_checked

/-- The engine did not fall back to the empty list: it really reached the empty clause. -/
theorem demo_refutation_found : refutationOf demoF 2 ≠ none := by
  intro h
  have hfalse : checkProof demoF demoRefut = false := by
    have hd : demoRefut = [] := by simp [demoRefut, h]
    rw [hd]
    exact rejects_empty
  exact absurd demo_refutation_checked (by simp [hfalse])

/-! ### The bridge to the verdict -/

/-- A refutation the engine produces for the generated formula gives the analyser's UNSAT verdict
without running the solver: this is `encodingUnsat_of_proof` fed by the prover instead of by
hand-written evidence. -/
theorem refute_answer {P : Protocol} {B : Bounded.Bounds} {k : Nat} {p : List Line}
    (hu : univClosedBool (shapeOf P B) P = true)
    (h : refutationOf (encode P B) k = some p) :
    Analyzer.analyze P B = Analyzer.Verdict.encodingUnsat :=
  encodingUnsat_of_proof p hu (refute_sound h)

/-! ### Completeness: the engine refutes every unsatisfiable formula

The route is Davis-Putnam variable elimination. dpElim f v replaces f by the clauses that do not
mention v together with every resolvent on v; that preserves satisfiability, so eliminating all
variables of an unsatisfiable formula leaves a variable-free unsatisfiable formula, which must
contain the empty clause. Every clause the elimination produces is a line of the saturation
engine, so the empty clause is reached at fuel = (number of variables). -/

/-- A clause is tautological when it holds a variable in both polarities. -/
def taut (c : Clause) : Bool := c.any fun l => c.any fun k => l.var == k.var && l.neg == !k.neg

/-- Does v occur in c in either polarity? -/
def mentions (c : Clause) (v : BVar) : Bool := c.any fun l => l.var == v

theorem mem_taut {c : Clause} :
    taut c = true <-> ∃ l ∈ c, ∃ k ∈ c, l.var == k.var && l.neg == !k.neg := by
  simp [taut, List.any_eq_true]

/-- A predicate is false on every element of a list whose any is false. -/
theorem not_any_mem {α : Type} {l : List α} {p : α -> Bool} (h : l.any p = false) {x : α}
    (hx : x ∈ l) : p x = false := by
  cases hp : p x with
  | true =>
      have : l.any p = true := List.any_eq_true.mpr ⟨x, hx, hp⟩
      rw [this] at h
      exact absurd h (by decide)
  | false => rfl

/-- A tautological clause is satisfied by every assignment. -/
theorem taut_eval {c : Clause} (h : taut c = true) (a : Assignment) : Clause.eval a c = true := by
  obtain ⟨l, hl, k, hk, heq⟩ := mem_taut.mp h
  rw [Bool.and_eq_true] at heq
  have hv : l.var = k.var := by simpa using heq.1
  have hn : l.neg = !k.neg := by simpa using heq.2
  rw [Clause.eval, List.any_eq_true]
  cases hln : l.neg with
  | false =>
      have hk' : k.neg = true := by
        cases h2 : k.neg <;> simp_all
      cases ha : a l.var with
      | true => exact ⟨l, hl, by simp [Lit.eval, hln, ha]⟩
      | false => exact ⟨k, hk, by simp [Lit.eval, hk', ← hv, ha]⟩
  | true =>
      have hk' : k.neg = false := by
        cases h2 : k.neg <;> simp_all
      cases ha : a l.var with
      | true => exact ⟨k, hk, by simp [Lit.eval, hk', ← hv, ha]⟩
      | false => exact ⟨l, hl, by simp [Lit.eval, hln, ha]⟩

/-- Set one variable of an assignment. -/
def setVar (a : Assignment) (v : BVar) (b : Bool) : Assignment := fun x => if x = v then b else a x

@[simp] theorem setVar_eq (a : Assignment) (v : BVar) (b : Bool) : setVar a v b v = b := by
  simp [setVar]

theorem setVar_ne (a : Assignment) {v w : BVar} (b : Bool) (h : w ≠ v) :
    setVar a v b w = a w := by
  simp [setVar, h]

theorem lit_eval_setVar {a : Assignment} {l : Lit} {v : BVar} (b : Bool) (h : l.var ≠ v) :
    Lit.eval (setVar a v b) l = Lit.eval a l := by
  unfold Lit.eval
  rw [setVar_ne a b h]

/-- A clause all of whose literals are false is unsatisfied. -/
theorem clause_eval_false_of_all {a : Assignment} {c : Clause}
    (h : ∀ l ∈ c, Lit.eval a l = false) : Clause.eval a c = false := by
  cases hc : Clause.eval a c with
  | true =>
      rw [Clause.eval, List.any_eq_true] at hc
      obtain ⟨l, hl, he⟩ := hc
      have := h l hl
      rw [this] at he
      exact absurd he (by decide)
  | false => rfl

/-- Two assignments that agree on the literals of c agree on whether c holds. -/
theorem clause_eval_congr {a b : Assignment} {c : Clause}
    (h : ∀ l ∈ c, Lit.eval a l = Lit.eval b l) : Clause.eval a c = Clause.eval b c := by
  unfold Clause.eval
  induction c with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.any_cons, h x (List.Mem.head _),
        ih (fun l hl => h l (List.Mem.tail _ hl))]

theorem clause_eval_congr_off {a : Assignment} {c : Clause} {v : BVar} (b : Bool)
    (h : ∀ l ∈ c, l.var ≠ v) : Clause.eval (setVar a v b) c = Clause.eval a c :=
  clause_eval_congr (fun l hl => lit_eval_setVar b (h l hl))

/-- A literal of a clause falsified by setVar a v b, away from v, is false under a. -/
theorem lit_eval_of_eval_set_false {a : Assignment} {c : Clause} {v : BVar} {b : Bool}
    (h : Clause.eval (setVar a v b) c = false) {l : Lit} (hl : l ∈ c) (hv : l.var ≠ v) :
    Lit.eval a l = false := by
  have h2 : Lit.eval (setVar a v b) l = false :=
    not_any_mem (show c.any (fun k => Lit.eval (setVar a v b) k) = false from h) hl
  rw [← lit_eval_setVar b hv]
  exact h2

/-- Setting v true satisfies every clause with a positive occurrence of v. -/
theorem eval_setVar_true_of_hasPos {a : Assignment} {c : Clause} {v : BVar}
    (h : hasPos c v = true) : Clause.eval (setVar a v true) c = true := by
  obtain ⟨l, hl, heq⟩ := List.any_eq_true.mp h
  rw [Bool.and_eq_true] at heq
  have hv : l.var = v := beq_iff_eq.mp heq.1
  have hn : l.neg = false := by simpa using heq.2
  rw [Clause.eval, List.any_eq_true]
  exact ⟨l, hl, by simp [Lit.eval, hn, hv, setVar]⟩

/-- Setting v false satisfies every clause with a negative occurrence of v. -/
theorem eval_setVar_false_of_hasNeg {a : Assignment} {c : Clause} {v : BVar}
    (h : hasNeg c v = true) : Clause.eval (setVar a v false) c = true := by
  obtain ⟨l, hl, heq⟩ := List.any_eq_true.mp h
  rw [Bool.and_eq_true] at heq
  have hv : l.var = v := beq_iff_eq.mp heq.1
  have hn : l.neg = true := heq.2
  rw [Clause.eval, List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  unfold Lit.eval
  rw [hn, hv, setVar_eq]
  decide

theorem clause_eval_append {a : Assignment} (x y : Clause) :
    Clause.eval a (x ++ y) = (Clause.eval a x || Clause.eval a y) := by
  simp [Clause.eval, List.any_append]

/-- A variable that occurs in a clause occurs with one polarity or the other. -/
theorem mentions_iff {c : Clause} {v : BVar} :
    mentions c v = true <-> hasPos c v = true ∨ hasNeg c v = true := by
  unfold mentions hasPos hasNeg
  rw [List.any_eq_true, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, h1⟩
    cases hln : l.neg with
    | false => left; exact ⟨l, hl, by simp [hln, h1]⟩
    | true => right; exact ⟨l, hl, by simp [hln, h1]⟩
  · intro hOr
    rcases hOr with ⟨l, hl, h2⟩ | ⟨l, hl, h2⟩
    · rw [Bool.and_eq_true] at h2
      exact ⟨l, hl, h2.1⟩
    · rw [Bool.and_eq_true] at h2
      exact ⟨l, hl, h2.1⟩

theorem not_mentions {c : Clause} {v : BVar} (h : mentions c v = false) {l : Lit} (hl : l ∈ c) :
    l.var ≠ v := by
  intro heq
  have h2 : mentions c v = true := by
    unfold mentions
    exact List.any_eq_true.mpr ⟨l, hl, by simp [heq]⟩
  rw [h2] at h
  exact absurd h (by decide)

/-- **The resolvents used by the elimination**: every resolvent on v of two non-tautological
clauses of f. -/
def resolventsOn (f : CNF) (v : BVar) : List Clause :=
  (f.clauses.filter fun c => !taut c).flatMap fun c₁ =>
    (f.clauses.filter fun c => !taut c).filterMap fun c₂ =>
      if hasPos c₁ v && hasNeg c₂ v then some (resolve c₁ c₂ v) else none

theorem mem_resolventsOn {f : CNF} {v : BVar} {c : Clause} :
    c ∈ resolventsOn f v <->
      ∃ c₁ c₂, c₁ ∈ f.clauses ∧ c₂ ∈ f.clauses ∧ taut c₁ = false ∧ taut c₂ = false ∧
        hasPos c₁ v = true ∧ hasNeg c₂ v = true ∧ c = resolve c₁ c₂ v := by
  unfold resolventsOn
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    obtain ⟨c₁, hc₁, h2⟩ := h
    rw [List.mem_filter] at hc₁
    rw [List.mem_filterMap] at h2
    obtain ⟨c₂, hc₂, h3⟩ := h2
    rw [List.mem_filter] at hc₂
    by_cases hp : hasPos c₁ v = true
    · by_cases hn : hasNeg c₂ v = true
      · have hred : (if hasPos c₁ v && hasNeg c₂ v then some (resolve c₁ c₂ v)
            else none) = some (resolve c₁ c₂ v) := by simp [hp, hn]
        rw [hred] at h3
        exact ⟨c₁, c₂, hc₁.1, hc₂.1, by simp_all, by simp_all, hp, hn, (Option.some.inj h3).symm⟩
      · have hred : (if hasPos c₁ v && hasNeg c₂ v then some (resolve c₁ c₂ v)
            else none) = (none : Option Clause) := by simp [hn]
        rw [hred] at h3
        exact absurd h3 (by simp)
    · have hred : (if hasPos c₁ v && hasNeg c₂ v then some (resolve c₁ c₂ v)
          else none) = (none : Option Clause) := by simp [hp]
      rw [hred] at h3
      exact absurd h3 (by simp)
  · rintro ⟨c₁, c₂, hc₁, hc₂, ht₁, ht₂, hp, hn, rfl⟩
    have h1 : c₁ ∈ f.clauses.filter (fun c => !taut c) :=
      List.mem_filter.mpr ⟨hc₁, by simp [ht₁]⟩
    have h2 : c₂ ∈ f.clauses.filter (fun c => !taut c) :=
      List.mem_filter.mpr ⟨hc₂, by simp [ht₂]⟩
    have h3 : resolve c₁ c₂ v ∈
        (f.clauses.filter (fun c => !taut c)).filterMap fun c₂ =>
          if hasPos c₁ v && hasNeg c₂ v then some (resolve c₁ c₂ v) else none :=
      List.mem_filterMap.mpr ⟨c₂, h2, by simp [hp, hn]⟩
    exact List.mem_flatMap.mpr ⟨c₁, h1, h3⟩

/-- **Davis-Putnam elimination of v**: the non-tautological clauses that do not mention v, plus
every resolvent on v. Tautological clauses are dropped - every assignment satisfies them - which
is what keeps the resolvents free of v. -/
def dpElim (f : CNF) (v : BVar) : CNF :=
  ⟨ (f.clauses.filter fun c => !taut c && !mentions c v) ++ resolventsOn f v ⟩

theorem dpElim_clauses (f : CNF) (v : BVar) :
    (dpElim f v).clauses =
      (f.clauses.filter fun c => !taut c && !mentions c v) ++ resolventsOn f v := rfl

/-- Every model of f is a model of dpElim f v: resolvents are consequences of their parents. -/
theorem sat_dpElim {f : CNF} {v : BVar} (a : Assignment) (ha : Sat a f) : Sat a (dpElim f v) := by
  intro c hc
  rw [dpElim_clauses, List.mem_append] at hc
  rcases hc with hc | hc
  · rw [List.mem_filter] at hc
    exact ha c hc.1
  · obtain ⟨c₁, c₂, hc₁, hc₂, _, _, hp, hn, rfl⟩ := mem_resolventsOn.mp hc
    exact eval_resolve (ha c₁ hc₁) (ha c₂ hc₂) hp hn

/-- A formula some assignment fails to satisfy has a clause that assignment falsifies. -/
theorem not_sat_exists {f : CNF} {a : Assignment} (h : ¬ Sat a f) :
    ∃ c ∈ f.clauses, Clause.eval a c = false := by
  rw [Sat] at h
  push Not at h
  obtain ⟨c, hc, hne⟩ := h
  cases he : Clause.eval a c with
  | true => exact absurd he hne
  | false => exact ⟨c, hc, he⟩

/-- A Boolean that is false is not true. -/
theorem bool_ne_true {p : Bool} (h : p = false) : ¬ (p = true) := by
  rw [h]
  decide

/-- In a clause with no negative occurrence of the pivot, the positive-pivot filter keeps only
literals away from the pivot. -/
theorem off_of_filter_pos {c : Clause} {v : BVar} (hn : hasNeg c v = false) {l : Lit}
    (hl : l ∈ c.filter fun x => !(x.var == v && !x.neg)) : l.var ≠ v := by
  rw [List.mem_filter] at hl
  intro heq
  have hlv : (l.var == v) = true := by simp [heq]
  have hln : l.neg = true := by
    have h2 := hl.2
    rw [hlv] at h2
    simp at h2
    exact h2
  have hneg : hasNeg c v = true := by
    unfold hasNeg
    exact List.any_eq_true.mpr ⟨l, hl.1, by rw [Bool.and_eq_true]; exact ⟨hlv, hln⟩⟩
  exact absurd hneg (bool_ne_true hn)

/-- In a clause with no positive occurrence of the pivot, the negative-pivot filter keeps only
literals away from the pivot. -/
theorem off_of_filter_neg {c : Clause} {v : BVar} (hp : hasPos c v = false) {l : Lit}
    (hl : l ∈ c.filter fun x => !(x.var == v && x.neg)) : l.var ≠ v := by
  rw [List.mem_filter] at hl
  intro heq
  have hlv : (l.var == v) = true := by simp [heq]
  have hln : l.neg = false := by
    have h2 := hl.2
    rw [hlv] at h2
    simp at h2
    exact h2
  have hpos : hasPos c v = true := by
    unfold hasPos
    exact List.any_eq_true.mpr ⟨l, hl.1, by rw [Bool.and_eq_true]; exact ⟨hlv, by simp [hln]⟩⟩
  exact absurd hpos (bool_ne_true hp)

/-- **The hard direction of the elimination lemma.** A model of `dpElim f v` can be extended to
a model of `f`: try `v := true`; if that fails, some clause `c₁` of `f` is falsified, which
forces `c₁` to be non-tautological and to contain `v` only negatively; try `v := false`
instead, and if that also fails, the resolvent of the two falsified clauses is a clause of
`dpElim f v` that neither polarity of `v` can rescue - contradiction. -/
theorem sat_exists_of_dpElim {f : CNF} {v : BVar} (h : Satisfiable (dpElim f v)) :
    Satisfiable f := by
  obtain ⟨a, ha⟩ := h
  by_cases h1 : Sat (setVar a v true) f
  · exact ⟨setVar a v true, h1⟩
  · obtain ⟨c₁, hc₁, ne₁⟩ := not_sat_exists h1
    by_cases h2 : Sat (setVar a v false) f
    · exact ⟨setVar a v false, h2⟩
    · obtain ⟨c₂, hc₂, ne₂⟩ := not_sat_exists h2
      -- both falsified clauses are non-tautological
      have nt₁ : taut c₁ = false := by
        cases h : taut c₁ with
        | true => exact absurd (taut_eval h (setVar a v true)) (bool_ne_true ne₁)
        | false => rfl
      have nt₂ : taut c₂ = false := by
        cases h : taut c₂ with
        | true => exact absurd (taut_eval h (setVar a v false)) (bool_ne_true ne₂)
        | false => rfl
      -- c₁ has no positive occurrence of v; c₂ has no negative occurrence
      have noPos₁ : hasPos c₁ v = false := by
        cases h : hasPos c₁ v with
        | true => exact absurd (eval_setVar_true_of_hasPos h) (bool_ne_true ne₁)
        | false => rfl
      have noNeg₂ : hasNeg c₂ v = false := by
        cases h : hasNeg c₂ v with
        | true => exact absurd (eval_setVar_false_of_hasNeg h) (bool_ne_true ne₂)
        | false => rfl
      -- c₁ mentions v (negatively); c₂ mentions v (positively)
      have men₁ : mentions c₁ v = true := by
        cases hm : mentions c₁ v with
        | true => rfl
        | false =>
            have hmem : c₁ ∈ (dpElim f v).clauses := by
              rw [dpElim_clauses, List.mem_append]
              exact Or.inl (List.mem_filter.mpr ⟨hc₁, by simp [nt₁, hm]⟩)
            have hcongr : Clause.eval (setVar a v true) c₁ = Clause.eval a c₁ :=
              clause_eval_congr_off true (fun l hl => not_mentions hm hl)
            rw [hcongr] at ne₁
            rw [ha c₁ hmem] at ne₁
            exact absurd ne₁ (by decide)
      have men₂ : mentions c₂ v = true := by
        cases hm : mentions c₂ v with
        | true => rfl
        | false =>
            have hmem : c₂ ∈ (dpElim f v).clauses := by
              rw [dpElim_clauses, List.mem_append]
              exact Or.inl (List.mem_filter.mpr ⟨hc₂, by simp [nt₂, hm]⟩)
            have hcongr : Clause.eval (setVar a v false) c₂ = Clause.eval a c₂ :=
              clause_eval_congr_off false (fun l hl => not_mentions hm hl)
            rw [hcongr] at ne₂
            rw [ha c₂ hmem] at ne₂
            exact absurd ne₂ (by decide)
      have neg₁ : hasNeg c₁ v = true := by
        rw [mentions_iff] at men₁
        cases men₁ with
        | inl hp => exact absurd hp (bool_ne_true noPos₁)
        | inr hn => exact hn
      have pos₂ : hasPos c₂ v = true := by
        rw [mentions_iff] at men₂
        cases men₂ with
        | inl hp => exact hp
        | inr hn => exact absurd hn (bool_ne_true noNeg₂)
      -- the resolvent is a clause of dpElim f v, and a falsifies it
      have hres : resolve c₂ c₁ v ∈ (dpElim f v).clauses := by
        rw [dpElim_clauses, List.mem_append]
        exact Or.inr (mem_resolventsOn.mpr
          ⟨c₂, c₁, hc₂, hc₁, nt₂, nt₁, pos₂, neg₁, rfl⟩)
      have ha' := ha (resolve c₂ c₁ v) hres
      have hf : Clause.eval a (resolve c₂ c₁ v) = false := by
        unfold resolve
        rw [clause_eval_append]
        refine Bool.or_eq_false_iff.mpr ⟨?_, ?_⟩
        · refine clause_eval_false_of_all (fun l hl => ?_)
          have := lit_eval_of_eval_set_false (b := false) ne₂ (List.mem_of_mem_filter hl)
            (off_of_filter_pos noNeg₂ hl)
          exact this
        · refine clause_eval_false_of_all (fun l hl => ?_)
          have := lit_eval_of_eval_set_false (b := true) ne₁ (List.mem_of_mem_filter hl)
            (off_of_filter_neg noPos₁ hl)
          exact this
      exact absurd ha' (bool_ne_true hf)

/-- **Davis-Putnam elimination preserves satisfiability.** -/
theorem dpElim_sat {f : CNF} {v : BVar} : Satisfiable (dpElim f v) <-> Satisfiable f :=
  ⟨fun h => sat_exists_of_dpElim h, fun ⟨a, ha⟩ => ⟨a, sat_dpElim a ha⟩⟩

/-! ### The payoff: a safety verdict carried by produced evidence

`CheckedSafe.boundedSafe_of_checkedProof` turns a *checked* refutation into
`boundedSafeGoals q`. Composed with `refute_sound`, the verdict now comes from evidence the
engine *produced*: no solver runs anywhere in the chain, and the only thing trusted is
`checkProof`. -/

/-- **From produced evidence to the security statement.** The hypotheses are exactly the ones
`CheckedSafe` needs: the goals the query selected are ones the encoding represents, the query is
non-empty, and the three representability conditions on the shape. -/
theorem boundedSafe_of_refutation {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsec : SecretsOK (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) {k : Nat} {p : List Line}
    (h : refutationOf (encode q.protocol q.bounds) k = some p) : boundedSafeGoals q :=
  boundedSafe_of_checkedProof hq hne hU hsec hgap (refute_sound h)

/-- The same verdict as evidence: a `SafeEvidence` whose refutation was produced here rather than
supplied by hand. -/
def safeEvidence_of_refutation {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsec : SecretsOK (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) {k : Nat} {p : List Line}
    (h : refutationOf (encode q.protocol q.bounds) k = some p) : SafeEvidence :=
  safeEvidenceOfProof hq hne hU hsec hgap p (refute_sound h)

/-- **The engine's own output survives the byte round trip.** Serialize the refutation the engine
emitted, hand the integers back to the decoder, and the checker still accepts: bytes -> proof ->
formula fact, with the producer on both ends. -/
theorem demo_refutation_round_trip :
    checkCode demoF (demoRefut.length + 1) (proofCode demoRefut) = true := by
  rw [checkCode_of (proofOfCode_proofCode' demoRefut)]
  exact demo_refutation_checked

/-- So the serialized engine output refutes the demo formula too. -/
theorem demo_refutation_round_trip_unsat : ProtSat.Unsat demoF :=
  checkCode_sound demo_refutation_round_trip

/-! ### The elimination reaches the empty clause, and the engine reaches it too -/

/-- The variables a formula mentions, with repetitions. -/
def varsOf (f : CNF) : List BVar := f.clauses.flatMap fun c => c.map Lit.var

/-- A formula no variable occurs in: every clause is empty. -/
def varFree (f : CNF) : Prop := ∀ c ∈ f.clauses, c = []

/-- Eliminate the variables of vs one after another. -/
def elimAll : CNF -> List BVar -> CNF
  | f, [] => f
  | f, v :: vs => elimAll (dpElim f v) vs

theorem elimAll_nil (f : CNF) : elimAll f [] = f := rfl

theorem elimAll_cons (f : CNF) (v : BVar) (vs : List BVar) :
    elimAll f (v :: vs) = elimAll (dpElim f v) vs := rfl

/-- **Eliminating a list of variables preserves satisfiability.** -/
theorem elimAll_sat : ∀ (vs : List BVar) (f : CNF),
    Satisfiable (elimAll f vs) <-> Satisfiable f := by
  intro vs
  induction vs with
  | nil => intro f; simp [elimAll_nil]
  | cons v rest ih =>
      intro f
      rw [elimAll_cons]
      exact Iff.trans (ih (dpElim f v)) dpElim_sat

/-- Both polarities of one variable in a clause make it tautological. -/
theorem taut_of_hasPos_hasNeg {c : Clause} {v : BVar} (hp : hasPos c v = true)
    (hn : hasNeg c v = true) : taut c = true := by
  obtain ⟨l, hl, heq⟩ := List.any_eq_true.mp hp
  obtain ⟨k, hk, heq'⟩ := List.any_eq_true.mp hn
  rw [Bool.and_eq_true] at heq heq'
  have h1 : l.var = v := beq_iff_eq.mp heq.1
  have h2 : l.neg = false := by simpa using heq.2
  have h3 : k.var = v := beq_iff_eq.mp heq'.1
  have h4 : k.neg = true := heq'.2
  rw [mem_taut]
  exact ⟨l, hl, k, hk, by rw [Bool.and_eq_true]; exact ⟨by simp [h1, h3], by simp [h2, h4]⟩⟩

theorem not_hasNeg_of_taut_false {c : Clause} {v : BVar} (ht : taut c = false)
    (hp : hasPos c v = true) : hasNeg c v = false := by
  cases h : hasNeg c v with
  | true => exact absurd (taut_of_hasPos_hasNeg hp h) (bool_ne_true ht)
  | false => rfl

theorem not_hasPos_of_taut_false {c : Clause} {v : BVar} (ht : taut c = false)
    (hn : hasNeg c v = true) : hasPos c v = false := by
  cases h : hasPos c v with
  | true => exact absurd (taut_of_hasPos_hasNeg h hn) (bool_ne_true ht)
  | false => rfl

/-- A literal of a resolvent came from one of its parents. -/
theorem mem_resolve {c₁ c₂ : Clause} {v : BVar} {l : Lit} (hl : l ∈ resolve c₁ c₂ v) :
    l ∈ c₁.filter (fun x => !(x.var == v && !x.neg)) ∨
      l ∈ c₂.filter (fun x => !(x.var == v && x.neg)) := by
  unfold resolve at hl
  rw [List.mem_append] at hl
  exact hl

/-- Eliminating every variable that occurs leaves nothing but empty clauses. -/
theorem elimAll_varFree : ∀ (vs : List BVar) (f : CNF),
    (∀ c ∈ f.clauses, ∀ l ∈ c, l.var ∈ vs) -> varFree (elimAll f vs) := by
  intro vs
  induction vs with
  | nil =>
      intro g h c hc
      cases c with
      | nil => rfl
      | cons l rest => exact absurd (h (l :: rest) hc l (List.Mem.head _)) (by simp)
  | cons v rest ih =>
      intro g h c hc
      rw [elimAll_cons] at hc
      refine ih (dpElim g v) ?_ c hc
      intro c' hc' l hl
      rw [dpElim_clauses, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · rw [List.mem_filter] at hc'
        obtain ⟨hc₁', hcond⟩ := hc'
        rw [Bool.and_eq_true] at hcond
        have := h c' hc₁' l hl
        rcases List.mem_cons.mp this with rfl | hrest
        · exact absurd (not_mentions (by simpa using hcond.2) hl) (by simp)
        · exact hrest
      · obtain ⟨c₁, c₂, hc₁, hc₂, ht₁, ht₂, hp, hn, rfl⟩ := mem_resolventsOn.mp hc'
        have hv : l.var ≠ v := by
          rcases mem_resolve hl with h1 | h1
          · exact off_of_filter_pos (not_hasNeg_of_taut_false ht₁ hp) h1
          · exact off_of_filter_neg (not_hasPos_of_taut_false ht₂ hn) h1
        rcases mem_resolve hl with h1 | h1
        · have := h c₁ hc₁ l (List.mem_of_mem_filter h1)
          rcases List.mem_cons.mp this with rfl | hrest
          · exact absurd hv (by simp)
          · exact hrest
        · have := h c₂ hc₂ l (List.mem_of_mem_filter h1)
          rcases List.mem_cons.mp this with rfl | hrest
          · exact absurd hv (by simp)
          · exact hrest

/-- The clauses of the formula are lines of its own saturation at fuel 0. -/
theorem clList_seed : ∀ (fs : List Clause) (i : Nat), clList (seed fs i) = fs := by
  intro fs
  induction fs with
  | nil => intro i; rfl
  | cons c rest ih =>
      intro i
      have hseed : seed (c :: rest) i = { cl := c, why := Just.orig i } :: seed rest (i + 1) := rfl
      rw [hseed, clList_cons, ih (i + 1)]

theorem mem_clList_seed {f : CNF} {c : Clause} (h : c ∈ f.clauses) :
    c ∈ clList (saturate 0 f) := by
  have h0 : saturate 0 f = seed f.clauses 0 := rfl
  rw [h0, clList_seed]
  exact h

/-- Saturation only ever adds lines. -/
theorem mem_saturate_add {f : CNF} {k n : Nat} {l : Line} (h : l ∈ saturate k f) :
    l ∈ saturate (k + n) f := by
  induction n with
  | zero => simpa using h
  | succ n' ih =>
      have heq : saturate (k + n'.succ) f =
          saturate (k + n') f ++ step (saturate (k + n') f) := rfl
      rw [heq]
      exact List.mem_append.mpr (Or.inl ih)

theorem mem_clList_saturate_add {f : CNF} {k n : Nat} {c : Clause}
    (h : c ∈ clList (saturate k f)) : c ∈ clList (saturate (k + n) f) := by
  unfold clList at *
  rw [List.mem_map] at *
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, mem_saturate_add hl, rfl⟩

/-- The lines a round produces stay in the next saturation. -/
theorem mem_clList_step_add {f : CNF} {k : Nat} {c : Clause}
    (h : c ∈ clList (step (saturate k f))) : c ∈ clList (saturate (k + 1) f) := by
  have heq : saturate (k + 1) f = saturate k f ++ step (saturate k f) := rfl
  rw [heq, ← clList_append, List.mem_append]
  exact Or.inr h

/-- Deduplication never loses a clause: a candidate clause is either kept or was already there. -/
theorem mem_novel_or : ∀ (seen : List Clause) (cand : List Line) (cl : Clause),
    cl ∈ clList cand → cl ∈ clList (novel seen cand) ∨ cl ∈ seen := by
  intro seen cand
  induction cand generalizing seen with
  | nil => intro cl h; exact absurd h (by simp [clList_nil])
  | cons a rest ih =>
      intro cl h
      by_cases hm : a.cl ∈ seen
      · have h1 : novel seen (a :: rest) = novel seen rest := by simp [novel_cons, hm]
        rw [h1]
        have hmem : cl ∈ a.cl :: clList rest := by rwa [clList_cons] at h
        rcases List.mem_cons.mp hmem with heq | hmem
        · exact Or.inr (heq ▸ hm)
        · exact ih seen cl hmem
      · have h1 : novel seen (a :: rest) = a :: novel (seen ++ [a.cl]) rest := by
          simp [novel_cons, hm]
        rw [h1]
        have hmem : cl ∈ a.cl :: clList rest := by rwa [clList_cons] at h
        rcases List.mem_cons.mp hmem with heq | hmem
        · exact Or.inl (by rw [clList_cons, heq]; exact List.Mem.head _)
        · cases ih (seen ++ [a.cl]) cl hmem with
          | inl h2 => exact Or.inl (List.mem_cons.mpr (Or.inr h2))
          | inr h2 =>
              rw [List.mem_append, List.mem_singleton] at h2
              rcases h2 with h2 | h2'
              · exact Or.inr h2
              · exact Or.inl (by rw [clList_cons, ← h2']; exact List.Mem.head _)

/-- Every resolvent of two lines of the saturation is either produced by the next round or was
already there. -/
theorem resolvent_in_step {acc : List Line} {c₁ c₂ : Clause} {v : BVar}
    (h₁ : c₁ ∈ clList acc) (h₂ : c₂ ∈ clList acc) (hp : hasPos c₁ v = true)
    (hn : hasNeg c₂ v = true) :
    resolve c₁ c₂ v ∈ clList (step acc) ∨ resolve c₁ c₂ v ∈ clList acc := by
  obtain ⟨i, hi⟩ := exists_rget_of_mem (clList acc) c₁ h₁
  obtain ⟨j, hj⟩ := exists_rget_of_mem (clList acc) c₂ h₂
  obtain ⟨l, hl, heq⟩ := List.any_eq_true.mp hp
  rw [Bool.and_eq_true] at heq
  have hlv : l.var = v := beq_iff_eq.mp heq.1
  have hln : l.neg = false := by simpa using heq.2
  have hmem : l ∈ c₁.filter (fun x => !x.neg) := List.mem_filter.mpr ⟨hl, by simp [hln]⟩
  have hline : ({ cl := resolve c₁ c₂ v, why := Just.res i j v } : Line) ∈ resols acc i j := by
    rw [resols_some hi hj, List.mem_flatMap]
    refine ⟨l, hmem, ?_⟩
    have hif : (if hasNeg c₂ l.var = true then
            ([{ cl := resolve c₁ c₂ l.var, why := Just.res i j l.var }] : List Line)
          else ([] : List Line))
          = ([{ cl := resolve c₁ c₂ v, why := Just.res i j v }] : List Line) := by
      rw [hlv]
      simp [hn]
    rw [hif]
    simp
  have hlen_i : i < acc.length := by
    have : i < (clList acc).length := rget_lt_of_some (clList acc) i c₁ hi
    simpa [clList, List.length_map] using this
  have hlen_j : j < acc.length := by
    have : j < (clList acc).length := rget_lt_of_some (clList acc) j c₂ hj
    simpa [clList, List.length_map] using this
  have hcand : ({ cl := resolve c₁ c₂ v, why := Just.res i j v } : Line) ∈ candidates acc := by
    unfold candidates
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_range.mpr hlen_i,
      List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hlen_j, hline⟩⟩
  have hnov : resolve c₁ c₂ v ∈ clList (novel (clList acc) (candidates acc))
      ∨ resolve c₁ c₂ v ∈ clList acc :=
    mem_novel_or (clList acc) (candidates acc) (resolve c₁ c₂ v)
      (List.mem_map.mpr ⟨_, hcand, rfl⟩)
  cases hnov with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h

/-- **Coverage.** Every clause the elimination produces is a line of the engine's saturation of
the *original* formula, one engine round per eliminated variable. -/
theorem dpElim_covered {g f : CNF} {v : BVar} {k : Nat}
    (h : ∀ c ∈ g.clauses, c ∈ clList (saturate k f)) :
    ∀ c ∈ (dpElim g v).clauses, c ∈ clList (saturate (k + 1) f) := by
  intro c hc
  rw [dpElim_clauses, List.mem_append] at hc
  rcases hc with hc | hc
  · rw [List.mem_filter] at hc
    exact mem_clList_saturate_add (n := 1) (h c hc.1)
  · obtain ⟨c₁, c₂, hc₁, hc₂, _, _, hp, hn, rfl⟩ := mem_resolventsOn.mp hc
    rcases @resolvent_in_step (saturate k f) c₁ c₂ v (h c₁ hc₁) (h c₂ hc₂) hp hn
        with hres | hres
    · exact mem_clList_step_add hres
    · exact mem_clList_saturate_add (n := 1) hres

theorem elimAll_covered : ∀ (vs : List BVar) (g f : CNF) (k : Nat),
    (∀ c ∈ g.clauses, c ∈ clList (saturate k f)) ->
    ∀ c ∈ (elimAll g vs).clauses, c ∈ clList (saturate (k + vs.length) f) := by
  intro vs
  induction vs with
  | nil => intro g f k h c hc; simpa using h c hc
  | cons v rest ih =>
      intro g f k h c hc
      rw [elimAll_cons] at hc
      rw [List.length_cons]
      have hidx : k + 1 + rest.length = k + (rest.length + 1) := by omega
      rw [← hidx]
      exact ih (dpElim g v) f (k + 1) (dpElim_covered h) c hc

/-! ### The completeness theorem -/

/-- **Completeness of the engine.** If a formula has no model, some amount of fuel makes the
engine emit a refutation - so the engine is not merely a sound way to check, it is a prover: for
every unsatisfiable formula there is evidence to find. The fuel it needs is the number of
variables of the formula, one saturation round per eliminated variable; the cost per round is
another matter, and it is the reason this is a completeness theorem and not a solver. -/
theorem refute_complete {f : CNF} (h : ProtSat.Unsat f) : ∃ k p, refutationOf f k = some p := by
  -- every clause the elimination derives is a line of the saturation of f
  have hcover : ∀ c ∈ (elimAll f (varsOf f)).clauses,
      c ∈ clList (saturate (varsOf f).length f) := by
    intro c hc
    have := elimAll_covered (varsOf f) f f 0 (by intro c' hc'; exact mem_clList_seed hc') c hc
    rw [Nat.zero_add] at this
    exact this
  -- eliminating every variable that occurs leaves only empty clauses behind
  have hvf : varFree (elimAll f (varsOf f)) :=
    elimAll_varFree (varsOf f) f (by
      intro c hc l hl
      exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)
  have hun : ProtSat.Unsat (elimAll f (varsOf f)) :=
    fun hs => h ((elimAll_sat (varsOf f) f).mp hs)
  have hempty : [] ∈ (elimAll f (varsOf f)).clauses := by
    by_contra hc
    refine hun ⟨fun _ => false, fun c hc' => ?_⟩
    have hnil : c = [] := hvf c hc'
    have : [] ∈ (elimAll f (varsOf f)).clauses := by rw [← hnil]; exact hc'
    exact absurd this hc
  -- so the saturation of f contains the empty clause, and the engine reports a refutation
  have hfound : [] ∈ clList (saturate (varsOf f).length f) := hcover _ hempty
  unfold clList at hfound
  obtain ⟨l, hl, heq⟩ := List.mem_map.mp hfound
  obtain ⟨p, hp⟩ := refutationOf_some_of_found (Iff.mpr (found_eq _) ⟨l, hl, heq⟩)
  exact ⟨(varsOf f).length, p, hp⟩

/-- Completeness plus soundness: the engine's output is accepted, and accepted output refutes.
Together these say `refutationOf` is a decision procedure for unsatisfiability in the limit of
unbounded fuel - the evidence half of roadmap stage 6. -/
theorem refute_iff {f : CNF} :
    ProtSat.Unsat f <-> ∃ k p, refutationOf f k = some p ∧ checkProof f p = true := by
  constructor
  · intro h
    obtain ⟨k, p, hk⟩ := refute_complete h
    exact ⟨k, p, hk, refute_sound hk⟩
  · rintro ⟨k, p, hk, _⟩
    exact refute_unsat hk

/-- The engine does not refute a satisfiable formula, for any fuel: soundness plus the checker's
own soundness already imply it, and it is worth writing down because it is the half of the story
that says the engine cannot lie. -/
theorem not_refutable_of_satisfiable {f : CNF} (h : Satisfiable f) (k : Nat) :
    refutationOf f k = none := by
  cases h' : refutationOf f k with
  | none => rfl
  | some p => exact absurd (refute_unsat h') (fun hu => hu h)

/-- A refutation of the demo formula, produced rather than written: the completeness theorem
evaluated at a concrete formula, with the fuel the engine actually needs. -/
example : ∃ k p, refutationOf demoF k = some p := refute_complete demoF_unsat

end ProtSat.Refute
