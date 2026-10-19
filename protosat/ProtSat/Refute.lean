/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

import ProtSat.Resolution

/-!
# ProtSat: a prover that emits independently checkable refutations

## Why this module exists

`Resolution.checkProof` can *verify* a resolution refutation, and
`Resolution.encodingUnsat_of_proof` turns a checked refutation into the analyser's
`encodingUnsat` verdict without replaying any search. What was missing is the other half
of the evidence pipeline: nothing *produced* a refutation. Roadmap stage 6 asks for a search
that emits evidence and a small independent checker that decides; this module is the search.

The engine is saturation by resolution. Round 0 seeds the formula, one line per clause, each
justified by `Just.orig`. Every further round appends the resolvent of every ordered pair of
lines built so far, on every pivot the checker's own side conditions accept, and drops clauses
the list already carries. `refutationOf f k` reads off the lines up to the first empty
clause. Termination is by fuel, so the engine cannot loop; deduplication keeps the closure
small enough for the kernel to evaluate it.

The property that matters is not that the engine is clever but that its output is accepted by
a checker it shares no code with beyond the clause vocabulary:

```lean
refute_sound  : refutationOf f k = some p -> checkProof f p = true
refute_unsat  : refutationOf f k = some p -> ProtSat.Unsat f
refute_answer : refutationOf (encode P B) k = some p -> analyze P B = encodingUnsat
```

`refute_sound` is proved by showing every line the engine emits is `lineOK` with respect to
the lines before it (`AllOK`), and that a list of justified lines containing the empty clause
is accepted by `checkFrom`. `demo_refutation_checked` is the closed, kernel-checked statement
that this really happens on a formula.

## What this does not do

It is not a fast solver. Saturation by resolution with no subsumption, no unit propagation and
no learning is exponential, and the fuel bound is a wall, not a strategy. Nothing here replaces
`DPLL.dpll` for *finding* models: a SAT answer still comes from the search. Only the UNSAT
side is what this module certifies.

Nothing in this module is trusted by the checker: `checkProof` re-derives every line from the
formula, so a bug in the engine can make it fail to find a refutation but can never make the
checker accept a false one.
-/

namespace ProtSat.Refute

open ProtSat
open ProtSat.Resolution
open ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer


open ProtSat
open ProtSat.Resolution
open ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer

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

/-- One saturation round: every resolvent of every ordered pair of lines of `acc`, minus the
clauses `acc` already carries. -/
def step (acc : List Line) : List Line :=
  novel (clList acc) ((List.range acc.length).flatMap fun i =>
    (List.range acc.length).flatMap fun j => resols acc i j)

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

end ProtSat.Refute
