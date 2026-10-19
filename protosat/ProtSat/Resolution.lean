/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Analyzer

/-!
# ProtSat: independently checkable UNSAT evidence (roadmap stage 6)

## Why this module exists

`Analyzer.analyze` answers `encodingUnsat` when `DPLL.dpll (encode P B) = none`, and
`DPLL.dpll_complete` turns that equation into `Unsat (encode P B)`. But the equation itself is a
*computation of the solver*: to believe it in the kernel you must re-run the solver in the kernel.
`EndToEnd.lean` measures that at minutes for a few hundred variables and beyond feasibility for a
thousand. That is the wrong shape of trust: the answer is certified by replaying the search.

Roadmap stage 6 asks for the other shape. A search - ours, or a faster external one - emits
*evidence*; a small independent checker decides whether the evidence really refutes *this formula*.
This module is that checker.

## What a refutation is

A refutation of a CNF is a list of clauses, each justified either as a clause of the formula or as
the resolution of two earlier lines on one variable, ending with the empty clause. Checking one is
linear in the proof: no search, no solver, no trust in the prover.

```lean
checkProof_sound : checkProof f p = true -> ProtSat.Unsat f
encodingUnsat_of_proof : checkProof (encode P B) p = true -> analyze P B = encodingUnsat
```

The acceptance gate asks that bad evidence be rejected, and it is discharged by example:
`rejects_truncated`, `rejects_corrupted`, `rejects_wrong_formula`, `rejects_empty`, next to
`accepts_demo`, a real refutation checked by the kernel.

## What this does not do

Producing refutations for protocol instances is the prover, not the checker. The reference `dpll
does not emit proofs, and no LRAT-producing solver is installed here (only `z3`), so Mathlib`s
elaboration-time LRAT replay cannot yet be exercised on a real instance. The bridge above is what
a prover plugs into: a checked refutation yields `dpll (encode P B) = none` through
`dpll_none_iff_unsat`, hence the analyser verdict, hence - for a gap-free query -
`boundedSafeGoals`, with no solver re-run anywhere.
-/

namespace ProtSat.Resolution

open ProtSat Encode Encoding Analyzer

/-- The resolvent of `c₁` and `c₂` on `v`: the two clauses without the positive occurrence of `v`
in `c₁` and the negative occurrence in `c₂`. The side conditions are checked separately, so the
function is total. -/
def resolve (c₁ c₂ : Clause) (v : BVar) : Clause :=
  (c₁.filter fun l => !(l.var == v && !l.neg)) ++ (c₂.filter fun l => !(l.var == v && l.neg))

/-- The justification of one line: clause number `n` of the formula, or the resolvent of earlier
lines `i` and `j` on variable `v`. -/
inductive Just : Type
  | orig : Nat -> Just
  | res : Nat -> Nat -> BVar -> Just
  deriving Repr, DecidableEq

/-- One line of a refutation. -/
structure Line where
  cl : Clause
  why : Just
  deriving Repr

/-- Is this line justified by the formula `f` and the earlier lines `prev`? -/
def lineOK (f : CNF) (prev : List Clause) (l : Line) : Bool :=
  match l.why with
  | Just.orig n => decide (rget f.clauses n = some l.cl)
  | Just.res i j v =>
      match rget prev i, rget prev j with
      | some c₁, some c₂ =>
          decide (c₁.any (fun x => x.var == v && !x.neg) = true ∧
            c₂.any (fun x => x.var == v && x.neg) = true ∧ l.cl = resolve c₁ c₂ v)
      | _, _ => false

/-- Walk the lines, keeping those already justified. The proof succeeds exactly when the empty
clause is derived. -/
def checkFrom (f : CNF) : List Clause -> List Line -> Bool
  | _, [] => false
  | prev, l :: rest =>
      if lineOK f prev l then
        if l.cl = [] then true else checkFrom f (prev ++ [l.cl]) rest
      else false

theorem checkFrom_nil (f prev) : checkFrom f prev [] = false := rfl

theorem checkFrom_cons (f prev l rest) :
    checkFrom f prev (l :: rest) =
      if lineOK f prev l then
        if l.cl = [] then true else checkFrom f (prev ++ [l.cl]) rest
      else false := rfl

/-- **The checker.** `checkProof f p = true` means `p` is a resolution refutation of `f`. -/
def checkProof (f : CNF) (p : List Line) : Bool := checkFrom f [] p

/-! ### Soundness -/

/-- A satisfied clause keeps a satisfied literal after dropping the false pivot. -/
theorem keep_neg_pivot {a : Assignment} {c : Clause} {v : BVar} {l : Lit}
    (he : Lit.eval a l = true) (hl : l ∈ c) (hv : a v = true) :
    (c.filter fun x => !(x.var == v && x.neg)).any (fun x => x.eval a) = true := by
  refine List.any_eq_true.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, he⟩
  have hgoal : (l.var == v && l.neg) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [Bool.and_eq_true] at hc
    have h1 : l.var = v := by simpa using hc.1
    have h2 : l.neg = true := by simpa using hc.2
    unfold Lit.eval at he
    simp [h2, h1, hv] at he
  have hfin : !(l.var == v && l.neg) = true := by
    cases h2 : (l.var == v && l.neg) with
    | true => exact absurd h2 (by simpa [hgoal] using hgoal)
    | false => rfl
  simpa using hfin

theorem keep_pos_pivot {a : Assignment} {c : Clause} {v : BVar} {l : Lit}
    (he : Lit.eval a l = true) (hl : l ∈ c) (hv : a v = false) :
    (c.filter fun x => !(x.var == v && !x.neg)).any (fun x => x.eval a) = true := by
  refine List.any_eq_true.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, he⟩
  have hgoal : (l.var == v && !l.neg) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [Bool.and_eq_true] at hc
    have h1 : l.var = v := by simpa using hc.1
    have h2 : l.neg = false := by simpa using hc.2
    unfold Lit.eval at he
    simp [h2, h1, hv] at he
  have hfin : !(l.var == v && !l.neg) = true := by
    cases h2 : (l.var == v && !l.neg) with
    | true => exact absurd h2 (by simpa [hgoal] using hgoal)
    | false => rfl
  simpa using hfin

/-- **Resolution preserves truth.** An assignment satisfying both parents and the pivot side
conditions satisfies the resolvent. -/
theorem eval_resolve {a : Assignment} {c₁ c₂ : Clause} {v : BVar}
    (h₁ : Clause.eval a c₁ = true) (h₂ : Clause.eval a c₂ = true)
    (hp : c₁.any (fun x => x.var == v && !x.neg) = true)
    (hn : c₂.any (fun x => x.var == v && x.neg) = true) :
    Clause.eval a (resolve c₁ c₂ v) = true := by
  unfold Clause.eval resolve
  rw [List.any_append, Bool.or_eq_true]
  by_cases hav : a v = true
  · right
    obtain ⟨l, hl, he⟩ := List.any_eq_true.mp h₂
    exact keep_neg_pivot he hl hav
  · left
    obtain ⟨l, hl, he⟩ := List.any_eq_true.mp h₁
    exact keep_pos_pivot he hl (by simpa using hav)

/-- Every justified line is satisfied by any model of the formula and of the earlier lines. -/
theorem lineOK_sat {f : CNF} {a : Assignment} (hfa : Sat a f) {prev : List Clause}
    (hall : ∀ c ∈ prev, Clause.eval a c = true) {l : Line} (h : lineOK f prev l = true) :
    Clause.eval a l.cl = true := by
  cases l with
  | mk cl why =>
      cases why with
      | orig n =>
          have hg : rget f.clauses n = some cl := of_decide_eq_true h
          exact hfa cl (Encode.rget_some_mem f.clauses n cl hg)
      | res i j v =>
          unfold lineOK at h
          simp at h
          cases hi : rget prev i with
          | none => rw [hi] at h; simp at h
          | some c₁ =>
              cases hj : rget prev j with
              | none => rw [hj] at h; simp at h
              | some c₂ =>
                  rw [hi, hj] at h
                  simp at h
                  obtain ⟨h1, h2, h3⟩ := h
                  rw [h3]
                  have hp : c₁.any (fun x => x.var == v && !x.neg) = true := by
                    obtain ⟨x, hx1, hx2, hx3⟩ := h1
                    exact List.any_eq_true.mpr ⟨x, hx1, by simpa [hx2, hx3]⟩
                  have hn : c₂.any (fun x => x.var == v && x.neg) = true := by
                    obtain ⟨x, hx1, hx2, hx3⟩ := h2
                    exact List.any_eq_true.mpr ⟨x, hx1, by simpa [hx2, hx3]⟩
                  refine eval_resolve (hall c₁ (Encode.rget_some_mem prev i c₁ hi))
                    (hall c₂ (Encode.rget_some_mem prev j c₂ hj)) hp hn

/-- If the walk succeeds, the empty clause is satisfied by every model of the formula. -/
theorem checkFrom_sat {f : CNF} {a : Assignment} (hfa : Sat a f) :
    ∀ (p : List Line) (prev : List Clause),
      (∀ c ∈ prev, Clause.eval a c = true) ->
      checkFrom f prev p = true -> Clause.eval a [] = true := by
  intro p
  induction p with
  | nil => intro prev _ h; exact absurd h (by simp [checkFrom_nil])
  | cons l rest ih =>
      intro prev hall h
      rw [checkFrom_cons] at h
      by_cases hok : lineOK f prev l
      · rw [if_pos hok] at h
        have hsat := lineOK_sat hfa hall hok
        by_cases he : l.cl = []
        · rw [if_pos he] at h
          rw [← he]
          exact hsat
        · rw [if_neg he] at h
          refine ih (prev ++ [l.cl]) ?_ h
          intro c hc
          rw [List.mem_append, List.mem_singleton] at hc
          rcases hc with hc | hc
          · exact hall c hc
          · subst hc
            exact hsat
      · exact absurd h (by rw [if_neg hok]; simp)

/-- **The checker is sound.** A checked refutation means the formula has no model. -/
theorem checkProof_sound {f : CNF} {p : List Line} (h : checkProof f p = true) :
    ProtSat.Unsat f := by
  intro hsat
  obtain ⟨a, ha⟩ := hsat
  have h0 := checkFrom_sat ha p [] (by simp) h
  exact absurd h0 (by simp [Clause.eval])

/-! ### The acceptance gate: bad evidence is rejected -/

/-- A formula with no model: (x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ z) ∧ (¬x ∨ ¬z). -/
def demoF : CNF :=
  { clauses := [[pos 0, pos 1], [pos 0, neg 1], [neg 0, pos 2], [neg 0, neg 2]] }

/-- A refutation of it. Resolution keeps the literals of both parents, so the resolvent repeats the
shared literal; the checker compares clauses literally, which is what makes a doctored line fail. -/
def demoP : List Line :=
  [ { cl := [pos 0, pos 1], why := Just.orig 0 },
    { cl := [pos 0, neg 1], why := Just.orig 1 },
    { cl := [neg 0, pos 2], why := Just.orig 2 },
    { cl := [neg 0, neg 2], why := Just.orig 3 },
    { cl := [pos 0, pos 0], why := Just.res 0 1 1 },
    { cl := [neg 0, neg 0], why := Just.res 2 3 2 },
    { cl := [], why := Just.res 4 5 0 } ]

/-- The kernel checks the refutation. -/
theorem accepts_demo : checkProof demoF demoP = true := by decide

/-- And it is a genuine refutation: no assignment satisfies the formula. -/
theorem demoF_unsat : ProtSat.Unsat demoF := checkProof_sound accepts_demo

/-- A proof that stops one line short derives nothing: it is rejected. -/
theorem rejects_truncated : checkProof demoF (demoP.take 6) = false := by decide

/-- An empty proof is rejected. -/
theorem rejects_empty : checkProof demoF [] = false := by decide

/-- A doctored line - claiming the resolvent drops a literal it does not drop - is rejected. -/
def demoP_bad : List Line :=
  [ { cl := [pos 0, pos 1], why := Just.orig 0 },
    { cl := [pos 0, neg 1], why := Just.orig 1 },
    { cl := [neg 0, pos 2], why := Just.orig 2 },
    { cl := [neg 0, neg 2], why := Just.orig 3 },
    { cl := [pos 0], why := Just.res 0 1 1 },
    { cl := [neg 0, neg 0], why := Just.res 2 3 2 },
    { cl := [], why := Just.res 4 5 0 } ]

theorem rejects_corrupted : checkProof demoF demoP_bad = false := by decide

/-- Evidence for a *different* formula is rejected: the orig lines no longer read back. -/
def demoF_other : CNF :=
  { clauses := [[pos 0, pos 1], [pos 0, neg 1], [neg 0, pos 2], [neg 0, neg 3]] }

theorem rejects_wrong_formula : checkProof demoF_other demoP = false := by decide

/-- A line citing a parent that does not exist is rejected. -/
def demoP_oob : List Line :=
  [ { cl := [], why := Just.res 0 1 0 }, { cl := [pos 0], why := Just.orig 9 } ]

theorem rejects_out_of_range : checkProof demoF demoP_oob = false := by decide

/-! ### The bridge to the verdict -/

/-- A checked refutation of the generated formula gives the analyser's UNSAT verdict - without
running the solver. This is the hole `EndToEnd.lean` leaves open: the answer stops being a
computation to trust and becomes evidence to check. -/
theorem encodingUnsat_of_proof {P : Protocol} {B : Bounded.Bounds} (p : List Line)
    (hu : univClosedBool (shapeOf P B) P = true)
    (h : checkProof (encode P B) p = true) : analyze P B = Verdict.encodingUnsat := by
  have hnone : DPLL.dpll (encode P B) = none :=
    (dpll_none_iff_unsat _).mpr (checkProof_sound h)
  rw [analyze, if_neg (by simp [hu]), hnone]

/-! ### Handing the exact formula to an external prover -/

/-- A literal in DIMACS form: variables are 1-based, negation is a minus sign. -/
def litDimacs (l : Lit) : String := (if l.neg then "-" else "") ++ toString (l.var + 1)

/-- The whole formula in DIMACS, so an external solver can be pointed at *this* formula and its
refutation handed back to `checkProof`. The header counts are computed from the lists themselves,
so a truncated file cannot silently pass as the same problem. -/
def toDimacs (f : CNF) : String :=
  let nv := (f.clauses.flatMap fun c => c.map fun l => l.var + 1).foldr max 0
  "p cnf " ++ toString nv ++ " " ++ toString f.clauses.length ++ "\n" ++
    String.join (f.clauses.map fun c =>
      String.join (c.map fun l => litDimacs l ++ " ") ++ "0\n")

/-- The printer emits the standard encoding of the demo formula: variables 1-based, one clause per
line, terminated by 0, with a header counting the variables and the clauses. This is the text an
external prover is handed, and the formula `checkProof` checks against is the same one. -/
theorem dimacs_demo :
    toDimacs demoF = "p cnf 3 4\n1 2 0\n1 -2 0\n-1 3 0\n-1 -3 0\n" := by decide

end ProtSat.Resolution