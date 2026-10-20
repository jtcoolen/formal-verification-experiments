/-
Copyright (2026) Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.AnalyzerEvidence

/-!
# ProtSat: the fast producer and the pruner, proved sound

## Why this module exists

`ProtSat/AnalyzerEvidence.lean` carries two producers of UNSAT evidence. The first,
`refutationOf`, is the saturating resolution prover of `ProtSat.Refute`; its output is proved
accepted by the independent checker (`refute_sound`). The second, `unitRefutationCodeOf`, is unit
propagation followed by dependency pruning. It is the only producer in the repository that refutes a
real protocol formula - the embedded 21-line certificate for `EndToEnd.qg` is its output - and the
file that defines it says plainly that it is *not* proved sound: "what makes an artifact from it
trustworthy is that `checkCode` accepts that artifact".

That leaves the certificate in an awkward position. `qg_checked` is a `decide` over 138 integers: it
shows the checker accepts *those bytes*, but nothing connects the bytes to the program that was
supposed to emit them, and `qg_producer_reproduces` - the claim that they are the producer's output -
is checked by the demo program at run time, outside the kernel. As it stands the certificate is a
hand-carried artifact the checker happens to accept, not a generated one.

This module proves the two missing soundness theorems, exactly as the task asked:

```lean
unitRefutation_checkProof  : unitRefutation f fuel = some p -> checkProof f p = true
prune_checkProof           : AllOK f [] p -> p nonempty -> last line of p empty ->
                                checkProof f (prune p) = true
unitCodeOf_sound           : unitCodeOf f fuel = some c -> exists k, checkCode f k c = true
unitRefutationCodeOf_sound : unitRefutationCodeOf q fuel = some c ->
                                exists k, checkCode (formulaOf q) k c = true
```

The first says every line the propagation engine emits is a legal derivation step: an initial clause
of the formula, or a resolution of two earlier emitted lines on a pivot both parents carry. The second
says the pruner preserves that property and keeps the empty clause, so a *pruned* proof is still a
proof. The third and fourth carry the pair through the byte format, and `boundedSafe_of_unitCode`
and `analyzeQuery_encodingUnsat_of_unitCode` turn the emitted code into the security
statement. Together they make the emitted code accepted *because the producer produced it*, which is
the difference between a generated certificate and an embedded one.

Three consequences are closed facts, not conditionals:

* `tiny_prune_accepted` and `tiny_code_accepted`: on a formula the kernel can propagate
  on, the producer's pruned output and its serialized code are accepted *by these theorems*, and
  `tiny_prune_accepted_decide` and `tiny_code_checked` confirm the same facts by
  replaying the checker. `tiny_sizes` shows the pruner at work: 6 lines emitted, 5 kept,
  one line dropped.
* `qg_pruned_accepted`: the embedded 21-line certificate is accepted, therefore its pruning
  is accepted - by `prune_checkProof`, not by `decide`. That is goal (2) discharged on
  the real certificate rather than on a toy.
* `qg_pruned_accepted_decide` confirms it by replaying the checker on the pruned certificate.
* `qg_pruned_accepted_decide` confirms the same fact by replaying the checker on the pruned certificate.
* `qg_prune_is_idempotent`: pruning the certificate returns exactly the 138 integers that are
  in the source, so the artifact is already closed under its own dependencies.

## How the producer proof goes

The engine's invariant is `Refute.AllOK f [] acc`: every line of the accumulator is justified by
the formula plus the lines before it. Three facts feed it.

* A unit that `unitLines off ls` reports really is a singleton clause of `ls` at the index it
  reports (`rget_unitLines`). The indices are absolute, which is what makes the offset arithmetic in
  `unitSaturate` correct rather than accidentally correct.
* `resolveWithUnit` cites its parents in the order the checker demands - the clause carrying the
  pivot positively first - and `complements c l` is exactly the side condition `lineOK` needs of
  the other parent (`lineOK_resolveWithUnit`). This is the one place a plausible-looking producer
  could have been wrong: had the two branches of that `if` swapped their citation order, every
  emitted line would have been rejected.
* `propagate` only ever cites indices below `acc.length`, and `acc` grows by appending, so a
  citation made in round `k` still reads back in round `k + 1` (`Encode.rget_append`).

## How the pruner proof goes

`prune` keeps the lines the last line depends on and renumbers the citations. Two things have to go
together:

* the keep-mask is *closed under citations* - if a line survives, so do its parents
  (`keepClosure_closed`), which is what makes a renumbered citation point at a line that is still
  there; and
* the renumbering `posOf kept j = #{kept indices below j}` sends a parent to its new position,
  which is below the position of the line that cites it (`AllOK_restrictFrom`, the induction over
  the kept indices with an already-emitted prefix).

The closure proof is the delicate part: `keepClosure` iterates `markParents` under a fuel bound
and the bound has to be big enough for the iteration to have reached a fixed point. The route taken
here: `markParents` is pointwise extensive and length-preserving (`markParents_mono`,
`markParents_length`); the fuel recursion satisfies `markParents p (keepClosure m p k) =
keepClosure m.succ p k` (`keepClosure_succ`), so the sequence is exactly the iterate of
`markParents`; a step that changes the mask strictly increases the number of marks
(`numMarks_lt_of`); there are at most `k.length` marks, so at fuel `k.length` the sequence has
stabilized (`keepClosure_stable`); and a stable mask is closed under citations
(`markParents_closed`). `prune` uses fuel `p.length`, which is the bound the lemma needs. The
other half of the closure argument is `lt_of_mem_cites`: in a justified proof every citation
points backwards, so a dependency chain cannot be longer than the proof.

## Measured cost

Whole file, `lake env lean ProtSat/UnitRefute.lean`: about 3 s, of which about 1.9 s is loading
the imports. Each gate was timed on its own in a file that imports `ProtSat.AnalyzerEvidence` and
repeats the same `decide` (the baseline import cost is 1.85 s, subtracted below):

| gate | what the kernel replays | wall clock |
|---|---|---|
| `tiny_emitted_bool` | unit propagation of a 3-clause formula, 2 rounds | under 0.05 s |
| `tiny_sizes` | the same, plus pruning and two lengths | under 0.05 s |
| `tiny_prune_accepted_decide` | checking the 5 pruned lines | under 0.05 s |
| `tiny_code_checked` | decode 30 integers and check 5 lines | under 0.05 s |
| `proofOfCode_qg_bool` | decode the 138 certificate integers | under 0.05 s |
| `qg_last_empty`, `qg_no_earlier_empty` | index the decoded proof, test 21 clauses | under 0.05 s |
| `qg_prune_is_idempotent` | decode, prune (21 rounds of `markParents`), re-encode | about 0.3 s |

No gate here exceeds 60 s, and every one of them is discharged by the kernel: nothing is evaluated
outside it, and no decision procedure is called through the FFI.

## What is *not* claimed, and why

* The producer is not complete: unit propagation misses refutations that resolution finds, and nothing
  here says otherwise.
* The pruner is proved to keep the proof *valid*, not to keep it *small*.
* The `qg` certificate is still not produced inside the kernel, and that was measured rather
  than assumed: making the kernel evaluate `unitRefutation (formulaOf qg) qgFuel` - the search,
  not the certificate - was timed at **65.9 s** of kernel time and needs `maxRecDepth 100000` and a
  raised `maxHeartbeats` to get there (the default heartbeat limit aborts it at about 10 s). That
  is over the budget this repository holds itself to, and it is the wrong shape of trust anyway: the
  certificate exists so the kernel never replays a search. So the link is stated as a conditional -
  `qg_produced_is_accepted` and `qg_producer_reproduces_is_enough` say that *if* the producer
  emits these bytes (the equation the demo program checks at run time) then the checker accepts them,
  and the proof of the implication never touches the search. What *is* unconditional about the
  embedded certificate is `qg_pruned_accepted`: pruning it preserves acceptance, by theorem.
-/

namespace ProtSat.UnitRefute

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query
  BoundedExec Represent Resolution Serialize CheckedSafe Refute AnalyzerEvidence

/-! ### (1) Every line the propagation engine emits is a legal resolution step -/

/-- Pointwise equal Boolean predicates have equal `any`. -/
theorem any_congr {α : Type} (l : List α) {p q : α → Bool} (h : ∀ x, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.any_cons, List.any_cons, h x, ih]

/-- Complementing a *negative* unit is exactly holding the pivot positively. -/
theorem complements_eq_hasPos {c : Clause} {l : Lit} (hl : l.neg = true) :
    complements c l = hasPos c l.var := by
  unfold complements hasPos
  refine any_congr c (fun k => ?_)
  show (k.var == l.var && k.neg == !l.neg) = (k.var == l.var && !k.neg)
  rw [hl]
  cases k.neg <;> rfl

/-- Complementing a *positive* unit is exactly holding the pivot negatively. -/
theorem complements_eq_hasNeg {c : Clause} {l : Lit} (hl : l.neg = false) :
    complements c l = hasNeg c l.var := by
  unfold complements hasNeg
  refine any_congr c (fun k => ?_)
  show (k.var == l.var && k.neg == !l.neg) = (k.var == l.var && k.neg)
  rw [hl]
  cases k.neg <;> rfl

/-- Reading a unit that `unitLines off ls` reported: the reported index is the offset plus a position
in the list, and the clause at that position is the singleton `[l]`. This is what makes the absolute
indices `unitSaturate` passes around meaningful. -/
theorem rget_unitLines : ∀ (ls : List Line) (off : Nat) (i : Nat) (l : Lit),
    (i, l) ∈ unitLines off ls → ∃ k, i = off + k ∧ rget (clList ls) k = some [l] := by
  intro ls
  induction ls with
  | nil => intro off i l h; exact absurd h (by simp [unitLines])
  | cons a rest ih =>
      intro off i l h
      cases a with
      | mk cl why =>
          cases cl with
          | nil =>
              have h1 : unitLines off ({ cl := [], why := why } :: rest)
                  = unitLines (off + 1) rest := rfl
              rw [h1] at h
              obtain ⟨k, hk, hg⟩ := ih (off + 1) i l h
              refine ⟨k + 1, by omega, ?_⟩
              rw [clList_cons, Encode.rget_succ]
              exact hg
          | cons x xs =>
              cases xs with
              | nil =>
                  have h1 : unitLines off ({ cl := [x], why := why } :: rest)
                      = (off, x) :: unitLines (off + 1) rest := rfl
                  rw [h1] at h
                  rw [List.mem_cons] at h
                  rcases h with ⟨rfl, rfl⟩ | h
                  · rw [clList_cons]
                    exact ⟨0, by omega, rfl⟩
                  · obtain ⟨k, hk, hg⟩ := ih (off + 1) i l h
                    refine ⟨k + 1, by omega, ?_⟩
                    rw [clList_cons, Encode.rget_succ]
                    exact hg
              | cons y ys =>
                  have h1 : unitLines off ({ cl := x :: y :: ys, why := why } :: rest)
                      = unitLines (off + 1) rest := rfl
                  rw [h1] at h
                  obtain ⟨k, hk, hg⟩ := ih (off + 1) i l h
                  refine ⟨k + 1, by omega, ?_⟩
                  rw [clList_cons, Encode.rget_succ]
                  exact hg

/-- **One propagation step is a legal resolution step.** Resolving the clause `c` against the unit
line `[l]` that `acc` carries at index `i` yields a line the checker accepts after `acc`, provided
`c` holds the literal that `l` refutes. The two branches are the two polarities of the pivot, and
each cites the positive-pivot parent first, which is the order `lineOK` demands. -/
theorem lineOK_resolveWithUnit {f : CNF} (acc : List Line) (i j : Nat) (l : Lit) (c : Clause)
    (hi : rget (clList acc) i = some [l]) (hj : rget (clList acc) j = some c)
    (hcomp : complements c l = true) :
    lineOK f (clList acc) (resolveWithUnit i j l c) = true := by
  cases hln : l.neg with
  | true =>
      have hpos : hasPos c l.var = true := by
        rw [← complements_eq_hasPos hln]
        exact hcomp
      have hneg : hasNeg [l] l.var = true := by
        rw [hasNeg]
        simp [hln]
      have h := lineOK_res (f := f) hj hi hpos hneg
      have hred : resolveWithUnit i j l c =
          { cl := resolve c [l] l.var, why := Just.res j i l.var } := by
        simp [resolveWithUnit, hln]
      rw [hred]
      exact h
  | false =>
      have hneg : hasNeg c l.var = true := by
        rw [← complements_eq_hasNeg hln]
        exact hcomp
      have hpos : hasPos [l] l.var = true := by
        rw [hasPos]
        simp [hln]
      have h := lineOK_res (f := f) hi hj hpos hneg
      have hred : resolveWithUnit i j l c =
          { cl := resolve [l] c l.var, why := Just.res i j l.var } := by
        simp [resolveWithUnit, hln]
      rw [hred]
      exact h

/-- Every line one propagation round emits is justified by the formula and the lines already in the
accumulator - provided each unit it propagates from is a unit where it claims to be. -/
theorem baseOK_propagate {f : CNF} (acc : List Line) :
    (us : List (Nat × Lit)) → (∀ u ∈ us, rget (clList acc) u.1 = some [u.2]) →
      baseOK f (clList acc) (propagate acc us)
  | [], _ => baseOK_nil f (clList acc)
  | (i, l) :: rest, hu => by
      have h1 : rget (clList acc) i = some [l] := hu (i, l) (by simp)
      have hrest : baseOK f (clList acc) (propagate acc rest) :=
        baseOK_propagate acc rest (fun u hu' => hu u (List.Mem.tail _ hu'))
      have hEq : propagate acc ((i, l) :: rest) =
          (List.range acc.length).filterMap (fun j =>
            match rget (clList acc) j with
            | some c => if complements c l then some (resolveWithUnit i j l c) else none
            | none => none) ++ propagate acc rest := rfl
      rw [hEq]
      refine baseOK_append ?_ hrest
      intro x hx
      rw [List.mem_filterMap] at hx
      obtain ⟨j, hj, hget⟩ := hx
      have hlen : j < (clList acc).length := by
        rw [clList, List.length_map]
        exact List.mem_range.mp hj
      cases hg : rget (clList acc) j with
      | none => exact absurd hget (by rw [hg]; simp)
      | some c =>
          have hkey : (if complements c l then some (resolveWithUnit i j l c) else none) = some x :=
            by simpa [hg] using hget
          by_cases hcomp : complements c l
          · rw [if_pos hcomp] at hkey
            obtain rfl := Option.some.inj hkey
            exact lineOK_resolveWithUnit acc i j l c h1 hg hcomp
          · rw [if_neg hcomp] at hkey
            exact absurd hkey (by simp)

/-- **The accumulator is a valid proof prefix at every fuel.** Whatever the fuel, and whatever units
it is handed (as long as they are units where they claim to be), the lines `unitSaturate` accumulates
are each an initial clause or a resolution of two earlier lines. This is the invariant the checker
walks. -/
theorem AllOK_unitSaturate {f : CNF} : ∀ (k : Nat) (acc : List Line) (us : List (Nat × Lit)),
    AllOK f [] acc → (∀ u ∈ us, rget (clList acc) u.1 = some [u.2]) →
      AllOK f [] (unitSaturate k acc us) := by
  intro k
  induction k with
  | zero => intro acc us hall _; exact hall
  | succ k ih =>
      intro acc us hall hu
      set new := novel (clList acc) (propagate acc us) with hnew
      have hnewOK : AllOK f (clList acc) new :=
        baseOK_AllOK (baseOK_novel (clList acc) (baseOK_propagate acc us hu))
      have hEq : unitSaturate (k + 1) acc us =
          if new = [] then acc
          else if found (acc ++ new) then acc ++ new
          else unitSaturate k (acc ++ new) (unitLines acc.length new) := rfl
      rw [hEq]
      by_cases hnil : new = []
      · rw [if_pos hnil]
        exact hall
      · rw [if_neg hnil]
        have happ : AllOK f [] (acc ++ new) := AllOK_append hall new hnewOK
        by_cases hf : found (acc ++ new)
        · rw [if_pos hf]
          exact happ
        · rw [if_neg hf]
          refine ih (acc ++ new) (unitLines acc.length new) happ ?_
          intro u hu
          obtain ⟨k', hk', hg⟩ := rget_unitLines new acc.length u.1 u.2 hu
          have hlen : (clList acc).length = acc.length := by rw [clList, List.length_map]
          rw [hk', ← clList_append, ← hlen, rget_append]
          exact hg

/-- The accumulator the propagation engine ends with, spelled out once so the lemmas below do not have
to repeat it. -/
def accOf (f : CNF) (fuel : Nat) : List Line :=
  unitSaturate fuel (seed f.clauses 0) (unitLines 0 (seed f.clauses 0))

/-- The producer's own definition, restated against `accOf`. -/
theorem unitRefutation_eq (f : CNF) (fuel : Nat) :
    unitRefutation f fuel =
      if found (accOf f fuel) then some (uptoEmpty (accOf f fuel)) else none := rfl

/-- The propagation accumulator is a valid proof prefix: every line an initial clause or a resolution
of two earlier lines of it. -/
theorem AllOK_accOf {f : CNF} : ∀ (fuel : Nat), AllOK f [] (accOf f fuel) := by
  intro fuel
  show AllOK f [] (unitSaturate fuel (seed f.clauses 0) (unitLines 0 (seed f.clauses 0)))
  refine AllOK_unitSaturate fuel (seed f.clauses 0) (unitLines 0 (seed f.clauses 0)) ?_ ?_
  · exact AllOK_seed f f.clauses 0 (by intro j c hc; simpa using hc) []
  · intro u hu
    obtain ⟨k, hk, hg⟩ := rget_unitLines (seed f.clauses 0) 0 u.1 u.2 hu
    rwa [show u.1 = 0 + k from hk, Nat.zero_add]

/-- The producer's refutation exists exactly when the propagation reached the empty clause. -/
theorem found_accOf {f : CNF} {fuel : Nat} {p : List Line}
    (h : unitRefutation f fuel = some p) : found (accOf f fuel) = true := by
  rw [unitRefutation_eq] at h
  by_cases hf : found (accOf f fuel)
  · exact hf
  · rw [if_neg hf] at h
    exact absurd h (by simp)

/-- The refutation the producer returns is the accumulator cut at the first empty line. -/
theorem some_accOf_unitRefutation {f : CNF} {fuel : Nat} {p : List Line}
    (h : unitRefutation f fuel = some p) : p = uptoEmpty (accOf f fuel) := by
  have hf := found_accOf h
  rw [unitRefutation_eq, if_pos hf] at h
  exact (Option.some.inj h).symm

/-- **Every line the producer emits is a legal derivation step.** If unit propagation reaches a
refutation, each of its lines is an initial clause of `f` or a resolution of two earlier lines of
it. -/
theorem AllOK_unitRefutation {f : CNF} {fuel : Nat} {p : List Line}
    (h : unitRefutation f fuel = some p) : AllOK f [] p := by
  rw [some_accOf_unitRefutation h]
  exact AllOK_uptoEmpty [] _ (AllOK_accOf fuel)

/-- **Soundness of the fast producer, in the checker's own vocabulary.** Whatever
`unitRefutation` hands back, the independent line-by-line checker accepts it as a refutation of
`f`. The checker replays no search: this is `checkFrom_true` applied to the invariant above. -/
theorem unitRefutation_checkProof {f : CNF} {fuel : Nat} {p : List Line}
    (h : unitRefutation f fuel = some p) : checkProof f p = true := by
  rw [some_accOf_unitRefutation h]
  exact uptoEmpty_checkProof (AllOK_accOf fuel) (found_accOf h)

/-- A refutation the producer returns ends with the empty clause - the line the pruner must keep. -/
theorem uptoEmpty_last {p : List Line} (h : found p = true) :
    ∃ q l, uptoEmpty p = q ++ [l] ∧ l.cl = [] := by
  induction p with
  | nil => exact absurd h (by simp [found])
  | cons a rest ih =>
      by_cases ha : a.cl = []
      · refine ⟨[], a, ?_, ha⟩
        simp [uptoEmpty, ha]
      · have h1 : uptoEmpty (a :: rest) = a :: uptoEmpty rest := by simp [uptoEmpty, ha]
        have hf : found rest = true := by
          rw [found_cons] at h
          exact h.resolve_left ha
        obtain ⟨q, l, hq, hl⟩ := ih hf
        refine ⟨a :: q, l, ?_, hl⟩
        rw [h1, hq]
        simp
/-! ### (2) Reading lines by index -/

/-- The line at an index, with the default \`reindex\` itself reads for an out-of-range index. -/
def lineAt (p : List Line) (i : Nat) : Line := p.getD i { cl := [], why := Just.orig 0 }

/-- An in-range read is what \`getD\` returns. -/
theorem getD_of_rget {α : Type} : ∀ (l : List α) (i : Nat) (x : α) (d : α),
    rget l i = some x -> l.getD i d = x := by
  intro l
  induction l with
  | nil => intro i x d h; exact absurd h (by simp [rget])
  | cons y ys ih =>
      intro i x d h
      cases i with
      | zero => rw [List.getD_cons_zero]; exact Option.some.inj h
      | succ i =>
          rw [List.getD_cons_succ]
          exact ih i x d (by simpa [rget] using h)

/-- An out-of-range read is what \`getD\` falls back to. -/
theorem getD_of_rget_none {α : Type} : ∀ (l : List α) (i : Nat) (d : α),
    rget l i = none -> l.getD i d = d := by
  intro l
  induction l with
  | nil => intro i d h; rfl
  | cons y ys ih =>
      intro i d h
      cases i with
      | zero => exact absurd h (by simp [rget])
      | succ i =>
          rw [List.getD_cons_succ]
          exact ih i d (by simpa [rget] using h)

/-- An in-range read is what \`lineAt\` returns. -/
theorem lineAt_of_rget {p : List Line} {i : Nat} {l : Line} (h : rget p i = some l) :
    lineAt p i = l := by
  unfold lineAt
  exact getD_of_rget p i l _ h

/-- \`reindex\` on a line justified by the formula: clause and citation untouched. -/
theorem reindex_orig {p : List Line} {before : Nat -> Nat} {i n : Nat}
    (h : (lineAt p i).why = Just.orig n) :
    reindex p before i = { cl := (lineAt p i).cl, why := Just.orig n } := by
  have h1 : reindex p before i =
      match (lineAt p i).why with
      | Just.orig a => { cl := (lineAt p i).cl, why := Just.orig a }
      | Just.res a b v => { cl := (lineAt p i).cl, why := Just.res (before a) (before b) v } := rfl
  rw [h1, h]

/-- \`reindex\` on a resolvent line: the clause is untouched, both citations are renumbered. -/
theorem reindex_res {p : List Line} {before : Nat -> Nat} {i a b : Nat} {v : BVar}
    (h : (lineAt p i).why = Just.res a b v) :
    reindex p before i =
      { cl := (lineAt p i).cl, why := Just.res (before a) (before b) v } := by
  have h1 : reindex p before i =
      match (lineAt p i).why with
      | Just.orig a => { cl := (lineAt p i).cl, why := Just.orig a }
      | Just.res a b v => { cl := (lineAt p i).cl, why := Just.res (before a) (before b) v } := rfl
  rw [h1, h]

/-- Renumbering never changes a line's clause - only whom it cites. -/
theorem reindex_cl {p : List Line} (before : Nat -> Nat) (i : Nat) :
    (reindex p before i).cl = (lineAt p i).cl := by
  have h : reindex p before i =
      match (lineAt p i).why with
      | Just.orig a => { cl := (lineAt p i).cl, why := Just.orig a }
      | Just.res a b v => { cl := (lineAt p i).cl, why := Just.res (before a) (before b) v } := rfl
  rw [h]
  cases hwhy : (lineAt p i).why with
  | orig a => rfl
  | res a b v => rfl

/-- The lines a line cites, in terms of its justification. -/
theorem cites_eq (p : List Line) (i : Nat) :
    cites p i = match (lineAt p i).why with
      | Just.res a b _ => [a, b]
      | Just.orig _ => [] := by
  cases h : rget p i with
  | none =>
      have h1 : cites p i = [] := by unfold cites; simp [h]
      have h2 : lineAt p i = { cl := [], why := Just.orig 0 } := by
        unfold lineAt
        exact getD_of_rget_none p i _ h
      rw [h1, h2]
  | some l =>
      cases hwhy : l.why with
      | orig n =>
          have h1 : cites p i = [] := by unfold cites; simp [h, hwhy]
          rw [h1, lineAt_of_rget h, hwhy]
      | res a b v =>
          have h1 : cites p i = [a, b] := by unfold cites; simp [h, hwhy]
          rw [h1, lineAt_of_rget h, hwhy]

/-- Everything a line cites is a parent of a resolvent line. -/
theorem mem_cites {p : List Line} {i j : Nat} (h : j ∈ cites p i) :
    ∃ a b v, (lineAt p i).why = Just.res a b v ∧ (j = a ∨ j = b) := by
  rw [cites_eq] at h
  cases hwhy : (lineAt p i).why with
  | orig n => exact absurd h (by simp [hwhy])
  | res a b v =>
      rw [hwhy] at h
      simp at h
      rcases h with heq | heq
      · exact ⟨a, b, v, rfl, Or.inl heq⟩
      · exact ⟨a, b, v, rfl, Or.inr heq⟩

/-- Both parents of a resolvent line are cited by it. -/
theorem cites_res {p : List Line} {i a b : Nat} {v : BVar}
    (h : (lineAt p i).why = Just.res a b v) : a ∈ cites p i ∧ b ∈ cites p i := by
  rw [cites_eq, h]
  simp

/-- Reading a map at an index maps the read. -/
theorem rget_map {α β : Type} (f : α -> β) : ∀ (l : List α) (i : Nat),
    rget (l.map f) i = (rget l i).map f := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons x xs ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i => exact ih i

/-- Reading a map with \`getD\` at an in-range index maps the read. -/
theorem getD_map_of_lt {α β : Type} (f : α -> β) :
    ∀ (l : List α) (i : Nat) (d : β) (d' : α), i < l.length ->
      (l.map f).getD i d = f (l.getD i d') := by
  intro l
  induction l with
  | nil => intro i d d' h; exact absurd h (by simp)
  | cons x xs ih =>
      intro i d d' h
      cases i with
      | zero =>
          show (f x :: List.map f xs).getD 0 d = f ((x :: xs).getD 0 d')
          rw [List.getD_cons_zero, List.getD_cons_zero]
      | succ i =>
          show (f x :: List.map f xs).getD (i + 1) d = f ((x :: xs).getD (i + 1) d')
          rw [List.getD_cons_succ, List.getD_cons_succ]
          exact ih i d d' (by rw [List.length_cons] at h; omega)

/-- Reading below the cut of a \`take\` is reading the whole list. -/
theorem rget_take {α : Type} : ∀ (l : List α) (i a : Nat), a < i -> i ≤ l.length ->
    rget (List.take i l) a = rget l a := by
  intro l
  induction l with
  | nil => intro i a ha hi; rw [List.length_nil] at hi; omega
  | cons x xs ih =>
      intro i a ha hi
      cases i with
      | zero => exact absurd ha (by omega)
      | succ i =>
          cases a with
          | zero =>
              show rget (List.take (i + 1) (x :: xs)) 0 = rget (x :: xs) 0
              rfl
          | succ a =>
              show rget (List.take i xs) a = rget xs a
              refine ih i a ?_ ?_
              · omega
              · rw [List.length_cons] at hi; omega

/-- **Extracting a justified line from a proof prefix.** Line \`i\` of a proof whose lines are all
justified is justified by the starting prefix plus the clauses of the lines before it. -/
theorem AllOK_lineOK_of {f : CNF} : ∀ (p : List Line) (base : List Clause), AllOK f base p ->
    ∀ (i : Nat) (l : Line), rget p i = some l ->
      lineOK f (base ++ clList (List.take i p)) l = true := by
  intro p
  induction p with
  | nil => intro base _ i l h; exact absurd h (by simp [rget])
  | cons q rest ih =>
      intro base h i l hget
      obtain ⟨h1, h2⟩ := AllOK_cons_inv h
      cases i with
      | zero =>
          have h0 : rget (q :: rest) 0 = some q := rfl
          rw [h0] at hget
          obtain rfl := Option.some.inj hget
          have hnil : clList (List.take 0 (q :: rest)) = [] := rfl
          rw [hnil, List.append_nil]
          exact h1
      | succ i =>
          have hget' : rget rest i = some l := by
            have hshift : rget (q :: rest) (i + 1) = rget rest i := rfl
            rw [hshift] at hget
            exact hget
          have hthis := ih (base ++ [q.cl]) h2 i l hget'
          have htake : List.take (i + 1) (q :: rest) = q :: List.take i rest := rfl
          have hcl : clList (q :: List.take i rest) =
              [q.cl] ++ clList (List.take i rest) := rfl
          rw [htake, hcl, ← List.append_assoc]
          exact hthis

/-- **The checker's side conditions, extracted.** If the checker accepted a resolvent line, the two
parents are in the prefix, carry the pivot in the required polarities, and the clause is the
resolvent. -/
theorem lineOK_res_some {f : CNF} {prev : List Clause} {i j : Nat} {v : BVar} {cl : Clause}
    (h : lineOK f prev { cl := cl, why := Just.res i j v } = true) :
    ∃ c₁ c₂, rget prev i = some c₁ ∧ rget prev j = some c₂ ∧ hasPos c₁ v = true ∧
      hasNeg c₂ v = true ∧ cl = resolve c₁ c₂ v := by
  cases h1 : rget prev i with
  | none => simp [lineOK, h1] at h
  | some c₁ =>
      cases h2 : rget prev j with
      | none => simp [lineOK, h2] at h
      | some c₂ =>
          obtain ⟨hp, hn, hcl⟩ := lineOK_res_iff (f := f) h1 h2 |>.mp h
          exact ⟨c₁, c₂, rfl, rfl, hp, hn, hcl⟩

/-- **In a justified proof every citation points backwards.** A resolvent line only cites lines that
were already there - which is what bounds the depth of a dependency chain, and what makes the
renumbering below order-preserving. -/
theorem lt_of_mem_cites {f : CNF} {p : List Line} (hall : AllOK f [] p) :
    ∀ {i j : Nat}, i < p.length -> j ∈ cites p i -> j < i := by
  intro i j hi hj
  obtain ⟨a, b, v, hwhy, hjab⟩ := mem_cites hj
  obtain ⟨l, hl⟩ := Encode.rget_lt p i hi
  have hline := AllOK_lineOK_of p [] hall i l hl
  cases l with
  | mk cl why =>
      have hwhy' : why = Just.res a b v := by
        have := lineAt_of_rget hl
        rw [this] at hwhy
        exact hwhy
      rw [hwhy'] at hline
      obtain ⟨c₁, c₂, h1, h2, _, _, _⟩ := lineOK_res_some hline
      have hlen : (clList (List.take i p)).length = i := by
        have hi' : i ≤ p.length := Nat.le_of_lt hi
        rw [clList, List.length_map, List.length_take, Nat.min_eq_left hi']
      rcases hjab with rfl | rfl
      · have := rget_lt_of_some (clList (List.take i p)) j c₁ h1
        rwa [hlen] at this
      · have := rget_lt_of_some (clList (List.take i p)) j c₂ h2
        rwa [hlen] at this


/-! ### (3) More index arithmetic -/

/-- Out of range, `getD` returns its fallback. -/
theorem getD_oob {α : Type} : ∀ (l : List α) (i : Nat) (d : α), l.length ≤ i -> l.getD i d = d := by
  intro l
  induction l with
  | nil => intro i d h; rfl
  | cons y ys ih =>
      intro i d h
      cases i with
      | zero => exact absurd h (by simp [List.length_cons])
      | succ i =>
          rw [List.getD_cons_succ]
          exact ih i d (by rw [List.length_cons] at h; omega)

/-- Reading the element a `snoc` appended, at exactly the old length. -/
theorem getD_append_self {α : Type} : ∀ (l : List α) (x : α) (d : α),
    (l ++ [x]).getD l.length d = x := by
  intro l
  induction l with
  | nil => intro x d; rfl
  | cons y ys ih =>
      intro x d
      show (ys ++ [x]).getD ys.length d = x
      have h1 : ((y :: ys) ++ [x]).getD ((y :: ys).length) d = (ys ++ [x]).getD ys.length d := rfl
      rw [← h1]
      exact ih x d

/-- Reading a `map` over `List.range` at an in-range index applies the function. -/
theorem getD_map_range : ∀ (n i : Nat) (f : Nat -> Bool), i < n ->
    ((List.range n).map f).getD i false = f i := by
  intro n
  induction n with
  | zero => intro i f h; exact absurd h (by omega)
  | succ n ih =>
      intro i f hi
      rw [List.range_succ, List.map_append]
      show ((List.map f (List.range n) ++ [f n]).getD i false) = f i
      by_cases h : i < n
      · rw [List.getD_append (List.map f (List.range n)) [f n] false i
          (by rw [List.length_map, List.length_range]; exact h)]
        exact ih i f h
      · have hlen : ((List.range n).map f).length = n := by
          rw [List.length_map, List.length_range]
        have h2 := getD_append_self ((List.range n).map f) (f n) false
        rw [hlen] at h2
        have heq : i = n := by omega
        rw [heq]
        exact h2

/-- Keeping the head: when the predicate holds of the head, the filter keeps it. -/
theorem filter_cons_pos {p : Nat -> Bool} {x : Nat} {xs : List Nat} (h : p x = true) :
    List.filter p (x :: xs) = x :: List.filter p xs := by
  rw [List.filter_cons, if_pos h]

/-- Dropping the head: when the predicate fails of the head, the filter skips it. -/
theorem filter_cons_neg {a x : Nat} : ∀ (xs : List Nat), ¬ (x < a) ->
    List.filter (fun y => y < a) (x :: xs) = List.filter (fun y => y < a) xs := by
  intro xs h
  rw [List.filter_cons, if_neg (fun hc => h (by simpa using hc))]

/-- A filter whose predicate fails on every element is empty. -/
theorem filter_eq_nil_of {a : Nat} : ∀ (l : List Nat), (∀ b ∈ l, ¬ (b < a)) ->
    List.filter (fun x => x < a) l = [] := by
  intro l h
  rw [List.filter_eq_nil_iff]
  intro b hb hlt
  exact h b hb (by simpa using hlt)

/-- Keeping the elements below a bound that every element exceeds leaves nothing. -/
theorem filter_eq_nil_of' : ∀ (l : List Nat) (a : Nat), (∀ b ∈ l, a < b) ->
    List.filter (fun x => x < a) l = [] := by
  intro l a h
  exact filter_eq_nil_of l (fun b hb hlt => Nat.not_lt_of_le (Nat.le_of_lt (h b hb)) hlt)

/-! ### (4) The keep-mask reaches a fixed point -/

/-- How many lines a mask marks. -/
def numMarks : List Bool -> Nat
  | [] => 0
  | true :: rest => numMarks rest + 1
  | false :: rest => numMarks rest

@[simp] theorem numMarks_nil : numMarks [] = 0 := rfl
@[simp] theorem numMarks_true (t : List Bool) : numMarks (true :: t) = numMarks t + 1 := rfl
@[simp] theorem numMarks_false (t : List Bool) : numMarks (false :: t) = numMarks t := rfl

/-- A mask never marks more lines than there are lines. -/
theorem numMarks_le_length : ∀ (k : List Bool), numMarks k ≤ k.length := by
  intro k
  induction k with
  | nil => exact Nat.le_refl 0
  | cons b rest ih =>
      cases b with
      | true => show numMarks rest + 1 ≤ rest.length + 1; omega
      | false => show numMarks rest ≤ rest.length + 1; omega

/-- The tail of a pointwise-larger mask is again pointwise larger. -/
theorem getD_tail_mono {a b : Bool} {t h : List Bool}
    (hh : ∀ i, (a :: t).getD i false = true -> (b :: h).getD i false = true) :
    ∀ i, t.getD i false = true -> h.getD i false = true := by
  intro i hi
  have h1 : (a :: t).getD (i + 1) false = true := by rw [List.getD_cons_succ]; exact hi
  have h2 := hh (i + 1) h1
  rwa [List.getD_cons_succ] at h2

/-- A mask that marks everything a second mask marks, and has the same length, marks no more lines. -/
theorem numMarks_le_of : ∀ (k h : List Bool),
    (∀ i, k.getD i false = true -> h.getD i false = true) -> k.length = h.length ->
      numMarks k ≤ numMarks h := by
  intro k
  induction k with
  | nil =>
      intro h hh hlen
      cases h with
      | nil => rfl
      | cons b t => exact absurd hlen (by simp [List.length_cons])
  | cons a t ih =>
      intro h hh hlen
      cases h with
      | nil => exact absurd hlen.symm (by simp [List.length_cons])
      | cons b u =>
          have hlen' : t.length = u.length := by simpa [List.length_cons] using hlen
          have htt := getD_tail_mono (a := a) (b := b) hh
          cases a with
          | false =>
              cases b with
              | false => show numMarks t ≤ numMarks u; exact ih u htt hlen'
              | true =>
                  have hle := ih u htt hlen'
                  show numMarks t ≤ numMarks u + 1; omega
          | true =>
              have hb : b = true := by
                have h1 : (true :: t).getD 0 false = true := rfl
                simpa using hh 0 h1
              subst hb
              have hle := ih u htt hlen'
              show numMarks t + 1 ≤ numMarks u + 1; omega

/-- Two masks of equal length, one marking everything the other does, are equal when they mark as many
lines. -/
theorem eq_of_numMarks_eq : ∀ (k h : List Bool),
    (∀ i, k.getD i false = true -> h.getD i false = true) -> k.length = h.length ->
      numMarks k = numMarks h -> k = h := by
  intro k
  induction k with
  | nil =>
      intro h hh hlen hnum
      cases h with
      | nil => rfl
      | cons b t => exact absurd hlen (by simp [List.length_cons])
  | cons a t ih =>
      intro h hh hlen hnum
      cases h with
      | nil => exact absurd hlen.symm (by simp [List.length_cons])
      | cons b u =>
          have hlen' : t.length = u.length := by simpa [List.length_cons] using hlen
          have htt := getD_tail_mono (a := a) (b := b) hh
          cases a with
          | false =>
              cases b with
              | true =>
                  have hle := numMarks_le_of t u htt hlen'
                  have hcontra : False := by
                    simp [numMarks] at hnum
                    omega
                  exact False.elim hcontra
              | false =>
                  have hnum' : numMarks t = numMarks u := by simpa [numMarks] using hnum
                  show false :: t = false :: u
                  rw [ih u htt hlen' hnum']
          | true =>
              have hb : b = true := by
                have h1 : (true :: t).getD 0 false = true := rfl
                simpa using hh 0 h1
              subst hb
              have hnum' : numMarks t = numMarks u := by simpa [numMarks] using hnum
              show true :: t = true :: u
              rw [ih u htt hlen' hnum']

/-- A mask that is pointwise larger, of the same length, and not equal, marks strictly more lines. -/
theorem numMarks_lt_of {k h : List Bool}
    (hh : ∀ i, k.getD i false = true -> h.getD i false = true) (hlen : k.length = h.length)
    (hne : k ≠ h) : numMarks k < numMarks h := by
  by_contra hc
  have hle := numMarks_le_of k h hh hlen
  have : k = h := eq_of_numMarks_eq k h hh hlen (by omega)
  exact absurd this hne

/-- The citations of everything a mask marks. -/
def addCites (p : List Line) (k : List Bool) : List Nat :=
  (List.range k.length).flatMap fun i => if k.getD i false then cites p i else []

/-- `markParents` restated without its `let`, so its entries can be read off. -/
theorem markParents_eq (p : List Line) (k : List Bool) :
    markParents p k = (List.range k.length).map
      (fun j => k.getD j false || (addCites p k).any (fun x => x == j)) := rfl

/-- Reading `markParents` at an in-range index: the old mark, or a citation of an old mark. -/
theorem markParents_getD {p : List Line} {k : List Bool} {j : Nat} (hj : j < k.length) :
    (markParents p k).getD j false =
      (k.getD j false || (addCites p k).any (fun x => x == j)) := by
  rw [markParents_eq]
  exact getD_map_range k.length j _ hj

/-- Marking parents never changes the length of the mask. -/
theorem markParents_length (p : List Line) (k : List Bool) :
    (markParents p k).length = k.length := by
  rw [markParents_eq]
  simp [List.length_map, List.length_range]

/-- `markParents` only ever adds marks. -/
theorem markParents_mono {p : List Line} {k : List Bool} {i : Nat}
    (h : k.getD i false = true) : (markParents p k).getD i false = true := by
  have hi : i < k.length := by
    by_cases h2 : i < k.length
    · exact h2
    · rw [getD_oob k i false (by omega)] at h
      exact absurd h (by decide)
  rw [markParents_getD hi, h]
  simp

/-- A mask closed under `markParents` is closed under citations. -/
theorem markParents_closed {p : List Line} {k : List Bool} {i j : Nat}
    (hfix : markParents p k = k) (hi : i < k.length) (h : k.getD i false = true)
    (hij : j ∈ cites p i) (hj : j < k.length) : k.getD j false = true := by
  have hadd : (addCites p k).any (fun x => x == j) = true := by
    unfold addCites
    rw [List.any_eq_true]
    refine ⟨j, ?_, by simp⟩
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [if_pos h]
    exact hij
  rw [← hfix, markParents_getD hj]
  rw [Bool.or_eq_true]
  right
  exact hadd

/-- No fuel, no closure: keepClosure 0 is the identity on masks. -/
theorem keepClosure_zero (p : List Line) (k : List Bool) : keepClosure 0 p k = k := rfl

/-- One step of the closure recursion, unfolded: stop if the mask already contains its parents, otherwise mark one more layer. -/
theorem keepClosure_succ_eq (p : List Line) (m : Nat) (k : List Bool) :
    keepClosure m.succ p k =
      if markParents p k == k then k else keepClosure m p (markParents p k) := rfl

/-- The fuel recursion never removes a mark. -/
theorem keepClosure_mono : ∀ (m : Nat) (p : List Line) (k : List Bool) (i : Nat),
    k.getD i false = true -> (keepClosure m p k).getD i false = true := by
  intro m
  induction m with
  | zero => intro p k i h; rw [keepClosure_zero]; exact h
  | succ m ih =>
      intro p k i h
      rw [keepClosure_succ_eq]
      by_cases hc : markParents p k == k
      · rw [if_pos hc]
        exact h
      · rw [if_neg hc]
        exact ih p (markParents p k) i (markParents_mono h)

/-- The closure recursion never changes the length of the mask. -/
theorem keepClosure_length : ∀ (m : Nat) (p : List Line) (k : List Bool),
    (keepClosure m p k).length = k.length := by
  intro m
  induction m with
  | zero => intro p k; rw [keepClosure_zero]
  | succ m ih =>
      intro p k
      rw [keepClosure_succ_eq]
      by_cases hc : markParents p k == k
      · rw [if_pos hc]
      · rw [if_neg hc, ih p (markParents p k), markParents_length]

/-- **The fuel recursion is the iterate of `markParents`:** one more unit of fuel is exactly one more
application of `markParents`. This is what lets a fixed point be read off stabilization. -/
theorem keepClosure_succ : ∀ (m : Nat) (p : List Line) (k : List Bool),
    markParents p (keepClosure m p k) = keepClosure m.succ p k := by
  intro m
  induction m with
  | zero =>
      intro p k
      rw [keepClosure_zero, keepClosure_succ_eq]
      by_cases hc : markParents p k == k
      · rw [if_pos hc]
        exact by simpa using hc
      · rw [if_neg hc, keepClosure_zero]
  | succ m ih =>
      intro p k
      by_cases hc : markParents p k == k
      · have h1 : keepClosure m.succ p k = k := by rw [keepClosure_succ_eq, if_pos hc]
        have h2 : keepClosure m.succ.succ p k = k := by rw [keepClosure_succ_eq, if_pos hc]
        rw [h1, h2]
        exact by simpa using hc
      · have h1 : keepClosure m.succ p k = keepClosure m p (markParents p k) := by
          rw [keepClosure_succ_eq, if_neg hc]
        have h2 : keepClosure m.succ.succ p k = keepClosure m.succ p (markParents p k) := by
          rw [keepClosure_succ_eq, if_neg hc]
        rw [h1, h2]
        exact ih p (markParents p k)

/-- Each step of the fuel recursion marks at least as much as the step before. -/
theorem keepClosure_mono_succ : ∀ (m : Nat) (p : List Line) (k : List Bool) (i : Nat),
    (keepClosure m p k).getD i false = true ->
      (keepClosure m.succ p k).getD i false = true := by
  intro m
  induction m with
  | zero =>
      intro p k i h
      have h1 : keepClosure 1 p k = markParents p k := by
        rw [← keepClosure_succ, keepClosure_zero]
      rw [h1]
      exact markParents_mono h
  | succ m ih =>
      intro p k i h
      have h1 : keepClosure m.succ.succ p k = markParents p (keepClosure m.succ p k) := by
        rw [keepClosure_succ]
      rw [h1]
      exact markParents_mono h

/-- Once the fuel recursion stops moving it never moves again. -/
theorem keepClosure_eq_of_eq_at : ∀ (p : List Line) (k : List Bool) (j n : Nat),
    j ≤ n -> keepClosure j p k = keepClosure j.succ p k ->
      keepClosure n p k = keepClosure n.succ p k := by
  intro p k j n
  induction n with
  | zero =>
      intro hj h
      cases j with
      | zero => exact h
      | succ j => exact absurd hj (by omega)
  | succ n ih =>
      intro hj h
      by_cases hjeq : j = n.succ
      · subst hjeq
        exact h
      · have hmid := ih (by omega) h
        have h1 := keepClosure_succ n p k
        have h2 := keepClosure_succ n.succ p k
        show keepClosure n.succ p k = keepClosure n.succ.succ p k
        rw [← h1, ← h2]
        exact congrArg (markParents p) hmid

/-- Each strict step of the fuel recursion marks at least one more line. -/
theorem numMarks_keepClosure_ge : ∀ (p : List Line) (k : List Bool) (n : Nat),
    (∀ j, j < n -> keepClosure j p k ≠ keepClosure j.succ p k) ->
      numMarks k + n ≤ numMarks (keepClosure n p k) := by
  intro p k n
  induction n with
  | zero => intro _; exact Nat.le_refl _
  | succ n ih =>
      intro hall
      have hle := ih (fun j hj => hall j (by omega))
      have hne : keepClosure n p k ≠ keepClosure n.succ p k := hall n (by omega)
      have hmono : ∀ i, (keepClosure n p k).getD i false = true ->
          (keepClosure n.succ p k).getD i false = true := keepClosure_mono_succ n p k
      have hlen : (keepClosure n p k).length = (keepClosure n.succ p k).length := by
        rw [keepClosure_length, keepClosure_length]
      have hstrict := numMarks_lt_of hmono hlen hne
      show numMarks k + n + 1 ≤ numMarks (keepClosure n.succ p k)
      omega

/-- **The keep-mask has stabilized at fuel `k.length`:** the fuel `prune` uses. -/
theorem keepClosure_stable : ∀ (p : List Line) (k : List Bool),
    keepClosure k.length p k = keepClosure k.length.succ p k := by
  intro p k
  by_cases hne : keepClosure k.length p k = keepClosure k.length.succ p k
  · exact hne
  · exfalso
    have hall : ∀ j, j < k.length.succ -> keepClosure j p k ≠ keepClosure j.succ p k := by
      intro j hj heq
      refine hne (keepClosure_eq_of_eq_at p k j k.length (by omega) heq)
    have hgrow := numMarks_keepClosure_ge p k k.length.succ hall
    have hle := numMarks_le_length (keepClosure k.length.succ p k)
    have hlen := keepClosure_length k.length.succ p k
    have h0 : 0 ≤ numMarks k := Nat.zero_le _
    omega

/-- **The keep-mask is closed under citations.** If a line survives the closure and cites a line that
exists, that parent survives too - which is what makes the renumbering below legal. -/
theorem keepClosure_closed {p : List Line} {k : List Bool} {i j : Nat}
    (hi : i < k.length) (h : (keepClosure k.length p k).getD i false = true)
    (hij : j ∈ cites p i) (hj : j < k.length) :
    (keepClosure k.length p k).getD j false = true := by
  have hfix : markParents p (keepClosure k.length p k) = keepClosure k.length p k := by
    rw [keepClosure_succ, keepClosure_stable]
  have hlen : (keepClosure k.length p k).length = k.length := keepClosure_length k.length p k
  have hi' : i < (keepClosure k.length p k).length := by rw [hlen]; exact hi
  have hj' : j < (keepClosure k.length p k).length := by rw [hlen]; exact hj
  exact markParents_closed hfix hi' h hij hj'

/-! ### (5) Ascending index lists -/

/-- A strictly increasing index list: the shape of a keep-mask read back as indices. -/
inductive Asc : List Nat -> Prop
  | nil : Asc []
  | cons : ∀ (a : Nat) (l : List Nat), (∀ b ∈ l, a < b) -> Asc l -> Asc (a :: l)

/-- The head of an ascending list is below every other element, and the tail is ascending. -/
theorem Asc.destruct : ∀ {a l}, Asc (a :: l) -> (∀ b ∈ l, a < b) ∧ Asc l := by
  intro a l h
  cases h with
  | cons b m hlt hasc => exact ⟨hlt, hasc⟩

/-- The tail of an ascending list is ascending. -/
theorem Asc.tail : ∀ {a l}, Asc (a :: l) -> Asc l := fun h => (Asc.destruct h).2

/-- In an ascending list, every element is below each element after it. -/
theorem Asc.lt_tail : ∀ {a l}, Asc (a :: l) -> ∀ b ∈ l, a < b := fun h => (Asc.destruct h).1

/-- A prefix of an ascending concatenation is itself ascending. -/
theorem Asc.pre : ∀ (pre idx : List Nat), Asc (pre ++ idx) -> Asc pre := by
  intro pre
  induction pre with
  | nil => intro idx _; exact Asc.nil
  | cons y rest ih =>
      intro idx h
      rw [List.cons_append] at h
      obtain ⟨hlt, hasc⟩ := Asc.destruct h
      exact Asc.cons y rest (fun b hb => hlt b (List.mem_append.mpr (Or.inl hb))) (ih idx hasc)

/-- Every element of the prefix of an ascending concatenation is below every element of the suffix. -/
theorem Asc.append_left : ∀ (pre idx : List Nat), Asc (pre ++ idx) ->
    ∀ a, a ∈ pre -> ∀ x, x ∈ idx -> a < x := by
  intro pre
  induction pre with
  | nil => intro idx _ a ha; exact absurd ha (by simp)
  | cons y rest ih =>
      intro idx h a ha x hx
      rw [List.cons_append] at h
      obtain ⟨hlt, hasc⟩ := Asc.destruct h
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hlt x (List.mem_append.mpr (Or.inr hx))
      · exact ih idx hasc a ha x hx

/-- Appending a largest element to an ascending list keeps it ascending. -/
theorem Asc.append_single : ∀ (l : List Nat) (a : Nat), Asc l -> (∀ b ∈ l, b < a) ->
    Asc (l ++ [a]) := by
  intro l
  induction l with
  | nil => intro a _ _; exact Asc.cons a [] (by simp) Asc.nil
  | cons x xs ih =>
      intro a hasc hlt
      show Asc (x :: (xs ++ [a]))
      refine Asc.cons x (xs ++ [a]) ?_
        (ih a (Asc.tail hasc) (fun b hb => hlt b (List.mem_cons.mpr (Or.inr hb))))
      intro b hb
      rw [List.mem_append] at hb
      rcases hb with hbx | hba
      · exact Asc.lt_tail hasc b hbx
      · have hb'a : b = a := by simpa using hba
        subst hb'a
        exact hlt x (List.Mem.head _)

/-- Keeping the head when the predicate holds of it. -/
theorem filter_cons_pos_of_lt {a x : Nat} : ∀ (xs : List Nat), x < a ->
    List.filter (fun y => y < a) (x :: xs) = x :: List.filter (fun y => y < a) xs := by
  intro xs h
  refine filter_cons_pos ?_
  exact decide_eq_true h

/-- The indices below n that satisfy a predicate, in their natural order, form an ascending list. -/
theorem Asc.range_filter : ∀ (n : Nat) (P : Nat -> Bool), Asc ((List.range n).filter P) := by
  intro n P
  induction n with
  | zero => exact Asc.nil
  | succ n ih =>
      rw [List.range_succ, List.filter_append]
      have h2 : List.filter P [n] = (if P n then [n] else []) := by
        rw [List.filter_cons, List.filter_nil]
      rw [h2]
      by_cases hP : P n
      · rw [if_pos hP]
        refine Asc.append_single ((List.range n).filter P) n ih (fun b hb => ?_)
        have : b < n := List.mem_range.mp (List.mem_of_mem_filter hb)
        omega
      · rw [if_neg hP, List.append_nil]
        exact ih

/-- In an ascending list, the number of elements below a member is its position. -/
theorem rget_filter_len_of_Asc : ∀ (l : List Nat) (a : Nat), Asc l -> a ∈ l ->
    rget l (l.filter fun x => x < a).length = some a := by
  intro l
  induction l with
  | nil => intro a _ h; exact absurd h (by simp)
  | cons x xs ih =>
      intro a hasc ha
      obtain ⟨hlt, hasc'⟩ := Asc.destruct hasc
      by_cases hax : a = x
      · rw [hax]
        have hnil : List.filter (fun y => y < x) xs = [] :=
          filter_eq_nil_of' xs x (fun b hb => hlt b hb)
        rw [filter_cons_neg xs (by omega), hnil, List.length_nil]
        rfl
      · rw [List.mem_cons] at ha
        have ha' : a ∈ xs := ha.resolve_left hax
        have hx : x < a := hlt a ha'
        rw [filter_cons_pos_of_lt xs hx, List.length_cons]
        exact ih a hasc' ha'

/-- Everything below a prefix element is a prefix element: the renumbering restricted to the prefix is
the prefix's own numbering. -/
theorem filter_pre_of_Asc : ∀ (pre idx : List Nat) (a : Nat), Asc (pre ++ idx) -> a ∈ pre ->
    ((pre ++ idx).filter fun x => x < a) = pre.filter fun x => x < a := by
  intro pre
  induction pre with
  | nil => intro idx a _ ha; exact absurd ha (by simp)
  | cons y rest ih =>
      intro idx a hasc ha
      rw [List.cons_append]
      obtain ⟨hlt, hasc'⟩ := Asc.destruct hasc
      rw [List.mem_cons] at ha
      rcases ha with heq | ha
      · rw [heq]
        have h1 : List.filter (fun x => x < y) (y :: (rest ++ idx)) = [] := by
          rw [filter_cons_neg (rest ++ idx) (by omega),
            filter_eq_nil_of' (rest ++ idx) y (fun z hz => hlt z hz)]
        have h2 : List.filter (fun x => x < y) (y :: rest) = [] := by
          rw [filter_cons_neg rest (by omega),
            filter_eq_nil_of' rest y (fun z hz => hlt z (List.mem_append.mpr (Or.inl hz)))]
        rw [h1, h2]
      · have hy : y < a := hlt a (List.mem_append.mpr (Or.inl ha))
        rw [filter_cons_pos_of_lt (rest ++ idx) hy, filter_cons_pos_of_lt rest hy]
        rw [ih idx a hasc' ha]

/-- Snoc-then-append is append-cons. -/
theorem append_snoc_cons : ∀ (pre idx : List Nat) (i : Nat),
    (pre ++ [i]) ++ idx = pre ++ (i :: idx) := by
  intro pre
  induction pre with
  | nil => intro idx i; rfl
  | cons y rest ih =>
      intro idx i
      show y :: ((rest ++ [i]) ++ idx) = y :: (rest ++ i :: idx)
      rw [ih idx i]

/-- A kept index below the head of the remaining list is in the prefix already emitted. -/
theorem Asc.mem_prefix_of_lt : ∀ (pre : List Nat) (i : Nat) (idx : List Nat) (a : Nat),
    Asc (pre ++ i :: idx) -> a ∈ pre ++ i :: idx -> a < i -> a ∈ pre := by
  intro pre i idx a hasc ha hlt
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · exact ha
  · rw [List.mem_cons] at ha
    rcases ha with heq | ha
    · rw [heq] at hlt
      exact absurd hlt (by omega)
    · have hia : i < a := by
          have h2 : Asc ((pre ++ [i]) ++ idx) := by
            rw [append_snoc_cons]
            exact hasc
          exact Asc.append_left (pre ++ [i]) idx h2 i (by simp) a ha
      omega

/-! ### (6) The keep-mask as indices, and pruning -/
/-- The mask prune starts from: the last line only. -/
def lastMark (p : List Line) : List Bool :=
  (List.range p.length).map fun i => i + 1 == p.length

/-- The initial mask has exactly one entry per line of the proof. -/
theorem lastMark_length (p : List Line) : (lastMark p).length = p.length := by
  rw [lastMark]
  simp [List.length_map, List.length_range]

/-- The last line is marked: the empty clause is in the closure by construction. -/
theorem lastMark_last {p : List Line} (hne : p ≠ []) :
    (lastMark p).getD (p.length - 1) false = true := by
  cases p with
  | nil => exact absurd rfl hne
  | cons a rest =>
      have hlen : (a :: rest).length = rest.length + 1 := rfl
      rw [lastMark, hlen]
      have := getD_map_range (rest.length + 1) rest.length
        (fun i => i + 1 == rest.length + 1) (by omega)
      simp

/-- The lines prune keeps, as indices into p: the citation closure of the last line. -/
def keepIdx (p : List Line) : List Nat :=
  (List.range p.length).filter fun i => (keepClosure p.length p (lastMark p)).getD i false

/-- An index is kept exactly when it is in range and the closure mask marks it. -/
theorem mem_keepIdx {p : List Line} {i : Nat} :
    i ∈ keepIdx p <-> i < p.length ∧
      (keepClosure p.length p (lastMark p)).getD i false = true := by
  unfold keepIdx
  rw [List.mem_filter, List.mem_range]

/-- Every kept index is in range. -/
theorem keepIdx_lt {p : List Line} {i : Nat} (h : i ∈ keepIdx p) : i < p.length :=
  (mem_keepIdx.mp h).1

/-- The last line's index is kept: the closure starts from it and only grows. -/
theorem last_mem_keepIdx {p : List Line} (hne : p ≠ []) : p.length - 1 ∈ keepIdx p := by
  rw [mem_keepIdx]
  refine ⟨?_, keepClosure_mono p.length p (lastMark p) (p.length - 1) (lastMark_last hne)⟩
  cases p with
  | nil => exact absurd rfl hne
  | cons a rest => show rest.length + 1 - 1 < rest.length + 1; omega

/-- The kept indices are closed under citations. -/
theorem keepIdx_closed {p : List Line} {i j : Nat} (hi : i ∈ keepIdx p)
    (hij : j ∈ cites p i) (hj : j < p.length) : j ∈ keepIdx p := by
  have hlen : (lastMark p).length = p.length := lastMark_length p
  rw [mem_keepIdx] at hi ⊢
  have h1 : i < (lastMark p).length := by rw [hlen]; exact hi.1
  have h2 : (keepClosure (lastMark p).length p (lastMark p)).getD i false = true := by
    rw [hlen]; exact hi.2
  have h3 : j < (lastMark p).length := by rw [hlen]; exact hj
  have hres := keepClosure_closed (p := p) h1 h2 hij h3
  rw [hlen] at hres
  exact ⟨hj, hres⟩

/-- The kept indices come out in strictly increasing order. -/
theorem keepIdx_Asc (p : List Line) : Asc (keepIdx p) := by
  unfold keepIdx
  exact Asc.range_filter _ _

/-- The new position of a kept index: how many kept indices precede it. -/
def posOf (kept : List Nat) (j : Nat) : Nat := (kept.filter fun x => x < j).length

/-- Keep the lines indexed by idx, renumbering every citation by its position in kept. -/
def restrictFrom (p : List Line) (kept idx : List Nat) : List Line :=
  idx.map fun i => reindex p (posOf kept) i

/-- The whole pruned proof. -/
def restrict (p : List Line) (kept : List Nat) : List Line := restrictFrom p kept kept

/-- prune is restrict at its own keep-mask: the definition restated, so the theorems below can talk
about it. -/
theorem prune_eq (p : List Line) : prune p = restrict p (keepIdx p) := rfl

/-- Emitting one more line: the head is renumbered and the tail is emitted after it. -/
theorem restrictFrom_cons (p : List Line) (kept : List Nat) (i : Nat) (idx : List Nat) :
    restrictFrom p kept (i :: idx) =
      reindex p (posOf kept) i :: restrictFrom p kept idx := rfl

/-- The clauses of a pruned prefix extended by one line. -/
theorem clList_restrictFrom_append (p : List Line) (kept pre : List Nat) (i : Nat) :
    clList (restrictFrom p kept (pre ++ [i])) =
      clList (restrictFrom p kept pre) ++ [(reindex p (posOf kept) i).cl] := by
  unfold restrictFrom clList
  rw [List.map_append, List.map_singleton, List.map_append, List.map_singleton]

/-- Emitting no lines yields the empty proof. -/
theorem restrictFrom_nil (p : List Line) (kept : List Nat) : restrictFrom p kept [] = [] := rfl

/-- The pruned proof has exactly one line per kept index. -/
theorem restrict_length (p : List Line) (kept : List Nat) :
    (restrict p kept).length = kept.length := by
  unfold restrict restrictFrom
  simp [List.length_map]

/-- Reading the pruned proof at the new position of a kept index. -/
theorem restrict_rget {p : List Line} (kept : List Nat) (a : Nat) (hasc : Asc kept)
    (ha : a ∈ kept) :
    rget (restrict p kept) (posOf kept a) = some (reindex p (posOf kept) a) := by
  show rget (kept.map (fun i => reindex p (posOf kept) i)) (posOf kept a) = _
  rw [rget_map]
  have hpos : rget kept (posOf kept a) = some a := by
    show rget kept (kept.filter fun x => x < a).length = some a
    exact rget_filter_len_of_Asc kept a hasc ha
  rw [hpos]
  rfl

/-- Reading the pruned prefix at the new position of a kept index gives that index's clause. -/
theorem rget_clList_restrictFrom {p : List Line} (kept pre idx : List Nat) (a : Nat)
    (hke : kept = pre ++ idx) (hasc : Asc kept) (ha : a ∈ pre) :
    rget (clList (restrictFrom p kept pre)) (posOf kept a) = some (lineAt p a).cl := by
  have hasc' : Asc (pre ++ idx) := by rw [← hke]; exact hasc
  have hpos : posOf kept a = (pre.filter fun x => x < a).length := by
    unfold posOf
    rw [hke, filter_pre_of_Asc pre idx a hasc' ha]
  have hpre : Asc pre := Asc.pre pre idx hasc'
  rw [hpos]
  show rget ((pre.map (fun x => reindex p (posOf kept) x)).map Line.cl)
      (pre.filter fun x => x < a).length = some (lineAt p a).cl
  rw [rget_map, rget_map]
  have hget : rget pre (pre.filter fun x => x < a).length = some a :=
    rget_filter_len_of_Asc pre a hpre ha
  rw [hget]
  show some ((reindex p (posOf kept) a).cl) = some (lineAt p a).cl
  rw [reindex_cl]

/-- **The pruner preserves legal derivations.** Let kept be an ascending, citation-closed set of
in-range indices into a justified proof p. Then the lines of kept, renumbered by their positions, are
again each an initial clause or a resolution of two earlier lines. -/
theorem AllOK_restrictFrom {f : CNF} {p : List Line} (hall : AllOK f [] p) :
    ∀ (idx : List Nat) (pre kept : List Nat), kept = pre ++ idx ->
      (∀ i ∈ kept, i < p.length) -> Asc kept ->
      (∀ i ∈ kept, ∀ j, j ∈ cites p i -> j < p.length -> j ∈ kept) ->
        AllOK f (clList (restrictFrom p kept pre)) (restrictFrom p kept idx) := by
  intro idx
  induction idx with
  | nil =>
      intro pre kept _ _ _ _
      rw [restrictFrom_nil]
      exact AllOK.nil f (clList (restrictFrom p kept pre))
  | cons i rest ih =>
      intro pre kept hke hlt hasc hclosed
      have hke' : kept = (pre ++ [i]) ++ rest := by
        rw [hke]
        exact (append_snoc_cons pre rest i).symm
      have hrec : AllOK f (clList (restrictFrom p kept (pre ++ [i])))
          (restrictFrom p kept rest) :=
        ih (pre ++ [i]) kept hke' hlt hasc hclosed
      rw [clList_restrictFrom_append p kept pre i] at hrec
      rw [restrictFrom_cons]
      refine AllOK.cons f (clList (restrictFrom p kept pre)) _ _ ?_ hrec
      have hi : i < p.length := hlt i (by rw [hke]; simp)
      obtain ⟨l, hl⟩ := Encode.rget_lt p i hi
      have hline : lineOK f (clList (List.take i p)) l = true :=
        AllOK_lineOK_of p [] hall i l hl
      have hlineAt : lineAt p i = l := lineAt_of_rget hl
      cases l with
      | mk cl why =>
          cases why with
          | orig n =>
              have hw : (lineAt p i).why = Just.orig n := by rw [hlineAt]
              have hcl : (lineAt p i).cl = cl := by rw [hlineAt]
              rw [reindex_orig hw, hcl]
              exact lineOK_orig_iff.mpr (lineOK_orig_iff.mp hline)
          | res a b v =>
              have hw : (lineAt p i).why = Just.res a b v := by rw [hlineAt]
              have hcl0 : (lineAt p i).cl = cl := by rw [hlineAt]
              rw [reindex_res hw, hcl0]
              obtain ⟨c₁, c₂, h1, h2, hp, hn, hcl⟩ := lineOK_res_some hline
              have hac : a ∈ cites p i := (cites_res (p := p) (i := i) (h := hw)).1
              have hbc : b ∈ cites p i := (cites_res (p := p) (i := i) (h := hw)).2
              have ha' : a < i := lt_of_mem_cites hall hi hac
              have hb' : b < i := lt_of_mem_cites hall hi hbc
              have hka : a ∈ kept := hclosed i (by rw [hke]; simp) a hac (Nat.lt_trans ha' hi)
              have hkb : b ∈ kept := hclosed i (by rw [hke]; simp) b hbc (Nat.lt_trans hb' hi)
              have hasc'' : Asc (pre ++ i :: rest) := by rw [← hke]; exact hasc
              have hka' : a ∈ pre ++ i :: rest := by rw [← hke]; exact hka
              have hkb' : b ∈ pre ++ i :: rest := by rw [← hke]; exact hkb
              have hpa : a ∈ pre := Asc.mem_prefix_of_lt pre i rest a hasc'' hka' ha'
              have hpb : b ∈ pre := Asc.mem_prefix_of_lt pre i rest b hasc'' hkb' hb'
              have hc1 : c₁ = (lineAt p a).cl := by
                have h1' : rget (clList (List.take i p)) a =
                    (rget (List.take i p) a).map Line.cl := rget_map Line.cl _ _
                rw [h1'] at h1
                have htake : rget (List.take i p) a = rget p a :=
                  rget_take p i a ha' (Nat.le_of_lt hi)
                rw [htake] at h1
                obtain ⟨x, hxa, hcl1⟩ := Option.map_eq_some_iff.mp h1
                have hx : lineAt p a = x := lineAt_of_rget hxa
                rw [hx]
                exact hcl1.symm
              have hc2 : c₂ = (lineAt p b).cl := by
                have h2' : rget (clList (List.take i p)) b =
                    (rget (List.take i p) b).map Line.cl := rget_map Line.cl _ _
                rw [h2'] at h2
                have htake : rget (List.take i p) b = rget p b :=
                  rget_take p i b hb' (Nat.le_of_lt hi)
                rw [htake] at h2
                obtain ⟨x, hxb, hcl2⟩ := Option.map_eq_some_iff.mp h2
                have hx : lineAt p b = x := lineAt_of_rget hxb
                rw [hx]
                exact hcl2.symm
              have hra : rget (clList (restrictFrom p kept pre)) (posOf kept a) =
                  some (lineAt p a).cl :=
                rget_clList_restrictFrom kept pre (i :: rest) a hke hasc hpa
              have hrb : rget (clList (restrictFrom p kept pre)) (posOf kept b) =
                  some (lineAt p b).cl :=
                rget_clList_restrictFrom kept pre (i :: rest) b hke hasc hpb
              rw [← hc1] at hra
              rw [← hc2] at hrb
              exact lineOK_res_iff (f := f) hra hrb |>.mpr ⟨hp, hn, hcl⟩

/-- **The pruned producer output is a legal derivation.** -/
theorem AllOK_prune {f : CNF} {p : List Line} (hall : AllOK f [] p) : AllOK f [] (prune p) := by
  rw [prune_eq, restrict]
  refine AllOK_restrictFrom hall (keepIdx p) [] (keepIdx p) ?_ ?_ ?_ ?_
  · rfl
  · intro x hx
    exact keepIdx_lt hx
  · exact keepIdx_Asc p
  · intro x hx y hy hlen
    exact keepIdx_closed hx hy hlen

/-- The last line survives pruning, with its clause intact. -/
theorem prune_last_cl {p : List Line} (hne : p ≠ []) :
    ∃ l ∈ prune p, l.cl = (lineAt p (p.length - 1)).cl := by
  have hmem : (p.length - 1) ∈ keepIdx p := last_mem_keepIdx hne
  have hasc : Asc (keepIdx p) := keepIdx_Asc p
  have hline : rget (prune p) (posOf (keepIdx p) (p.length - 1)) =
      some (reindex p (posOf (keepIdx p)) (p.length - 1)) := by
    rw [prune_eq]
    exact restrict_rget (keepIdx p) (p.length - 1) hasc hmem
  have hlt : posOf (keepIdx p) (p.length - 1) < (prune p).length :=
    rget_lt_of_some (prune p) (posOf (keepIdx p) (p.length - 1)) _ hline
  obtain ⟨l, hl⟩ := Encode.rget_lt (prune p) (posOf (keepIdx p) (p.length - 1)) hlt
  refine ⟨l, Encode.rget_some_mem _ _ _ hl, ?_⟩
  have heq : l = reindex p (posOf (keepIdx p)) (p.length - 1) :=
    Option.some.inj (hl.symm.trans hline)
  rw [heq, reindex_cl]

/-- A non-empty list is its `dropLast> plus its last line, read with `lineAt`. -/
theorem dropLast_lineAt : ∀ (l : List Line), l ≠ [] ->
    l.dropLast ++ [lineAt l (l.length - 1)] = l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
      intro _
      cases xs with
      | nil => show ([] : List Line) ++ [lineAt [x] 0] = x :: []; simp [lineAt]
      | cons y ys =>
          have hne : (y :: ys : List Line) ≠ [] := by simp
          have hrec := ih hne
          show x :: ((y :: ys).dropLast ++ [lineAt (x :: y :: ys) ((x :: y :: ys).length - 1)])
              = x :: y :: ys
          rw [show (x :: y :: ys).length - 1 = (y :: ys).length from rfl]
          have hla : lineAt (x :: y :: ys) ((y :: ys).length) =
              lineAt (y :: ys) ((y :: ys).length - 1) := by
            have hsub : (y :: ys).length - 1 + 1 = (y :: ys).length := by
              simp [List.length_cons]
            have hge : 1 ≤ (y :: ys).length := by simp [List.length_cons]
            unfold lineAt
            rw [← hsub, List.getD_cons_succ, Nat.sub_add_cancel hge]
          rw [hla, hrec]

/-- **The pruner preserves acceptance.** A justified proof whose last line is the empty clause still
refutes after pruning: every surviving line is still a legal step, and the empty clause survives. -/
theorem prune_checkProof {f : CNF} {p : List Line} (hall : AllOK f [] p) (hne : p ≠ [])
    (hlast : (lineAt p (p.length - 1)).cl = []) : checkProof f (prune p) = true := by
  refine checkFrom_true (prune p) [] (AllOK_prune hall) ?_
  obtain ⟨m, hm, he⟩ := prune_last_cl hne
  exact ⟨m, hm, he.trans hlast⟩

/-- A refutation the producer returns is not the empty list. -/
theorem ne_uptoEmpty_of_found {p : List Line} (h : found p = true) : uptoEmpty p ≠ [] := by
  obtain ⟨l, hl, _⟩ := uptoEmpty_found h
  intro hd
  rw [hd] at hl
  exact absurd hl (by simp)

/-- **Soundness of the fast producer including pruning.** -/
theorem unitRefutation_pruned_checkProof {f : CNF} {fuel : Nat} {p : List Line}
    (h : unitRefutation f fuel = some p) : checkProof f (prune p) = true := by
  have hf := found_accOf h
  have hEq : p = uptoEmpty (accOf f fuel) := some_accOf_unitRefutation h
  subst hEq
  refine prune_checkProof (AllOK_unitRefutation h) (ne_uptoEmpty_of_found hf) ?_
  obtain ⟨q, l, hpq, hl⟩ := uptoEmpty_last hf
  have hlen : (uptoEmpty (accOf f fuel)).length - 1 = q.length := by
    rw [hpq]
    simp [List.length_append]
  have hline : lineAt (uptoEmpty (accOf f fuel))
      ((uptoEmpty (accOf f fuel)).length - 1) = l := by
    rw [hlen, hpq]
    unfold lineAt
    exact getD_append_self q l _
  rw [hline]
  exact hl

/-! ### (7) From the producer to a checked code, and to a verdict -/

/-- The fast producer's emitted code for a formula: propagate, prune, serialize. The query-level
emitter unitRefutationCodeOf is this at formulaOf q. -/
def unitCodeOf (f : CNF) (fuel : Nat) : Option (List Int) :=
  (unitRefutation f fuel).map (fun p => proofCode (prune p))

/-- The query-level emitter is the formula-level one evaluated at the query's own CNF. -/
theorem unitRefutationCodeOf_eq (q : Query) (fuel : Nat) :
    unitRefutationCodeOf q fuel = unitCodeOf (formulaOf q) fuel := rfl

/-- Unpacking the emitter. -/
theorem some_unitCodeOf {f : CNF} {fuel : Nat} {c : List Int} (h : unitCodeOf f fuel = some c) :
    ∃ p, unitRefutation f fuel = some p ∧ proofCode (prune p) = c := by
  unfold unitCodeOf at h
  cases h0 : unitRefutation f fuel with
  | none => exact absurd h (by simp [h0])
  | some p =>
      rw [h0] at h
      exact ⟨p, rfl, Option.some.inj h⟩

/-- **The emitted code is accepted by the independent checker.** This is the theorem the commit that
added the producer left open: the bytes unitRefutationCodeOf emits are accepted at the fuel the proof
itself needs, and the proof of that never runs a search. -/
theorem unitCodeOf_sound {f : CNF} {fuel : Nat} {c : List Int}
    (h : unitCodeOf f fuel = some c) : ∃ k, checkCode f k c = true := by
  obtain ⟨p, hp, hc⟩ := some_unitCodeOf h
  refine ⟨(prune p).length + 1, ?_⟩
  rw [← hc, checkCode_iff_checkProof]
  exact unitRefutation_pruned_checkProof hp

/-- The same for the query-level emitter. -/
theorem unitRefutationCodeOf_sound {q : Query} {fuel : Nat} {c : List Int}
    (h : unitRefutationCodeOf q fuel = some c) : ∃ k, checkCode (formulaOf q) k c = true := by
  rw [unitRefutationCodeOf_eq] at h
  exact unitCodeOf_sound h

/-- **Safety from the fast producer.** The hypotheses are the ones CheckedSafe needs and no more; the
search is never mentioned. -/
theorem boundedSafe_of_unitCode {q : Query} (fuel : Nat)
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    {c : List Int} (h : unitRefutationCodeOf q fuel = some c) : boundedSafeGoals q :=
  boundedSafe_of_code hq hne hU hsecStore hgap c (unitRefutationCodeOf_sound h)

/-- The analyser's answer from the fast producer's code, with no solver replay. -/
theorem analyzeQuery_encodingUnsat_of_unitCode {q : Query} (fuel : Nat)
    (hwf : WellFormed q) (hne : q.goals ≠ []) (hq : ∀ g ∈ q.goals, goalEncoded g)
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    {c : List Int} (h : unitRefutationCodeOf q fuel = some c) :
    analyzeQuery q = Result.encodingUnsat := by
  obtain ⟨k, hk⟩ := unitRefutationCodeOf_sound h
  exact analyzeQuery_encodingUnsat_of_code hwf hne hq hU hk

/-- **Converse of the acceptance lemma:** if the checker walked a proof whose last line is the first
empty one, every line of it is justified. This is what lets a certificate that was checked by decide
feed the pruning theorem. -/
theorem AllOK_of_checkFrom : ∀ (f : CNF) (q : List Line) (l : Line) (base : List Clause),
    checkFrom f base (q ++ [l]) = true -> l.cl = [] -> (∀ m ∈ q, m.cl ≠ []) ->
      AllOK f base (q ++ [l]) := by
  intro f q
  induction q with
  | nil =>
      intro l base h hl _
      have hnil : ([] : List Line) ++ [l] = [l] := rfl
      rw [hnil] at h ⊢
      have h1 : checkFrom f base [l] = if lineOK f base l then true else false := by
        rw [checkFrom_cons, if_pos hl]
      rw [h1] at h
      have hok : lineOK f base l = true := by
        by_cases hc : lineOK f base l
        · exact hc
        · rw [if_neg hc] at h
          exact absurd h (by decide)
      exact AllOK.cons f base l [] hok (AllOK.nil f (base ++ [l.cl]))
  | cons x xs ih =>
      intro l base h hl hne
      have hcons : x :: xs ++ [l] = x :: (xs ++ [l]) := rfl
      rw [hcons] at h ⊢
      have hx : x.cl ≠ [] := hne x (by simp)
      have h1 : checkFrom f base (x :: (xs ++ [l])) =
          if lineOK f base x then checkFrom f (base ++ [x.cl]) (xs ++ [l]) else false := by
        rw [checkFrom_cons, if_neg hx]
      rw [h1] at h
      have hok : lineOK f base x = true := by
        by_cases hc : lineOK f base x
        · exact hc
        · rw [if_neg hc] at h
          exact absurd h (by decide)
      have hrest : checkFrom f (base ++ [x.cl]) (xs ++ [l]) = true := by
        rw [if_pos hok] at h
        exact h
      refine AllOK.cons f base x (xs ++ [l]) hok (ih l (base ++ [x.cl]) hrest hl ?_)
      intro m hm
      exact hne m (List.mem_cons.mpr (Or.inr hm))

/-- Reading a checked proof back as a justified one, when its last line is the first empty one. -/
theorem AllOK_of_checkProof {f : CNF} {p : List Line} (h : checkProof f p = true)
    (hlast : (lineAt p (p.length - 1)).cl = [])
    (hne : ∀ m ∈ p.dropLast, m.cl ≠ []) : AllOK f [] p := by
  have hp : p ≠ [] := by
    intro hpnil
    rw [hpnil] at h
    exact absurd h (by simp [checkProof, checkFrom_nil])
  have hsplit : p = p.dropLast ++ [lineAt p (p.length - 1)] := (dropLast_lineAt p hp).symm
  have hthis := AllOK_of_checkFrom f p.dropLast (lineAt p (p.length - 1)) []
    (by rw [← hsplit]; exact h) hlast hne
  rw [hsplit]
  exact hthis


/-! ### (8) Kernel-checked gates -/

/-- A formula small enough for the kernel to propagate on. It has no empty clause, and its refutation
needs two propagation rounds: the unit pos 0 shrinks the clause neg 0 or pos 1 down to pos 1, and only
then can the unit neg 1 be resolved away. -/
def tinyF : CNF := { clauses := [[pos 0], [neg 0, pos 1], [neg 1]] }

/-- The fuel the tiny demo needs. -/
def tinyFuel : Nat := 2

/-- The producer's refutation of tinyF, unpruned. -/
def tinyP : List Line := (unitRefutation tinyF tinyFuel).getD []

/-- The producer refutes tinyF: the kernel evaluates the propagation. -/
theorem tiny_emitted_bool : (unitRefutation tinyF tinyFuel).isSome = true := by decide

/-- The producer's answer, as a some. -/
theorem tiny_some : unitRefutation tinyF tinyFuel = some tinyP := by
  cases h0 : unitRefutation tinyF tinyFuel with
  | none => exact absurd tiny_emitted_bool (by simpa [h0])
  | some p => simp [tinyP, h0]

/-- The unpruned refutation is 6 lines and pruning drops the one line the empty clause does not depend
on: 5 lines survive. -/
theorem tiny_sizes : tinyP.length = 6 ∧ (prune tinyP).length = 5 := by decide

/-- **The pruned producer output is accepted - by the soundness theorem, not by decide.** -/
theorem tiny_prune_accepted : checkProof tinyF (prune tinyP) = true :=
  unitRefutation_pruned_checkProof tiny_some

/-- And the kernel agrees by its own lights: the same proposition, discharged by replaying the checker.
This is the cross-check that the theorem above is about the real thing. -/
theorem tiny_prune_accepted_decide : checkProof tinyF (prune tinyP) = true := by decide

/-- The code the producer emits for tinyF. -/
def tinyCode : List Int := (unitCodeOf tinyF tinyFuel).getD []

/-- The producer emits a code for tinyF, and that code is exactly tinyCode. -/
theorem tiny_emitted : unitCodeOf tinyF tinyFuel = some tinyCode := by
  cases h0 : unitCodeOf tinyF tinyFuel with
  | none => exact absurd (by decide : (unitCodeOf tinyF tinyFuel).isSome = true) (by simpa [h0])
  | some c => simp [tinyCode, h0]

/-- The emitted code is accepted - by the theorem. -/
theorem tiny_code_accepted : ∃ k, checkCode tinyF k tinyCode = true :=
  unitCodeOf_sound tiny_emitted

/-- The emitted code is accepted - by the kernel, independently. -/
theorem tiny_code_checked : checkCode tinyF 6 tinyCode = true := by decide

/-- The refutation the embedded qg certificate bytes decode to. -/
def qgProof : List Line := (proofOfCode qgCheckFuel qgCode).getD []

/-- The certificate decodes at the fuel the checker already accepts. -/
theorem proofOfCode_qg_bool : (proofOfCode qgCheckFuel qgCode).isSome = true := by decide

/-- The 138 embedded integers decode to qgProof at the certificate's own fuel. -/
theorem proofOfCode_qg : proofOfCode qgCheckFuel qgCode = some qgProof := by
  cases h0 : proofOfCode qgCheckFuel qgCode with
  | none => exact absurd proofOfCode_qg_bool (by simpa [h0])
  | some p => simp [qgProof, h0]

/-- The embedded certificate is accepted as a proof: qg_checked read through the decoder. -/
theorem qg_proof_check : checkProof (formulaOf qg) qgProof = true := by
  have h := checkCode_of (f := formulaOf qg) proofOfCode_qg
  rw [qg_checked] at h
  exact h

/-- Its last line is the empty clause, and no earlier line is - so the checker walked all 21 lines. -/
theorem qg_last_empty : (lineAt qgProof (qgProof.length - 1)).cl = [] := by decide

/-- No line of the certificate before the last one is empty, so the checker really walked all 21 lines. -/
theorem qg_no_earlier_empty : ∀ m ∈ qgProof.dropLast, m.cl ≠ [] := by decide

/-- Every line of the embedded certificate is a legal derivation step. -/
theorem qg_proof_AllOK : AllOK (formulaOf qg) [] qgProof :=
  AllOK_of_checkProof qg_proof_check qg_last_empty qg_no_earlier_empty

/-- The certificate is not the empty proof. -/
theorem qg_proof_ne : qgProof ≠ [] := by
  intro h
  have h2 : checkProof (formulaOf qg) ([] : List Line) = true := by
    rw [← h]
    exact qg_proof_check
  exact absurd h2 (by simp [checkProof, checkFrom_nil])

/-- **The pruner preserves acceptance on the real certificate.** The 21-line qg proof is accepted;
pruning it keeps it accepted - and that implication is a theorem now, not a decision. -/
theorem qg_pruned_accepted : checkProof (formulaOf qg) (prune qgProof) = true :=
  prune_checkProof qg_proof_AllOK qg_proof_ne qg_last_empty

set_option maxRecDepth 20000 in
/-- The same fact by the kernel's own lights: decode the certificate, prune it, and check all 21
lines. About 0.6 s of kernel time, and it is the cross-check that `qg_pruned_accepted` is about the
real checker rather than about a vacuous hypothesis. -/
theorem qg_pruned_accepted_decide : checkProof (formulaOf qg) (prune qgProof) = true := by decide

set_option maxRecDepth 20000 in
/-- The pruner leaves the embedded certificate exactly as it found it: the 138 integers are already
closed under their own dependencies. -/
theorem qg_prune_is_idempotent : proofCode (prune qgProof) = qgCode := by decide

/-- **The certificate is generated, not hand-carried - conditionally on the producer's output.** The
hypothesis is exactly the equation the demo program checks at run time
(AnalyzerEvidence.qg_producer_reproduces); the conclusion follows from the soundness theorems above,
and its proof never evaluates the search. -/
theorem qg_produced_is_accepted :
    unitRefutationCodeOf qg qgFuel = some qgCode ->
      ∃ k, checkCode (formulaOf qg) k qgCode = true :=
  fun h => unitRefutationCodeOf_sound h

/-- The same, stated against the Bool the demo program prints. -/
theorem qg_producer_reproduces_is_enough : qg_producer_reproduces = true ->
    ∃ k, checkCode (formulaOf qg) k qgCode = true :=
  fun h => qg_produced_is_accepted (of_decide_eq_true h)

/-- And the security statement that follows from the producer's own output, with no solver anywhere. -/
theorem qg_boundedSafe_of_produced : qg_producer_reproduces = true -> boundedSafeGoals qg :=
  fun h => boundedSafe_of_unitCode qgFuel EndToEnd.qg_goals EndToEnd.qg_ne EndToEnd.qg_hU
    EndToEnd.qg_hsec EndToEnd.qg_gap (of_decide_eq_true h)

end ProtSat.UnitRefute
