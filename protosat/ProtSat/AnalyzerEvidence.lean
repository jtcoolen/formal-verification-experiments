/-
Copyright (2026) Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Refute
import ProtSat.EndToEnd
import ProtSat.AuthGap

/-!
# ProtSat: the analyser's safety verdict carried by a checked certificate

## Why this module exists

`ProtSat.Analyzer.analyze` and `ProtSat.Query.analyzeQuery` answer a safety question by *running a
solver*: `encodingUnsat` means "DPLL returned `none`". To believe that inside the kernel you have to
make the kernel replay the search, which `EndToEnd.lean` measures at minutes for a few hundred
variables and out of reach for a thousand.

The library already has every part of the other shape of trust - `Refute.refutationOf` (a saturating
resolution prover, proved sound by `refute_sound`), `Serialize.proofCode` (a refutation as a flat
`List Int`), `Serialize.checkCode` (decode and check, proved sound by `checkCode_sound`), and
`CheckedSafe.boundedSafe_of_checkedCode` (a checked code implies `boundedSafeGoals`). What was
missing is the wire that connects them to the analyser's own entry point. This module is that wire:

    query -> refutationCodeOf q fuel -> some code -> checkCode (encode ...) k code = true
          -> boundedSafeGoals q

Nothing in the chain re-runs DPLL, and nothing in the chain trusts the producer: the only trusted
component is the line-by-line resolution checker.

## What is in the file

* `refutationCodeOf` - the emitter: saturate the query's CNF with a fuel budget, serialize the
  refutation. `checkCode_of_refutationCodeOf` says the emitted code is accepted by the checker at
  the fuel the proof itself needs; `boundedSafe_of_emittedCode` turns that into `boundedSafeGoals
  q`; `analyzeQuery_encodingUnsat_of_code` turns it into the analyser's own answer, so the verdict
  and the certificate are shown to be the same fact rather than two computations that happen to
  agree.
* A second producer, `unitRefutationCodeOf`: unit propagation with dependency pruning. It exists
  because the proved-sound saturation engine cannot refute a real protocol formula at any affordable
  fuel - see "What is still missing" below. Its output is *not* proved sound here; what makes an
  artifact from it trustworthy is that `checkCode` accepts that artifact, and `checkCode_sound`
  needs no hypothesis about who produced the code.
* Two decided examples, both on models already in the repo:
  - `AuthGap.qs` (the secrecy reading of `Regressions.Authentication`): the saturation engine
    emits a code at fuel 0, the kernel decides that it does (`qs_emitted`), and safety follows
    from the engine's own soundness theorem. Honest caveat, already documented in `AuthGap`:
    that CNF literally contains the empty clause (`AuthGap.why_the_formula_is_unsat`), so its
    refutation is one line.
  - `EndToEnd.qg` (the guarded protocol: 246 variables, 291 clauses, no empty clause): a 21-line,
    138-integer certificate the kernel checks in a third of a second, from which both the analyser's
    `encodingUnsat` answer and `boundedSafeGoals qg` are derived - no solver replay anywhere.
    `EndToEnd.qg_verdict` reaches the same equation through DPLL;
    `qg_verdict_and_certificate_agrees`
    states the two together.

## Measured cost

Whole file, `lake env lean ProtSat/AnalyzerEvidence.lean`: about 3 s, of which about 1.2 s is
loading the imports. Each kernel gate was timed on its own, in a file that imports this one and
repeats the same `decide` (the baseline import cost is subtracted):

| gate | what the kernel replays | wall clock |
|---|---|---|
| `qg_checked` | decode 138 integers, check 21 lines against `encode Guard GB` | about 0.3 s |
| `qg_rejects_other_formula` | the same bytes against the leaky variant, rejected | under 0.1 s |
| `qs_emitted` | `saturate 0` of an 803-clause formula, then `isSome` | about 0.6 s |
| `qg_size` | decode the code and count its lines and literals | about 0.1 s |

For comparison, `EndToEnd.qg_unsat` - re-running DPLL on the same 246-variable formula in the
kernel - is measured in the `EndToEnd` header at about 20 s, and the same file records that the
replay is out of reach at 1263 variables. Checking a certificate costs a fraction of a second at
this size and grows with the certificate, not with the search. No gate here exceeds 60 s, and
every one of them is discharged by the kernel: nothing is evaluated outside it, and no decision
procedure is called through the FFI.

## What is still missing for a certificate-emitting analyser in general

* **Fuel policy.** `refutationCodeOf` takes its fuel from the caller and returns `none` when the
  budget runs out. Nothing picks a budget from the query's size, and no `Result.unknown` is produced
  from a `none`: `Query.UnknownReason.resourceExhausted` exists and the CNF route still never uses
  it.
* **The proved-sound engine is too weak to be the producer.** `Refute`'s own header measures
  `saturate 1 (encode Guard GB)` at 1150 lines and `saturate 2` at 37167 lines, about 19 minutes of
  evaluation, and neither reaches the empty clause. This module confirms that from the other side:
  unit propagation refutes the same formula with 200 derived lines and 491 lines in total, while
  `saturate 1` of the same formula is 1150 lines and does not reach the empty clause. Subsumption,
  unit propagation and polarity-directed pivoting are what would close the gap; the first two are
  prototyped here, neither is in the proved-sound engine.
* **The fast producer is not proved sound.** `unitRefutationCodeOf` is a computation whose output
  happens to be accepted; `refutationCodeOf` is a computation proved to produce accepted output.
  Making the fast engine match the proved one - including a proof that pruning preserves
  acceptance - is the remaining proof work.
* **Artifact size.** The unit-propagation producer's unpruned refutation of `qg` is 491 lines and
  3577 integers; the pruned artifact embedded below is 21 lines and 138 integers. Embedding a
  certificate in the source is only viable after pruning, and the proved-sound engine has no
  pruner at all - `refutationCodeOf` emits the whole prefix up to the empty clause.
* **The agreement-goal gap is untouched.** The CNF encodes secrecy only (`Query.goalEncoded`), so
  every theorem here still carries `∀ g ∈ q.goals, goalEncoded g`. A query selecting
  `Goal.agreement` is refused by `analyzeQuery`, and `AuthGap.attacked_for_agreement` shows such a
  query really is attacked. No certificate in this file changes that.
-/

namespace ProtSat.AnalyzerEvidence

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  Resolution Serialize CheckedSafe Refute

/-! ### (a) The emitter: a query in, a serialized refutation out -/

/-- The formula a query asks about: the CNF the analyser would hand to the solver. -/
def formulaOf (q : Query) : CNF := encode q.protocol q.bounds

/-- **The emitter.** Saturate the query's formula with `fuel` rounds of resolution, take the
refutation the engine reaches (the lines up to the first empty clause) and serialize it as a flat
list of integers. `none` means the budget did not reach a refutation - a resource answer, not a
verdict. -/
def refutationCodeOf (q : Query) (fuel : Nat) : Option (List Int) :=
  (refutationOf (formulaOf q) fuel).map proofCode

/-- The driver's view of the emitter: did it produce anything at this budget? -/
def emitted (q : Query) (fuel : Nat) : Bool := (refutationCodeOf q fuel).isSome

/-- Unpacking the emitter: if it answers `some c` then the engine reached a refutation `p` and `c`
is exactly `p`'s code. -/
theorem some_refutationCodeOf {q : Query} {fuel : Nat} {c : List Int}
    (h : refutationCodeOf q fuel = some c) :
    ∃ p, refutationOf (formulaOf q) fuel = some p ∧ proofCode p = c := by
  cases h0 : refutationOf (formulaOf q) fuel with
  | none => simp [refutationCodeOf, h0] at h
  | some p =>
      have h2 : refutationCodeOf q fuel = some (proofCode p) := by rw [refutationCodeOf, h0]; rfl
      rw [h2] at h
      exact ⟨p, rfl, Option.some.inj h⟩

/-- **The emitted code is accepted by the independent checker.** The decode fuel is one unit per
line of the refutation, plus one - the fuel `Serialize.proofOfCode_proofCode'` needs. No solver
appears: what is used is `refute_sound`, which is about the saturation engine, and
`checkCode_iff_checkProof`, which is about the format. -/
theorem checkCode_of_refutationCodeOf {q : Query} {fuel : Nat} {c : List Int}
    (h : refutationCodeOf q fuel = some c) : ∃ k, checkCode (formulaOf q) k c = true := by
  obtain ⟨p, hp, hc⟩ := some_refutationCodeOf h
  refine ⟨p.length + 1, ?_⟩
  rw [← hc, checkCode_iff_checkProof]
  exact refute_sound hp

/-- The safety conclusion from any code the checker accepts - the socket an external prover, or
the producer further down this file, plugs into. -/
theorem boundedSafe_of_code {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false) (c : List Int)
    (h : ∃ k, checkCode (formulaOf q) k c = true) : boundedSafeGoals q := by
  obtain ⟨k, hk⟩ := h
  exact boundedSafe_of_checkedCode hq hne hU hsecStore hgap hk

/-- **(b) Emitted evidence is a security statement.** The hypotheses are exactly the ones
`CheckedSafe` needs and no more: the goals the query selected are ones the encoding represents,
something is selected, the bounds name the protocol's closed expressions and its store secrets,
and the value domain has no representability gap. The solver is never mentioned. -/
theorem boundedSafe_of_emittedCode {q : Query} (fuel : Nat)
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    {c : List Int} (h : refutationCodeOf q fuel = some c) : boundedSafeGoals q :=
  boundedSafe_of_code hq hne hU hsecStore hgap c (checkCode_of_refutationCodeOf h)

/-- A safety verdict that cannot be detached from the query it answers: `SafeEvidence` carries the
query, and `Query.lean` records that nothing in the solver route constructs one. -/
def safeEvidence_of_emittedCode {q : Query} (fuel : Nat)
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    {c : List Int} (h : refutationCodeOf q fuel = some c) : SafeEvidence :=
  ⟨q, boundedSafe_of_emittedCode fuel hq hne hU hsecStore hgap h⟩

/-- The contract's answer built from emitted evidence: `Result.boundedSafe`, the case
`Query.analyzeQuery_ne_boundedSafe` says the solver route can never produce. -/
def resultOf_emittedCode {q : Query} (fuel : Nat)
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    {c : List Int} (h : refutationCodeOf q fuel = some c) : Result :=
  Result.boundedSafe (safeEvidence_of_emittedCode fuel hq hne hU hsecStore hgap h)

/-- And it is counted as a security answer by the definition the contract uses to tell security
verdicts apart from formula facts. -/
theorem resultOf_emittedCode_is_security {q : Query} (fuel : Nat)
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : domainGap q.protocol q.bounds = false)
    {c : List Int} (h : refutationCodeOf q fuel = some c) :
    securityResult (resultOf_emittedCode fuel hq hne hU hsecStore hgap h) = true := rfl

/-! ### From a checked code back to the analyser's own answer -/

/-- A checked refutation makes the analyser answer `encodingUnsat` **without running the solver**:
`DPLL.dpll_complete` is applied to the formula fact the checker established, so the equation about
`dpll` becomes a consequence of the certificate instead of a computation the kernel must replay. -/
theorem analyze_encodingUnsat_of_code {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P) {k : Nat} {c : List Int}
    (h : checkCode (encode P B) k c = true) :
    Analyzer.analyze P B = Analyzer.Verdict.encodingUnsat := by
  have hnone : DPLL.dpll (encode P B) = none :=
    (dpll_none_iff_unsat _).mpr (checkCode_sound h)
  have hu : univClosedBool (shapeOf P B) P = true := (univClosedBool_iff _ _).mpr hU
  rw [Analyzer.analyze, if_neg (by simp [hu]), hnone]

/-- A list of goals the encoding represents has nothing unsupported in it. -/
theorem filter_encoded_eq_nil : ∀ (gs : List Goal), (∀ g ∈ gs, goalEncoded g) ->
    gs.filter (fun g => ! goalEncoded g) = []
  | [], _ => rfl
  | g :: rest, h => by
      have hg : goalEncoded g = true := h g (List.Mem.head _)
      simp [hg, filter_encoded_eq_nil rest (fun x hx => h x (List.Mem.tail _ hx))]

/-- A non-empty list is not empty, in the Boolean form the analyser's branch needs. -/
theorem isEmpty_eq_false_of_ne {α : Type} {l : List α} (h : l ≠ []) : l.isEmpty = false := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- No goal of the query is refused by the encoding. -/
theorem unsupported_eq_nil {q : Query} (hq : ∀ g ∈ q.goals, goalEncoded g) :
    unsupported q = [] :=
  by simpa [unsupported] using filter_encoded_eq_nil q.goals hq

/-- **The verdict follows from the certificate.** With the model validated, a goal selected and
every selected goal encoded, a checked code for the query's formula *is* the analyser's answer -
the same equation `analyzeQuery` reaches by running DPLL, obtained here by checking a list of
integers. -/
theorem analyzeQuery_encodingUnsat_of_code {q : Query}
    (hwf : WellFormed q) (hne : q.goals ≠ []) (hq : ∀ g ∈ q.goals, goalEncoded g)
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol) {k : Nat} {c : List Int}
    (h : checkCode (formulaOf q) k c = true) : analyzeQuery q = Result.encodingUnsat := by
  have hana : analyze q.protocol q.bounds = Verdict.encodingUnsat :=
    analyze_encodingUnsat_of_code hU h
  rw [analyzeQuery]
  rw [if_pos (by simpa [WellFormed] using hwf)]
  rw [if_neg (by rw [isEmpty_eq_false_of_ne hne]; decide)]
  rw [if_neg (by rw [unsupported_eq_nil hq]; simp)]
  simp [hana]

/-- The same, for evidence the emitter produced rather than evidence someone handed over. -/
theorem analyzeQuery_encodingUnsat_of_emittedCode {q : Query} (fuel : Nat)
    (hwf : WellFormed q) (hne : q.goals ≠ []) (hq : ∀ g ∈ q.goals, goalEncoded g)
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    {c : List Int} (h : refutationCodeOf q fuel = some c) :
    analyzeQuery q = Result.encodingUnsat := by
  obtain ⟨k, hk⟩ := checkCode_of_refutationCodeOf h
  exact analyzeQuery_encodingUnsat_of_code hwf hne hq hU hk

/-! ### Reading the size of a certificate -/

/-- How many resolution lines a code decodes to at fuel `k`; `0` when it does not decode. -/
def codeLines (k : Nat) (c : List Int) : Nat :=
  match proofOfCode k c with
  | some p => p.length
  | none => 0

/-- How many literal occurrences a code carries - the work the checker has to do. -/
def codeLiterals (k : Nat) (c : List Int) : Nat :=
  match proofOfCode k c with
  | some p => p.foldr (fun l n => l.cl.length + n) 0
  | none => 0

/-- How many of a code's lines are original clauses of the formula rather than resolvents. -/
def codeOrigins (k : Nat) (c : List Int) : Nat :=
  match proofOfCode k c with
  | some p => (p.filter fun l =>
      match l.why with
      | Just.orig _ => true
      | Just.res _ _ _ => false).length
  | none => 0

/-! ### A second producer: unit propagation, then dependency pruning
  ### A second producer: unit propagation, then dependency pruning The engine above is proved
  sound but cannot refute a real protocol formula: saturation resolves every ordered pair of lines
  it holds, so the line list explodes long before the empty clause is reached. The producer here
  uses the standard cheap inference rule instead - resolve every clause against a unit the formula
  has already forced - and then keeps only the lines the empty clause depends on. It is only a
  *producer*: its output is trusted exactly as far as `checkCode` accepts it, and every artifact
  below is accepted.
is accepted. -/

/-- Does `c` hold the literal complementary to `l`? -/
def complements (c : Clause) (l : Lit) : Bool :=
  c.any fun k => k.var == l.var && k.neg == !l.neg

/-- The unit lines of `ls`, paired with their index, counting from `off`. -/
def unitLines : Nat -> List Line -> List (Nat × Lit)
  | _, [] => []
  | off, { cl := [l], why := _ } :: rest => (off, l) :: unitLines (off + 1) rest
  | off, _ :: rest => unitLines (off + 1) rest

/-- Resolve `c` against the unit line `[l]`, dropping the literal of `c` that `l` refutes. The
parents are cited in the order the checker demands: the one carrying the pivot positively first. -/
def resolveWithUnit (i j : Nat) (l : Lit) (c : Clause) : Line :=
  if l.neg then { cl := resolve c [l] l.var, why := Just.res j i l.var }
  else { cl := resolve [l] c l.var, why := Just.res i j l.var }

/-- One propagation round: every line a forced unit shrinks, shrunk. -/
def propagate (acc : List Line) : List (Nat × Lit) -> List Line
  | [] => []
  | (i, l) :: us =>
      let here := (List.range acc.length).filterMap fun j =>
        match rget (clList acc) j with
        | some c => if complements c l then some (resolveWithUnit i j l c) else none
        | none => none
      here ++ propagate acc us

/-- Unit propagation with fuel: rounds until nothing new appears, until the empty clause appears,
or until the budget runs out. -/
def unitSaturate : Nat -> List Line -> List (Nat × Lit) -> List Line
  | 0, acc, _ => acc
  | k + 1, acc, us =>
      let new := novel (clList acc) (propagate acc us)
      if new = [] then acc
      else
        let acc' := acc ++ new
        if found acc' then acc' else unitSaturate k acc' (unitLines acc.length new)

/-- The refutation unit propagation reaches, if it reaches one. -/
def unitRefutation (f : CNF) (fuel : Nat) : Option (List Line) :=
  let s := seed f.clauses 0
  let acc := unitSaturate fuel s (unitLines 0 s)
  if found acc then some (uptoEmpty acc) else none

/-- The lines a line cites. -/
def cites (p : List Line) (i : Nat) : List Nat :=
  match (rget p i).map (fun l => l.why) with
  | some (Just.res a b _) => [a, b]
  | _ => []

/-- One step of backward reachability: mark the parents of everything already marked. -/
def markParents (p : List Line) (keep : List Bool) : List Bool :=
  let add : List Nat := (List.range keep.length).flatMap fun i =>
    if keep.getD i false then cites p i else []
  (List.range keep.length).map fun j => keep.getD j false || add.any (fun x => x == j)

/-- The backward closure of the marked lines, iterated to a fixed point. -/
def keepClosure : Nat -> List Line -> List Bool -> List Bool
  | 0, _, k => k
  | m + 1, p, k => let k' := markParents p k; if k' == k then k else keepClosure m p k'

/-- One line with its citations renumbered after `before` many kept lines precede it. -/
def reindex (p : List Line) (before : Nat -> Nat) (i : Nat) : Line :=
  let l := p.getD i { cl := [], why := Just.orig 0 }
  match l.why with
  | Just.orig a => { cl := l.cl, why := Just.orig a }
  | Just.res a b v => { cl := l.cl, why := Just.res (before a) (before b) v }

/-- **Pruning.** Keep only the lines the empty clause depends on and renumber the citations. The
unpruned refutation of `EndToEnd.qg` is 491 lines and 3577 integers; the pruned one is 21 lines
and 138. Pruning is not yet a proved transformation - the checker's verdict on the pruned artifact
is what licenses the result, and that verdict is decided below. -/
def prune (p : List Line) : List Line :=
  let n := p.length
  let keep := keepClosure n p ((List.range n).map fun i => i + 1 == n)
  let idx := (List.range n).filter fun i => keep.getD i false
  idx.map fun i => reindex p (fun j => (idx.filter fun i => i < j).length) i

/-- The fast producer's emitted code: propagate, prune, serialize. -/
def unitRefutationCodeOf (q : Query) (fuel : Nat) : Option (List Int) :=
  (unitRefutation (formulaOf q) fuel).map (fun p => proofCode (prune p))

/-! ### (c) Decided example 1: the proved-sound emitter, on a real model -/

/-- The secrecy reading of `Regressions.Authentication`: the query of `ProtSat.AuthGap`. -/
abbrev qs : Query := AuthGap.qs

set_option maxRecDepth 20000 in
/-- **The kernel decides that the emitter emits.** One round of saturation - in fact zero: the
seed alone - reaches the empty clause for this query, so `refutationCodeOf qs 0` is not `none`.
About half a second of kernel time, and no solver: the engine's output is a list of lines, not a
search. -/
theorem qs_emitted : emitted qs 0 = true := by decide

/-- **Safety from the proved-sound engine, with no solver.** The code itself is not written down
here: it is 5836 integers, because `uptoEmpty` keeps every line before the empty clause and the
empty clause is the last clause of the formula. What the theorem needs is only that the emitter
emitted something, and `refute_sound` does the rest. Read this together with
`AuthGap.why_the_formula_is_unsat`: the model declares no secret, so the violation clause is the
empty disjunction and the refutation is one line. The certificate is genuine and the safety is
genuine; the *formula* is degenerate. `qg` below is the non-degenerate case. -/
theorem qs_boundedSafe : boundedSafeGoals qs := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa [emitted] using qs_emitted)
  exact boundedSafe_of_emittedCode 0 AuthGap.qs_goals AuthGap.qs_ne AuthGap.hU AuthGap.hsec
    AuthGap.gapFree hc

/-- The analyser's answer for that query, derived from the same emitted code. -/
theorem qs_verdict_from_code : analyzeQuery qs = Result.encodingUnsat := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa [emitted] using qs_emitted)
  exact analyzeQuery_encodingUnsat_of_emittedCode 0 AuthGap.qs_wellFormed AuthGap.qs_ne
    AuthGap.qs_goals AuthGap.hU hc

/-! ### (c) Decided example 2: a real certificate for the guarded protocol -/

/-- The guarded query of `ProtSat.EndToEnd`: 246 variables, 291 clauses, no empty clause, and the
secret is reachable in principle - the same role with the secret published is `EndToEnd.Leak`,
which the pipeline calls an attack. -/
abbrev qg : Query := EndToEnd.qg

/-- The fuel the unit-propagation producer is given. Ten rounds suffice; twelve is what the demo
runs. -/
def qgFuel : Nat := 12

/-- **The certificate.** The 138 integers below are a serialized resolution refutation of `encode
EndToEnd.Guard EndToEnd.GB`: 21 lines, 10 of them original clauses of the formula and 11
resolvents, 33 literal occurrences in total. They are the output of `unitRefutationCodeOf qg
qgFuel` - the demo program re-runs the producer and prints whether it reproduces them - and the
kernel accepts them as written, without running any search. -/
def qgCode : List Int := [
  0, 61, 0, 0, -69, 137, 0, 0, 63, 0,
  0, -137, 138, 0, 0, 66, 0, 0, -138, 139,
  0, 0, 68, 0, 0, -72, -139, 0, 0, 223,
  0, 0, -32, 0, 0, 242, 0, 0, 69, 0,
  0, 268, 0, 0, -47, 32, 0, 0, 284, 0,
  0, -210, 72, 0, 0, 289, 0, 0, -37, 32,
  210, 47, 0, 0, 290, 0, 0, 32, 37, 0,
  1, 6, 4, 31, -47, 0, 1, 8, 4, 31,
  -37, 210, 47, 0, 1, 9, 4, 31, 37, 0,
  1, 5, 0, 68, 137, 0, 1, 11, 10, 46,
  -37, 210, 0, 1, 13, 1, 136, 138, 0, 1,
  15, 2, 137, 139, 0, 1, 16, 3, 138, -72,
  0, 1, 7, 17, 71, -210, 0, 1, 14, 18,
  209, -37, 0, 1, 12, 19, 36, 0
]

/-- The decode fuel: one unit per line of the refutation, plus one. -/
def qgCheckFuel : Nat := 22

set_option maxRecDepth 20000 in
/-- **The kernel checks the certificate.** This is the whole trust story of the module: about 0.3
s of kernel time, against the minutes `EndToEnd.lean` measures for replaying DPLL on a formula of
this size. Nothing here re-runs a solver. -/
theorem qg_checked : checkCode (formulaOf qg) qgCheckFuel qgCode = true := by decide

/-- The certificate's size, as the kernel computes it from the code. -/
theorem qg_size : codeLines qgCheckFuel qgCode = 21 ∧ codeLiterals qgCheckFuel qgCode = 33 ∧
    codeOrigins qgCheckFuel qgCode = 10 := by decide

/-- **`boundedSafeGoals` from the certificate.** No solver, no search, no trust in the producer:
the chain is decode, check 21 resolution steps, and `CheckedSafe.boundedSafe_of_checkedCode`. -/
theorem qg_boundedSafe : boundedSafeGoals qg :=
  boundedSafe_of_code EndToEnd.qg_goals EndToEnd.qg_ne EndToEnd.qg_hU EndToEnd.qg_hsec
    EndToEnd.qg_gap qgCode ⟨qgCheckFuel, qg_checked⟩

/-- **The analyser's answer from the certificate.** `EndToEnd.qg_verdict` proves the same equation
by deciding `DPLL.dpll (encode Guard GB) = none`; this proof never mentions the solver. -/
theorem qg_verdict_from_code : analyzeQuery qg = Result.encodingUnsat :=
  analyzeQuery_encodingUnsat_of_code EndToEnd.qg_wf EndToEnd.qg_ne EndToEnd.qg_goals EndToEnd.qg_hU
    qg_checked

/-- **The agreement the task asks for.** The verdict the analyser gives and the certificate the
checker accepts are the same fact: the answer is `encodingUnsat` and the query is bounded safe,
and both are read off the 138 integers above. -/
theorem qg_verdict_and_certificate_agrees :
    analyzeQuery qg = Result.encodingUnsat ∧ boundedSafeGoals qg :=
  ⟨qg_verdict_from_code, qg_boundedSafe⟩

/-- The verdict with its evidence attached, in the contract's own vocabulary. -/
theorem qg_result_is_security :
    securityResult (Result.boundedSafe ⟨qg, qg_boundedSafe⟩) = true := rfl

/-- The public reading of the certificate: no permitted execution of the guarded protocol at one
event leaks the declared key, and the reason is a checked refutation rather than a solver's
silence. -/
theorem qg_noLeak_from_code :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg),
        BoundedTrace EndToEnd.Guard EndToEnd.GB tr Cs ∧ runsLeaks EndToEnd.Guard Cs := by
  intro h
  obtain ⟨tr, Cs, hbt, hleak⟩ := h
  exact qg_boundedSafe ⟨Goal.secrecy, by decide, tr, Cs, hbt,
    by rw [violation_secrecy]; exact hleak⟩

/-! ### The certificate is evidence about *this* formula -/

set_option maxRecDepth 20000 in
/-- Evidence is bound to the formula it refutes. `EndToEnd.Leak` is the same shape and the same
bounds with one action changed - the session publishes the key instead of an agent name - and its
CNF is satisfiable. The certificate above is rejected against it, so the 138 integers cannot be
replayed against a different model. -/
theorem qg_rejects_other_formula :
    checkCode (encode EndToEnd.Leak EndToEnd.GB) qgCheckFuel qgCode = false := by decide

/-- Too little decode fuel and the code does not decode, so there is no verdict: the checker
declines rather than guessing. Twenty-one units of fuel are enough for twenty-one lines; twenty
are not. -/
theorem qg_rejects_no_fuel : checkCode (formulaOf qg) 20 qgCode = false := by decide

/-- A truncated code - the final terminator erased - is rejected, and so is a code with its first
integer dropped: a certificate is only as good as the bytes it came in. -/
theorem qg_rejects_truncated : checkCode (formulaOf qg) qgCheckFuel (qgCode.dropLast) = false := by
  decide

/-- And the producer reproduces the artifact embedded above. This equality is checked by the demo
program at run time, not by the kernel: making the kernel check it would mean making the kernel
run the search, which is the one thing the certificate exists to avoid. -/
def qg_producer_reproduces : Bool := unitRefutationCodeOf qg qgFuel = some qgCode

end ProtSat.AnalyzerEvidence
