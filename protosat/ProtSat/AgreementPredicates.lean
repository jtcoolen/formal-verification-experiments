/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Query
import ProtSat.Regressions
import ProtSat.Reference
import ProtSat.Explore
import ProtSat.Contract

/-!
# ProtSat/AgreementPredicates.lean - the two agreement predicates, related exactly

## What this file does

The repository has two definitions of "this trace breaks non-injective agreement", and the same
`Goal.agreement` constructor names both of them:

* `ProtSat.AuthBreak` (`ProtSat/Operational.lean:461`): a committed `(tag, peer, value)` triple
  that occurs nowhere among the claimed triples. **Unordered**, and it compares only the triple - the
  actor and the position are not in `ProtSat.AuthInst` at all. `ProtSat.Query.Violation
  P Goal.agreement` is this one, so it is the target the CNF route is measured against.
* `ProtSat.Reference.authBreak` (`ProtSat/Reference.lean:565): `¬ agrees (insts P Cs tr)`, where
  `Reference.claimMatches` (`ProtSat/Reference.lean:532`) requires the same tag, the same data,
  the claimer to be the principal the committer believes it talked to, the committer to be the
  principal the claimer believes it talked to, and a **strictly earlier** position. **Ordered** and
  role-crossed. `ProtSat.Reference.Contract.goalViolation P Goal.agreement` is this one.

### 1. The exact logical relationship

The two predicates are not even typeable at one argument: `AuthBreak` reads
`ProtSat.Cfg`/`ProtSat.Ev` and `Reference.authBreak` reads `ProtSat.Reference.Cfg` /
`ProtSat.Reference.Ev` - two different transition systems, and no lemma in the repository turns a
run of one into a run of the other. So the relationship is stated where it can be stated: on the
*extracted event lists*, in the richer vocabulary `Reference.Inst`, which contains every field
either monitor reads. There:

* `AuthBreak` is *definitionally* the unordered monitor on the old extraction
  (`authBreak_eq_unorderedBreakAI`), and the unordered monitor on the new extraction transfers to it
  along the projection that keeps `(isCommit, tag, peer, data)` (`authBreak_of_extraction_eq`).
  That projection is the whole connection: it drops `sess`, `role`, `self` and `idx`.
* **The conjectured implication `Reference.authBreak -> AuthBreak` is FALSE**, and not for a subtle
  reason: the ordered monitor demands a claim *by the peer the commit names*, in the opposite
  direction, and the unordered monitor demands only a claim whose own peer field matches - so a commit
  excused by a later claim, or by a claim from the wrong principal, is an ordered violation with no
  unordered violation at all (`ordered_not_le_unordered`, decided on
  `Regressions.Semantics.futureClaimP`). The converse fails too: on the repository's own honest pair
  `Reference.Gates.pairP` the unordered monitor reports a violation the ordered monitor refuses
  (`unordered_not_le_ordered`). The two readings are **incomparable**, not nested.
* What *is* true is a conditional: on a run whose commits are addressed to the principal that performs
  them (`c.self = c.peer`) the ordered monitor is the stricter one
  (`unorderedAgrees_of_agrees_of_selfEqPeer`), and each counterexample violates exactly that
  hypothesis, so it is not decoration.
* The difference is not a matter of proof effort. Two event lists whose `AuthBreak`-visible records
  are **literally equal** - same commit triple, same claim triple, same order - are accepted by the
  ordered monitor and rejected by it (`authBreak_carries_too_little`). No predicate computed from
  `ProtSat.AuthInst` can express the ordering requirement, whatever it is.

### 2-3. The separation, decided, and the consequence

Section 4 gives three kernel-decided separations; section 5 turns the third into the finding:

* On `selfAddrP` - one session, claim then commit, both addressed to a peer that is not itself -
  the unordered monitor is silent on **every** execution the reference explorer enumerates (43 nodes,
  exhausted by the kernel) while the ordered monitor fires on one of them. A contract whose agreement
  target is `Query.Violation` therefore reports no attack on a protocol the repaired contract
  attacks: `selfAddr_unorderedBoundedSafe` against `selfAddr_orderedBoundedAttack`.
* The mirror-image failure is proved too: on the repository's honest two-party run
  `Reference.Gates.pairP` the unordered monitor reports a violation that the ordered monitor
  correctly refuses (`ordered_not_le_unordered`). The unordered reading is not merely weaker, it is
  wrong in both directions.
* "Is the Lowe attack invisible to the unordered predicate?" - **no, and that is not the defect.** The
  repository's NS model declares no authentication events at all (`NS_has_no_auth_events`), so both
  monitors are vacuous on it (`both_agrees_of_no_commits`). The blindness has to be witnessed on a
  model that actually claims and commits, which is what `selfAddrP` and `futureClaimP` are.

### 4. The `agreementInj` question

`Query.Violation P Goal.agreementInj _ _ = True` (`ProtSat/Query.lean:129`) makes
`boundedAttackGoals` hold for *every* query that selects it, whatever the protocol and whatever the
bounds: the empty trace is always a bounded trace (`empty_boundedTrace`). So
`not_boundedSafeGoals_of_agreementInj` - the predicate is trivially true and trivially reachable at
the level of the definition. It is **unreachable as a verdict**: `goalEncoded Goal.agreementInj =
false` gates `analyzeQuery` before the solver is consulted (`agreementInj_ne_securityResult`),
and it is *not* the validator that saves it - a well-formed query selecting it is exhibited and
decided (`injQ_wellFormed`, `injQ_refused`). Meanwhile the two contracts disagree about the same goal:
the trivial one fires on a run the real injective monitor accepts
(`agreementInj_predicates_differ`, `agreementInj_constant_agrees_with_nothing`).

### 5. Recommendation

Section 7 states the recommendation and the blast radius, counted by `grep` at `cf1d60a`. Nothing
here changes `Query.lean`, `Operational.lean` or `Contract.lean`.

## What this file does NOT do

* It does not connect the two transition systems, and it does not claim the two predicates can be
  compared at one `(P, Cs, tr)`: they cannot, because `Cfg` and `Ev` differ. Every cross-semantics
  statement below is either about the extracted event lists or is a pair of separately proved
  statements about the same `Protocol` in the two systems.
* It does not change any definition. `Query.Violation` stays unordered, `Goal` keeps three
  constructors, and no existing theorem is restated with a weaker statement.
* It does not prove anything about the CNF. `AuthClauses.Matching` is mentioned only to say which of
  its two selectors pairs with which predicate; the clause-level consequences belong to
  `ProtSat/GoalEncode.lean`, whose header already records the mismatch.
* It does not decide `ProtSat.Bounded.BoundedAttack` or `ProtSat.boundedAttackGoals` for any model:
  those quantify over `ProtSat` executions and that semantics has no enumerator. Every universal
  statement is over `ProtSat.Reference.Explore`'s enumeration, and each such theorem names the gap in
  its comment.
* It is not imported by `ProtSat.lean`, because adding that line would mean editing an existing file.
  `lake build` still elaborates it (the library glob is `ProtSat.+`), but the axiom audit and the
  theorem inventory in `scripts/ci.sh` walk the environment reachable from `import ProtSat`, so the
  75 theorems here join those two gates only once `import ProtSat.AgreementPredicates` is added to
  `ProtSat.lean`.
-/

namespace ProtSat.AgreementPredicates

open ProtSat Term Protocol Bounded Certificate Query
open Protocol

/-! ### 1. The unordered monitor, stated in the richer vocabulary -/

/-- The whole of what `ProtSat.AuthBreak` compares: the `(tag, peer, value)` triple an authentication
event records. Everything the old predicate can see is here; everything it cannot see - who performed
the event and where in the trace it happened - is dropped. -/
def instTriple (a : Reference.Inst) : Tag × Agent × Term := (a.tag, a.peer, a.data)

/-- The committed triples of a list of authentication events, in trace order: what
`ProtSat.commitsOf` computes, restated on `Reference.Inst`. -/
def commitTriples (ls : List Reference.Inst) : List (Tag × Agent × Term) :=
  ls.filterMap fun a => if a.isCommit then some (instTriple a) else none

/-- The claimed triples of a list of authentication events: what `ProtSat.claimsOf` computes,
restated on `Reference.Inst`. -/
def claimTriples (ls : List Reference.Inst) : List (Tag × Agent × Term) :=
  ls.filterMap fun a => if a.isCommit then none else some (instTriple a)

/-- **The unordered, triple-only agreement reading**, stated on `Reference.Inst`: every commit's
`(tag, peer, value)` triple is claimed somewhere in the list, by anyone, at any time. This is the
property `ProtSat.AuthBreak` denies, lifted into the vocabulary the ordered monitor uses. -/
def unorderedAgrees (ls : List Reference.Inst) : Prop :=
  ∀ c ∈ ls, c.isCommit → ∃ r ∈ ls, !r.isCommit ∧ instTriple r = instTriple c

/-- Some commit's triple is claimed nowhere: the reading of section 1 fails. -/
def unorderedBreak (ls : List Reference.Inst) : Prop := ¬ unorderedAgrees ls

/-- **The unordered violation in `AuthBreak`'s own shape**: a committed triple that is not among the
claimed triples. -/
def unorderedBreakT (ls : List Reference.Inst) : Prop :=
  ∃ c ∈ commitTriples ls, c ∉ claimTriples ls

/-- The executable unordered monitor: `true` exactly when the unordered reading holds. -/
def unorderedAgreesBool (ls : List Reference.Inst) : Bool :=
  ls.all fun c => !c.isCommit || ls.any fun r => !r.isCommit && instTriple r == instTriple c

/-- The executable unordered monitor is correct: the test is decided by the kernel, not trusted. -/
theorem unorderedAgreesBool_iff (ls : List Reference.Inst) :
    unorderedAgreesBool ls = true <-> unorderedAgrees ls := by
  classical
  rw [unorderedAgreesBool, unorderedAgrees, List.all_eq_true]
  constructor
  · intro hall c hc hcom
    rcases Bool.or_eq_true_iff.mp (hall c hc) with h | h
    · exact absurd hcom (by simpa using h)
    · obtain ⟨r, hr, hm⟩ := List.any_eq_true.mp h
      exact ⟨r, hr, by simpa using hm⟩
  · intro hall c hc
    refine Bool.or_eq_true_iff.mpr ?_
    by_cases hcom : c.isCommit
    · right
      obtain ⟨r, hr, hnc, heq⟩ := hall c hc hcom
      exact List.any_eq_true.mpr ⟨r, hr, by simp [hnc, heq]⟩
    · left
      simpa using hcom

/-- The executable unordered monitor fails exactly when the reading fails. -/
theorem unorderedBreak_iff_bool (ls : List Reference.Inst) :
    unorderedBreak ls <-> unorderedAgreesBool ls = false := by
  classical
  rw [unorderedBreak, Bool.eq_false_iff]
  exact (Iff.not (unorderedAgreesBool_iff ls)).symm

/-- The `AuthBreak`-shaped failure really is a failure of the unordered reading. Only this direction
is needed, and it is the one that does not need excluded middle over a list search. -/
theorem unorderedBreak_of_unorderedBreakT (ls : List Reference.Inst)
    (hb : unorderedBreakT ls) : unorderedBreak ls := by
  obtain ⟨c, hc, hn⟩ := hb
  rw [commitTriples, List.mem_filterMap] at hc
  obtain ⟨c', hc', hif⟩ := hc
  by_cases hcom : c'.isCommit
  · have htrip : instTriple c' = c := by simpa [hcom] using hif
    intro hall
    obtain ⟨r, hr, hnc, heq⟩ := hall c' hc' (by simpa using hcom)
    have hmem : c ∈ claimTriples ls := by
      rw [claimTriples, List.mem_filterMap]
      refine ⟨r, hr, ?_⟩
      have hfalse : r.isCommit = false := by simpa using hnc
      simp [hfalse, heq, htrip]
    exact hn hmem
  · exact absurd hif (by simp [hcom])

/-! ### 2. What `AuthBreak` actually is, and the exact connection between the two extractions -/

/-- The triple an `Operational` authentication event records: the same three fields, from the record
type that has nothing else. -/
def aiTriple (a : AuthInst) : Tag × Agent × Term := (a.tag, a.peer, a.val)

/-- The committed triples of a list of old-semantics authentication events. -/
def aiCommits (ls : List AuthInst) : List (Tag × Agent × Term) :=
  ls.filterMap fun a => if a.isCommit then some (aiTriple a) else none

/-- The claimed triples of a list of old-semantics authentication events. -/
def aiClaims (ls : List AuthInst) : List (Tag × Agent × Term) :=
  ls.filterMap fun a => if a.isCommit then none else some (aiTriple a)

/-- The projection from a repaired-semantics event to the old record type. What is kept is exactly
what `AuthBreak` compares; what is dropped - `sess`, `role`, `self`, `idx` - is exactly what
`Reference.claimMatches` needs. -/
def toAuthInst (a : Reference.Inst) : AuthInst :=
  { isCommit := a.isCommit, tag := a.tag, peer := a.peer, val := a.data }

/-- The committed triples `ProtSat.commitsOf` computes are exactly this projection of the old
extraction - definitionally. -/
theorem commitsOf_eq (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    commitsOf P Cs tr = aiCommits (authInsts P Cs tr) := rfl

/-- The claimed triples `ProtSat.claimsOf` computes are exactly this projection of the old
extraction - definitionally. -/
theorem claimsOf_eq (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    claimsOf P Cs tr = aiClaims (authInsts P Cs tr) := rfl

/-- **`AuthBreak` is the unordered monitor on the old extraction**, definitionally: the predicate
`Query.Violation P Goal.agreement` unfolds to "some committed triple is not among the claimed
triples" and to nothing else. This is what makes the rest of the file about `AuthBreak` rather than
about a look-alike. -/
theorem authBreak_eq_unorderedBreakAI (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    AuthBreak P Cs tr <->
      ∃ c ∈ aiCommits (authInsts P Cs tr), c ∉ aiClaims (authInsts P Cs tr) :=
  Iff.rfl

/-- Hence `AuthBreak` is a predicate on the extracted event list alone: two runs whose `authInsts`
agree have the same `AuthBreak` verdict, whatever else their configurations differ in. -/
theorem authBreak_congruent {P : Protocol} {Cs Cs' : List Cfg} {tr tr' : List Ev}
    (h : authInsts P Cs tr = authInsts P Cs' tr') :
    AuthBreak P Cs tr <-> AuthBreak P Cs' tr' := by
  have hc : commitsOf P Cs tr = commitsOf P Cs' tr' := by
    rw [commitsOf_eq, commitsOf_eq, h]
  have hl : claimsOf P Cs tr = claimsOf P Cs' tr' := by
    rw [claimsOf_eq, claimsOf_eq, h]
  simp [AuthBreak, hc, hl]

/-- Projecting the repaired extraction and taking the committed triples are the same operation. -/
theorem commitTriples_eq_aiCommits_map (ls : List Reference.Inst) :
    commitTriples ls = aiCommits (toAuthInst <$> ls) := by
  unfold commitTriples aiCommits toAuthInst instTriple aiTriple
  induction ls with
  | nil => rfl
  | cons a as ih =>
      simp only [List.filterMap_cons, ih]
      by_cases h : a.isCommit <;> simp [h]

/-- Projecting the repaired extraction and taking the claimed triples are the same operation. -/
theorem claimTriples_eq_aiClaims_map (ls : List Reference.Inst) :
    claimTriples ls = aiClaims (toAuthInst <$> ls) := by
  unfold claimTriples aiClaims toAuthInst instTriple aiTriple
  induction ls with
  | nil => rfl
  | cons a as ih =>
      simp only [List.filterMap_cons, ih]
      by_cases h : a.isCommit <;> simp [h]

/-- **The precise connection the task asked for.** The two repository predicates are the same formula
applied to two different extractions, and they coincide exactly when those extractions coincide after
dropping the four fields `AuthBreak` cannot see. Given such a run-pair, an unordered break of the
repaired extraction is an `AuthBreak` of the old run. The hypothesis is not a formality: it is what
the repository does not have, and section 3 shows it cannot hold in general. -/
theorem authBreak_of_extraction_eq {P : Protocol} {Cs tr Cs' tr'}
    (h : authInsts P Cs tr = toAuthInst <$> Reference.insts P Cs' tr')
    (hb : unorderedBreakT (Reference.insts P Cs' tr')) : AuthBreak P Cs tr := by
  refine (authBreak_eq_unorderedBreakAI P Cs tr).mpr ?_
  rw [h, ← commitTriples_eq_aiCommits_map, ← claimTriples_eq_aiClaims_map]
  exact hb

/-- The old-semantics executable test agrees with `AuthBreak`; recorded here so the witnesses below
do not silently depend on a monitor nobody checked. -/
theorem authBreakBool_iff' (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    authBreakBool P Cs tr = true <-> AuthBreak P Cs tr := authBreakBool_iff P Cs tr

/-! ### 3. What the ordered monitor reads that the unordered one cannot -/

/-- The six things `Reference.claimMatches` demands, unpacked. The unordered monitor can see only the
first three: it has no notion of who claimed, of the direction, or of when. -/
theorem claimMatches_imp {c r : Reference.Inst} (h : Reference.claimMatches c r = true) :
    r.isCommit = false ∧ r.tag = c.tag ∧ r.data = c.data ∧ r.self = c.peer ∧ r.peer = c.self ∧
      r.idx < c.idx := by
  classical
  simp only [Reference.claimMatches, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    beq_iff_eq] at h
  tauto

/-- A claim that matches a commit in the ordered sense excuses it in the unordered sense **if the
commit is addressed to the principal that performs it**. Outside that hypothesis the two readings share
no direction of implication at all. -/
theorem unorderedExcuse_of_claimMatches {c r : Reference.Inst} (hself : c.self = c.peer)
    (hm : Reference.claimMatches c r = true) :
    !r.isCommit ∧ instTriple r = instTriple c := by
  obtain ⟨hnc, htag, hdata, _, hpeer, _⟩ := claimMatches_imp hm
  have hp : r.peer = c.peer := hpeer.trans hself
  exact ⟨by simpa using hnc, by simp [instTriple, htag, hdata, hp]⟩

/-- **The corrected form of the conjectured implication.** On a run whose commits are all addressed to
the principal that performs them, ordered agreement implies unordered agreement: on such runs the
ordered monitor finds every attack the unordered one does, and possibly more. The hypothesis is doing
real work - `ordered_not_le_unordered` violates exactly it. -/
theorem unorderedAgrees_of_agrees_of_selfEqPeer {ls : List Reference.Inst}
    (h : ∀ c ∈ ls, c.isCommit → c.self = c.peer) (hall : Reference.agrees ls) :
    unorderedAgrees ls := by
  intro c hc hcom
  obtain ⟨r, hr, hm⟩ := hall c hc hcom
  obtain ⟨hnc, heq⟩ := unorderedExcuse_of_claimMatches (h c hc hcom) hm
  exact ⟨r, hr, hnc, heq⟩

/-- The contrapositive, in the direction the task conjectured: on a self-addressed run, an
`AuthBreak`-shaped violation *is* an `Reference.authBreak`. -/
theorem unorderedBreak_of_agrees_of_selfEqPeer {ls : List Reference.Inst}
    (h : ∀ c ∈ ls, c.isCommit → c.self = c.peer) :
    unorderedBreak ls -> ¬ Reference.agrees ls :=
  fun hb hall => hb (unorderedAgrees_of_agrees_of_selfEqPeer h hall)

/-- **The unordered reading depends only on which events happened.** Reordering the event list cannot
change its verdict - the formal content of "unordered". -/
theorem unorderedAgrees_perm {ls ls' : List Reference.Inst} (h : List.Perm ls ls') :
    unorderedAgrees ls <-> unorderedAgrees ls' := by
  classical
  unfold unorderedAgrees
  refine ⟨fun hall c hc hcom => ?_, fun hall c hc hcom => ?_⟩
  · obtain ⟨r, hr, hnc, heq⟩ := hall c (h.mem_iff.mpr hc) hcom
    exact ⟨r, h.mem_iff.mp hr, hnc, heq⟩
  · obtain ⟨r, hr, hnc, heq⟩ := hall c (h.mem_iff.mp hc) hcom
    exact ⟨r, h.mem_iff.mpr hr, hnc, heq⟩

/-- The unordered *monitor* is permutation-invariant as a computation, not only as a proposition. -/
theorem unorderedAgreesBool_perm {ls ls' : List Reference.Inst} (h : List.Perm ls ls') :
    unorderedAgreesBool ls = unorderedAgreesBool ls' := by
  classical
  have key : unorderedAgreesBool ls = true <-> unorderedAgreesBool ls' = true :=
    ((unorderedAgreesBool_iff ls).trans (unorderedAgrees_perm h)).trans
      ((unorderedAgreesBool_iff ls').symm)
  cases a : unorderedAgreesBool ls <;> cases b : unorderedAgreesBool ls' <;> simp_all

/-- **The ordered reading is not permutation-invariant on traces.** The witness is the repository's own
honest pair run in both orders - `Reference.Gates.pair_agrees` against
`Reference.Gates.later_claim_does_not_excuse`. The two traces are permutations of each other and the
ordered verdicts are opposite. -/
theorem agrees_not_trace_perm_invariant :
    ∃ (P : Protocol) (tr tr' : List Reference.Ev), List.Perm tr tr' ∧
      (¬ Reference.authBreak P (Reference.Gates.visit P tr) tr) ∧
        Reference.authBreak P (Reference.Gates.visit P tr') tr' :=
  ⟨Reference.Gates.pairP, [Reference.Ev.act 0, Reference.Ev.act 1],
    [Reference.Ev.act 1, Reference.Ev.act 0],
    List.Perm.swap _ _ _,
    Reference.Gates.pair_no_break,
    Reference.Gates.later_claim_does_not_excuse⟩

/-- The same commit triple and the same claim triple, with the claim **before** the commit. -/
def lsEarly : List Reference.Inst :=
  [ { isCommit := true, sess := 1, role := 1, self := 1, peer := 0, tag := 0,
      data := Term.nonce 5, idx := 1 },
    { isCommit := false, sess := 0, role := 0, self := 0, peer := 1, tag := 0,
      data := Term.nonce 5, idx := 0 } ]

/-- The same two records in the same list positions, with the claim **after** the commit: the
`AuthBreak`-visible projection is unchanged. -/
def lsLate : List Reference.Inst :=
  [ { isCommit := true, sess := 1, role := 1, self := 1, peer := 0, tag := 0,
      data := Term.nonce 5, idx := 0 },
    { isCommit := false, sess := 0, role := 0, self := 0, peer := 1, tag := 0,
      data := Term.nonce 5, idx := 1 } ]

/-- The projection `AuthBreak` can see cannot tell the two runs apart. -/
theorem toAuthInst_lsEarly_eq_toAuthInst_lsLate :
    toAuthInst <$> lsEarly = toAuthInst <$> lsLate := by decide

/-- The ordered monitor accepts the early claim. -/
theorem agrees_lsEarly : Reference.agrees lsEarly :=
  (Reference.agreesBool_iff _).mp (by decide : Reference.agreesBool lsEarly = true)

/-- The ordered monitor rejects the late claim, and nothing else changed. -/
theorem not_agrees_lsLate : ¬ Reference.agrees lsLate := fun hall => by
  have hne : Reference.agreesBool lsLate ≠ true := by decide
  exact hne ((Reference.agreesBool_iff _).mpr hall)

/-- **The inexpressibility result.** The gap is not a missing proof. Two event lists whose
`AuthBreak`-visible records are *literally equal* - same commit triple, same claim triple, same
order - are accepted by the ordered monitor and rejected by it, because the fields that decide the
question (`self`, and `idx` relative to the commit) are not in the projection at all. Any predicate
computed from `ProtSat.AuthInst` is blind to the ordering requirement, whatever it is. -/
theorem authBreak_carries_too_little :
    ∃ ls ls' : List Reference.Inst,
      (toAuthInst <$> ls) = (toAuthInst <$> ls') ∧
        Reference.agrees ls ∧ ¬ Reference.agrees ls' :=
  ⟨lsEarly, lsLate, toAuthInst_lsEarly_eq_toAuthInst_lsLate, agrees_lsEarly,
    not_agrees_lsLate⟩

/-- A run with no commits satisfies both readings, for the same reason: there is nothing to match. This
is the vacuity class the repository's NS model belongs to. -/
theorem both_agrees_of_no_commits {ls : List Reference.Inst}
    (h : ∀ c ∈ ls, c.isCommit = false) :
    unorderedAgrees ls ∧ Reference.agrees ls :=
  ⟨fun c hc hcom => absurd hcom (by simpa using h c hc),
    fun c hc hcom => absurd hcom (by simpa using h c hc)⟩

/-! ### 4. The separation, decided

**Kernel cost of every decision in this and the next section**, measured with `lake env lean` on this
file alone (Apple M-series, Mathlib v4.34.1, HEAD `cf1d60a`). The file contains 47 `decide` tactics and
elaborates in 2.4 s wall-clock in total, of which about 1.9 s is importing Mathlib and the ProtSat
modules it reads. With `set_option profiler true` the two slowest individual tactic replays in the
file are **155 ms** and **137 ms**; the heaviest single gate, `selfAddr_node_count`, costs about 0.6 s
and the 43-node enumeration gate `selfAddr_unorderedAttackFound_false` about 0.15 s. Nothing here is
close to the 60 s reporting threshold, and nothing bypasses the kernel.
-/

/-- The old-semantics run of `Regressions.Semantics.futureClaimP`: the commit first, the matching
claim second. This is the repository's own `later_claim_excuses_commit` witness. -/
def fcOldCs : List Cfg :=
  certCfgs (Examples.certOfTrace Regressions.Semantics.futureClaimP Regressions.Semantics.futureClaimTrace)

/-- The old-semantics trace of `futureClaimP`: two `Ev.act` events. -/
def fcOldTr : List Ev := Regressions.Semantics.futureClaimTrace

/-- The repaired-semantics trace of the *same protocol*: the same two actions, in the same order. The
event type is different (`Reference.Ev.act q` carries no message and no nonce) but the protocol, the
sessions and the annotations are the same object. -/
def fcNewTr : List Reference.Ev := [Reference.Ev.act 0, Reference.Ev.act 0]

/-- The configurations the repaired run visits. -/
def fcNewCs : List Reference.Cfg := Reference.Gates.visit Regressions.Semantics.futureClaimP fcNewTr

/-- The old run really is a run of the old semantics: the certificate checker accepts it. -/
theorem fc_old_runs :
    Runs Regressions.Semantics.futureClaimP (initCfg Regressions.Semantics.futureClaimP)
      fcOldTr fcOldCs :=
  checkSteps_runs Regressions.Semantics.futureClaimP
    (Examples.certOfTrace Regressions.Semantics.futureClaimP Regressions.Semantics.futureClaimTrace).steps
    (initCfg Regressions.Semantics.futureClaimP)
    (by decide : checkSteps Regressions.Semantics.futureClaimP
      (initCfg Regressions.Semantics.futureClaimP)
      (Examples.certOfTrace Regressions.Semantics.futureClaimP
        Regressions.Semantics.futureClaimTrace).steps = true)

/-- Non-vacuity: the old run really does record a commit, so `AuthBreak` is not silent because
nothing happened. -/
theorem fc_old_commits :
    commitsOf Regressions.Semantics.futureClaimP fcOldCs fcOldTr = [(0, 1, Term.agent 0)] :=
  by decide

/-- Non-vacuity: and it really does record the claim, one step later. -/
theorem fc_old_claims :
    claimsOf Regressions.Semantics.futureClaimP fcOldCs fcOldTr = [(0, 1, Term.agent 0)] :=
  by decide

/-- **Half one of the separation, on the real `AuthBreak`:** the unordered predicate does not fire
on this run - the commit's triple is claimed, just later. This is the repository's
`Regressions.Semantics.later_claim_excuses_commit`, read back through the proved monitor. -/
theorem fc_old_not_AuthBreak : ¬ AuthBreak Regressions.Semantics.futureClaimP fcOldCs fcOldTr := by
  intro h
  have h2 : authBreakBool Regressions.Semantics.futureClaimP fcOldCs fcOldTr = true :=
    (authBreakBool_iff _ _ _).mpr h
  have h3 : authBreakBool Regressions.Semantics.futureClaimP fcOldCs fcOldTr = false := by
    rw [fcOldCs, fcOldTr]
    exact Regressions.Semantics.later_claim_excuses_commit
  rw [h3] at h2
  exact absurd h2 (by simp)

/-- The repaired run really is a run of the repaired semantics. -/
theorem fc_new_run_eq :
    Reference.run Regressions.Semantics.futureClaimP
      (Reference.initCfg Regressions.Semantics.futureClaimP) fcNewTr = some fcNewCs := by decide

/-- The repaired run really is a run of the repaired semantics. -/
theorem fc_new_runs :
    Reference.Runs Regressions.Semantics.futureClaimP
      (Reference.initCfg Regressions.Semantics.futureClaimP) fcNewTr fcNewCs := fc_new_run_eq

/-- The repaired extraction: the same two events, with the two extra fields `self` and `idx` that
`AuthBreak` has no room for. -/
theorem fc_new_insts :
    Reference.insts Regressions.Semantics.futureClaimP fcNewCs fcNewTr =
      [ { isCommit := true, sess := 0, role := 0, self := 0, peer := 1, tag := 0,
          data := Term.agent 0, idx := 0 },
        { isCommit := false, sess := 0, role := 0, self := 0, peer := 1, tag := 0,
          data := Term.agent 0, idx := 1 } ] := by decide

/-- **Half two of the separation:** the ordered monitor fires on the same protocol and the same order
of events. -/
theorem fc_new_ordered_break :
    Reference.authBreak Regressions.Semantics.futureClaimP fcNewCs fcNewTr := fun hall => by
  have hne : Reference.agreesBool (Reference.insts Regressions.Semantics.futureClaimP fcNewCs
      fcNewTr) ≠ true := by decide
  exact hne ((Reference.agreesBool_iff _).mpr hall)

/-- And the unordered reading of the repaired extraction is silent, so the two monitors really do
disagree on one event list and not merely on two semantics. -/
theorem fc_new_unordered_silent :
    unorderedAgrees (Reference.insts Regressions.Semantics.futureClaimP fcNewCs fcNewTr) :=
  (unorderedAgreesBool_iff _).mp (by decide)

/-- **The extractions do coincide here**, after dropping the four fields `AuthBreak` cannot see:
`futureClaimP` is a case where the transfer lemma of section 2 applies. -/
theorem fc_extraction_agrees :
    authInsts Regressions.Semantics.futureClaimP fcOldCs fcOldTr =
      toAuthInst <$> Reference.insts Regressions.Semantics.futureClaimP fcNewCs fcNewTr :=
  by decide

/-- **`ordered_not_le_unordered`.** The conjectured implication fails: an ordered agreement
violation with no unordered violation at all, on a run of a protocol already in the repository. The
reason is visible in `fc_new_insts`: the commit is addressed to agent 1 and performed by agent 0,
so the ordered monitor demands a claim *by agent 1*, which the unordered monitor never asks for - it
only asks for a claim whose own peer field says 1, which the later claim by agent 0 supplies. -/
theorem ordered_not_le_unordered :
    ∃ (P : Protocol) (Cs : List Reference.Cfg) (tr : List Reference.Ev),
      Reference.authBreak P Cs tr ∧ unorderedAgrees (Reference.insts P Cs tr) :=
  ⟨Regressions.Semantics.futureClaimP, fcNewCs, fcNewTr, fc_new_ordered_break,
    fc_new_unordered_silent⟩

/-- The honest two-party run of the repository's own pair model: session 0 (playing agent 0) claims to
have started a run with agent 1, and session 1 (playing agent 1) commits to having completed one with
agent 0. -/
def pairTr : List Reference.Ev := [Reference.Ev.act 0, Reference.Ev.act 1]

/-- The configurations that run visits. -/
def pairCs : List Reference.Cfg := Reference.Gates.visit Reference.Gates.pairP pairTr

/-- The extraction of the honest run: two events, addressed in opposite directions. -/
theorem pair_insts :
    Reference.insts Reference.Gates.pairP pairCs pairTr =
      [ { isCommit := false, sess := 0, role := 0, self := 0, peer := 1, tag := 0,
          data := Term.nonce 5, idx := 0 },
        { isCommit := true, sess := 1, role := 1, self := 1, peer := 0, tag := 0,
          data := Term.nonce 5, idx := 1 } ] := by decide

/-- The ordered monitor accepts the honest run - this is `Reference.Gates.pair_no_break`. -/
theorem pair_ordered_silent : ¬ Reference.authBreak Reference.Gates.pairP pairCs pairTr :=
  Reference.Gates.pair_no_break

/-- **The mirror-image failure:** the unordered monitor reports a violation on the honest run. It
looks for a claim whose *peer field* equals the commit's peer field - agent 0 - and the only claim in
the run names agent 1, because a claim names the principal the claimer is talking to, not the
principal it is answering. -/
theorem pair_unordered_fires : unorderedBreak (Reference.insts Reference.Gates.pairP pairCs pairTr) :=
  (unorderedBreak_iff_bool _).mpr (by decide : unorderedAgreesBool
    (Reference.insts Reference.Gates.pairP pairCs pairTr) = false)

/-- **`unordered_not_le_ordered`.** The converse implication fails too, and on the repository's own
honest model: an unordered violation with no ordered violation. Note that the commit here has
`self ≠ peer`, exactly the hypothesis `unorderedAgrees_of_agrees_of_selfEqPeer` needs. -/
theorem unordered_not_le_ordered :
    ∃ (P : Protocol) (Cs : List Reference.Cfg) (tr : List Reference.Ev),
      unorderedBreak (Reference.insts P Cs tr) ∧ ¬ Reference.authBreak P Cs tr :=
  ⟨Reference.Gates.pairP, pairCs, pairTr, pair_unordered_fires, pair_ordered_silent⟩

/-- The two monitors also disagree on the *reordered* honest trace, where both fire: recorded so the
claim "they are incomparable" is not read as "they never coincide". -/
theorem pair_swapped_both_fire :
    unorderedBreak (Reference.insts Reference.Gates.pairP
        (Reference.Gates.visit Reference.Gates.pairP [Reference.Ev.act 1, Reference.Ev.act 0])
        [Reference.Ev.act 1, Reference.Ev.act 0]) ∧
      Reference.authBreak Reference.Gates.pairP
        (Reference.Gates.visit Reference.Gates.pairP [Reference.Ev.act 1, Reference.Ev.act 0])
        [Reference.Ev.act 1, Reference.Ev.act 0] :=
  ⟨(unorderedBreak_iff_bool _).mpr (by decide), Reference.Gates.later_claim_does_not_excuse⟩

/-! ### 5. The consequence: what a CNF-route SAFE for an agreement query would mean -/

/-- **The agreement question the CNF route asks, restated over the repaired transition system with the
unordered monitor.** This is the exact shape of `ProtSat.boundedAttackGoals (Query.mk P B
[Goal.agreement])` - "some permitted execution has a commit triple that is claimed nowhere" - with
`ProtSat.Operational`'s transition system replaced by the repaired one, because that is the only
transition system in the repository with an exhaustive enumerator. The swap is the gap this file is
about, and it is named in every theorem that depends on it. -/
def unorderedBoundedAttack (P : Protocol) (B : Bounds) : Prop :=
  ∃ tr Cs, Reference.Explore.BoundedRun P B tr Cs ∧ unorderedBreak (Reference.insts P Cs tr)

/-- No permitted execution violates the unordered reading: what a `boundedSafeGoals` answer for an
agreement query would mean if the enumeration above were the semantics of the query. -/
def unorderedBoundedSafe (P : Protocol) (B : Bounds) : Prop := ¬ unorderedBoundedAttack P B

/-- The executable form of `unorderedBoundedAttack` over the reference enumeration. -/
def unorderedAttackFound (P : Protocol) (B : Bounds) : Bool :=
  (Reference.Explore.allNodes P B B.steps).any fun x =>
    ! unorderedAgreesBool (Reference.insts P x.Cs x.tr)

/-- A positive answer of the executable question is a genuine attack: the enumeration is sound. -/
theorem unorderedBoundedAttack_of_unorderedAttackFound {P : Protocol} {B : Bounds}
    (h : unorderedAttackFound P B = true) : unorderedBoundedAttack P B := by
  classical
  rw [unorderedAttackFound, List.any_eq_true] at h
  obtain ⟨x, hx, hv⟩ := h
  rw [Reference.Explore.allNodes, List.mem_flatMap] at hx
  obtain ⟨k, hk, hmem⟩ := hx
  obtain ⟨hpre, hlen⟩ := Reference.Explore.isPrefix_of_mem_frontier
    (Reference.Explore.isPrefix_initNode P B) hmem
  have hv' : unorderedAgreesBool (Reference.insts P x.Cs x.tr) = false := by simpa using hv
  refine ⟨x.tr, x.Cs, ⟨hpre.1, ?_, hpre.2.1⟩, (unorderedBreak_iff_bool _).mpr hv'⟩
  rw [hlen]
  simp only [Reference.Explore.initNode, List.length_nil, Nat.zero_add]
  exact Nat.le_of_lt_succ (List.mem_range.mp hk)

/-- And complete: a genuine bounded attack appears in the enumeration. This is the direction the safety
conclusion needs, and it is the same `frontier_complete` argument the reference explorer uses. -/
theorem unorderedAttackFound_of_unorderedBoundedAttack {P : Protocol} {B : Bounds}
    (h : unorderedBoundedAttack P B) : unorderedAttackFound P B = true := by
  classical
  obtain ⟨tr, Cs, ⟨hrun, hlen, hb⟩, hv⟩ := h
  have hvb : unorderedAgreesBool (Reference.insts P Cs tr) = false :=
    (unorderedBreak_iff_bool _).mp hv
  obtain ⟨l, hCs⟩ := Reference.Explore.run_nonempty hrun
  subst hCs
  obtain ⟨y, hy, h1, h2, _⟩ :=
    Reference.Explore.frontier_complete (Reference.Explore.isPrefix_initNode P B)
      (by unfold Reference.Runs; exact hrun)
      (fun C hC => hb C (List.Mem.tail _ hC))
  simp [Reference.Explore.initNode] at h1 h2
  rw [unorderedAttackFound, List.any_eq_true]
  refine ⟨y, ?_, ?_⟩
  · rw [Reference.Explore.allNodes, List.mem_flatMap]
    exact ⟨tr.length, List.mem_range.mpr (by omega), h1 ▸ hy⟩
  · rw [h2, h1]
    simp [hvb]

/-- So the executable question decides the semantic one. -/
theorem unorderedAttackFound_iff {P : Protocol} {B : Bounds} :
    unorderedAttackFound P B = true <-> unorderedBoundedAttack P B :=
  ⟨unorderedBoundedAttack_of_unorderedAttackFound, unorderedAttackFound_of_unorderedBoundedAttack⟩

/-- **Bounded safety by exhaustion** for the unordered reading. -/
theorem unorderedBoundedSafe_of_unorderedAttackFound_false {P : Protocol} {B : Bounds}
    (h : unorderedAttackFound P B = false) : unorderedBoundedSafe P B := by
  intro ⟨tr, Cs, hrun, hv⟩
  exact absurd (unorderedAttackFound_of_unorderedBoundedAttack ⟨tr, Cs, hrun, hv⟩)
    (by simpa using h)

/-- **The ordering witness.** One session, played by agent 1, talking to agent 0: it claims to have
started a run with agent 0 and then commits to having completed one with agent 0, on the same tag and
the same data. Every field the unordered monitor compares is present and equal; the only thing wrong is
that the claim was not made by agent 0. This is `Contract.Gates.authOrderP` with `self` changed
from 0 to 1 and agent 1 added to the domain - two fields of model data, and the two readings of
`Goal.agreement` come apart. -/
def selfAddrP : Protocol :=
  { roles := [{ acts := [Action.claim 0 (Expr.agent 0) (Expr.nonce 5),
                         Action.commit 0 (Expr.agent 0) (Expr.nonce 5)] }]
    sessions := [{ role := 0, self := 1, peer := 0 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [{ tag := 0 }] }

/-- Two events suffice to reach both authentication actions. -/
def selfAddrB : Bounds := { steps := 2, rounds := 0 }

/-- The honest-looking execution: claim, then commit. -/
def selfAddrTr : List Reference.Ev := [Reference.Ev.act 0, Reference.Ev.act 0]

/-- The configurations it visits. -/
def selfAddrCs : List Reference.Cfg := Reference.Gates.visit selfAddrP selfAddrTr

/-- It is a run. -/
theorem selfAddr_run_eq :
    Reference.run selfAddrP (Reference.initCfg selfAddrP) selfAddrTr = some selfAddrCs := by decide

/-- The claim-then-commit execution is a run of the repaired semantics. -/
theorem selfAddr_runs :
    Reference.Runs selfAddrP (Reference.initCfg selfAddrP) selfAddrTr selfAddrCs :=
  selfAddr_run_eq

/-- It reaches a commit, so the agreement question is not vacuous. -/
theorem selfAddr_reaches_commit :
    ((Reference.insts selfAddrP selfAddrCs selfAddrTr).any fun i => i.isCommit) = true := by decide

/-- The commit is addressed to agent 0 and performed by agent 1, so the self-addressing hypothesis of
section 3 fails on this very run - which is why the two monitors can disagree here. -/
theorem selfAddr_commit_not_self_addressed :
    ∃ c ∈ Reference.insts selfAddrP selfAddrCs selfAddrTr, c.isCommit ∧ c.self ≠ c.peer :=
  by decide

/-- On the completed run the unordered monitor is silent: the commit's triple is claimed, by the wrong
principal. -/
theorem selfAddr_unordered_silent :
    unorderedAgrees (Reference.insts selfAddrP selfAddrCs selfAddrTr) :=
  (unorderedAgreesBool_iff _).mp (by decide)

/-- On the completed run the ordered monitor fires: agent 0 never claimed anything. -/
theorem selfAddr_ordered_break : Reference.authBreak selfAddrP selfAddrCs selfAddrTr :=
  fun hall => by
    have hne : Reference.agreesBool (Reference.insts selfAddrP selfAddrCs selfAddrTr) ≠ true :=
      by decide
    exact hne ((Reference.agreesBool_iff _).mpr hall)

/-- The enumeration is small: 43 nodes, so the universal statement below is a kernel computation and
not a metaphor. -/
theorem selfAddr_node_count :
    (Reference.Explore.allNodes selfAddrP selfAddrB selfAddrB.steps).length = 43 := by decide

/-- **The unordered monitor is silent on every permitted execution of `selfAddrP`.** Not just on the
one run above: on all 43 enumerated nodes, including every prefix and every idle-padded variant. The
reason is structural and is worth stating plainly - the commit is the *second* action of the only
session, so no execution reaches a commit without having already performed the claim that excuses it
under the triple-only reading. -/
theorem selfAddr_unorderedAttackFound_false :
    unorderedAttackFound selfAddrP selfAddrB = false := by decide

/-- **Therefore the CNF-route agreement target reports no attack on `selfAddrP`.** -/
theorem selfAddr_unorderedBoundedSafe : unorderedBoundedSafe selfAddrP selfAddrB :=
  unorderedBoundedSafe_of_unorderedAttackFound_false selfAddr_unorderedAttackFound_false

/-- **While the repaired contract reports an attack on it**: the violating execution is a bounded
execution of the same model under the same bounds. -/
theorem selfAddr_orderedBoundedAttack :
    Reference.Explore.BoundedAttack selfAddrP selfAddrB :=
  ⟨selfAddrTr, selfAddrCs,
    ⟨selfAddr_runs, by decide, fun C hC => by
      have hall : (selfAddrCs.all (Reference.Explore.inBoundsBool selfAddrP selfAddrB)) = true :=
        by decide
      rw [List.all_eq_true] at hall
      exact (Reference.Explore.inBoundsBool_iff).mp (hall C hC)⟩,
    Or.inr selfAddr_ordered_break⟩

/-- **The finding, in one line.** The same model, the same bounds, one enumeration: the agreement
semantics the CNF route is measured against sees no attack, and the agreement semantics the deciding
contract computes sees one. A `boundedSafeGoals` answer for a `Goal.agreement` query therefore
does not mean "no commit went unmatched"; it means "no commit triple went unclaimed", and those are
different propositions on a protocol this repository can write down in eight lines. -/
theorem cnf_route_agreement_target_is_blind :
    unorderedBoundedSafe selfAddrP selfAddrB ∧ Reference.Explore.BoundedAttack selfAddrP selfAddrB :=
  ⟨selfAddr_unorderedBoundedSafe, selfAddr_orderedBoundedAttack⟩

/-- The mirror image, restated as a contract fact: on the honest pair the unordered reading reports an
attack that the ordered reading refuses. A CNF route measured against `AuthBreak` can therefore also
answer *attack* on a run where the repaired contract answers safe - the mismatch is not a one-sided
loss of precision. -/
theorem cnf_route_agreement_target_overreports :
    unorderedBreak (Reference.insts Reference.Gates.pairP pairCs pairTr) ∧
      ¬ Reference.authBreak Reference.Gates.pairP pairCs pairTr :=
  ⟨pair_unordered_fires, pair_ordered_silent⟩

/-- What each route's agreement predicate *is*, pinned down for the record: the CNF route's target is
the unordered triple test and the deciding contract's is the ordered role-crossed test. Both are
definitional, which is exactly why nobody noticed. -/
theorem violation_agreement_is_AuthBreak (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    Violation P Goal.agreement Cs tr <-> AuthBreak P Cs tr := violation_agreement P Cs tr

/-- And the deciding contract's agreement goal is the ordered monitor, on the repaired semantics. -/
theorem goalViolation_agreement_is_authBreak (P : Protocol)
    (Cs : List Reference.Cfg) (tr : List Reference.Ev) :
    ProtSat.Reference.Contract.goalViolation P Goal.agreement Cs tr <->
      Reference.authBreak P Cs tr :=
  ProtSat.Reference.Contract.goalViolation_agreement P Cs tr

/-! **5c. The Lowe question.** *Is the Lowe attack invisible to the unordered predicate?* Not as the
question is usually assumed: the repository's Needham-Schroeder model declares no authentication event
at all, so **both** monitors are vacuous on it and neither can witness anything. That is a stronger
failure than the one asked about - the model cannot express the property in either reading - and it is
decided here rather than asserted. -/

/-- The NS model's instantiated sessions perform no claim and no commit: the model-level check the
validator performs, decided. -/
theorem NS_has_no_auth_events : authEvents Examples.NS.P = [] := by decide

/-- The same fact for the trace the review advertised an agreement break on, in the old semantics: this
is `Regressions.Semantics.NS_has_no_auth_events`. -/
theorem NS_no_auth_events_old :
    authInsts Examples.NS.P
      (certCfgs (Examples.certOfTrace Examples.NS.P Examples.NS.trace)) Examples.NS.trace = [] :=
  Regressions.Semantics.NS_has_no_auth_events

/-- So the unordered predicate cannot fire on the NS run: there is no commit to be unclaimed. -/
theorem NS_unordered_vacuous :
    ¬ AuthBreak Examples.NS.P
      (certCfgs (Examples.certOfTrace Examples.NS.P Examples.NS.trace)) Examples.NS.trace := fun h => by
  have h2 : authBreakBool Examples.NS.P
      (certCfgs (Examples.certOfTrace Examples.NS.P Examples.NS.trace)) Examples.NS.trace = true :=
    (authBreakBool_iff _ _ _).mpr h
  rw [Regressions.Semantics.NS_auth_not_broken] at h2
  exact absurd h2 (by decide)

/-- And the ordered monitor is vacuous on any run of a model whose extraction is empty, which is the
shape the NS model has: the two predicates agree here only because neither has anything to say. -/
theorem both_vacuous_of_insts_nil (P : Protocol) (Cs : List Reference.Cfg) (tr : List Reference.Ev)
    (h : Reference.insts P Cs tr = []) :
    ¬ Reference.authBreak P Cs tr ∧ unorderedAgrees (Reference.insts P Cs tr) :=
  ⟨fun hall => hall (by intro c hc hcom; rw [h] at hc; exact absurd hc (by simp)),
    by intro c hc hcom; rw [h] at hc; exact absurd hc (by simp)⟩

/-! ### 6. The `Goal.agreementInj` question: a trivially true violation predicate, and why no verdict
reaches it -/

/-- Every execution violates `Goal.agreementInj` under the CNF-route semantics. This is the
definition `Query.Violation P Goal.agreementInj _ _ = True` read out; it is stated here because the
consequences below are the point, not the definition. -/
theorem violation_agreementInj_is_true (P : Protocol) :
    ∀ (Cs : List Cfg) (tr : List Ev), Violation P Goal.agreementInj Cs tr :=
  violation_agreementInj P

/-- The empty execution is always a bounded execution: no protocol, no bounds and no universe
condition can exclude it. -/
theorem cfgInUniverse_initCfg (P : Protocol) (B : Bounds) :
    cfgInUniverse (initCfg P) (univ P B) = true := by
  classical
  unfold cfgInUniverse
  rw [initCfg]
  simp
  exact initKn_subset_univ P B

/-- The empty trace is a bounded trace of every protocol under every bound. -/
theorem empty_boundedTrace (P : Protocol) (B : Bounds) : BoundedTrace P B [] [initCfg P] :=
  ⟨Runs.nil P (initCfg P), by simp, fun C hC => by
    simp only [List.mem_singleton] at hC
    subst hC
    exact cfgInUniverse_initCfg P B⟩

/-- **Every query that selects `Goal.agreementInj` has a bounded attack**, whatever its protocol and
whatever its bounds: the empty execution violates the goal, because the goal's violation predicate is
`True`. This is not a labelling problem and not a conservative approximation of the answer - it is
the answer, computed from the definition, for every model in the repository. -/
theorem boundedAttackGoals_of_agreementInj {q : Query} (h : Goal.agreementInj ∈ q.goals) :
    boundedAttackGoals q :=
  ⟨Goal.agreementInj, h, [], [initCfg q.protocol], empty_boundedTrace q.protocol q.bounds,
    trivial⟩

/-- So no query that selects `Goal.agreementInj` can ever be `boundedSafeGoals` - not even a
protocol with no sessions at all. -/
theorem not_boundedSafeGoals_of_agreementInj {q : Query} (h : Goal.agreementInj ∈ q.goals) :
    ¬ boundedSafeGoals q :=
  fun hall => hall (boundedAttackGoals_of_agreementInj h)

/-- In particular the two-goal query `[secrecy, agreementInj]` is an attack for every protocol,
which is the shape a caller would most plausibly write when asking for injective agreement alongside
secrecy. -/
theorem boundedAttackGoals_secrecy_agreementInj (P : Protocol) (B : Bounds) :
    boundedAttackGoals (Query.mk P B [Goal.secrecy, Goal.agreementInj]) :=
  boundedAttackGoals_of_agreementInj (by simp)

/-- **Is it reachable?** Not through the analyser. Any query selecting an unencoded goal gets no
security verdict at all, and `Goal.agreementInj` is not encoded, so `analyzeQuery` answers
`unsupportedGoals` or `invalidModel` or `noGoals` and never `attack`, never
`boundedSafe`, never even `encodingUnsat`. This is the gate that keeps the trivial predicate from
becoming a wrong answer, and it is a gate on the *encoding*, not on the semantics. -/
theorem agreementInj_ne_securityResult {q : Query} (h : Goal.agreementInj ∈ q.goals) :
    securityResult (analyzeQuery q) = false :=
  analyzeQuery_not_security_of_unencoded ⟨Goal.agreementInj, h, by decide⟩

/-- Nor does it reach the unsatisfiability answer. -/
theorem agreementInj_ne_encodingUnsat {q : Query} (h : Goal.agreementInj ∈ q.goals) :
    analyzeQuery q ≠ Result.encodingUnsat := by
  intro heq
  have hsel : ∃ g ∈ q.goals, ! goalEncoded g := ⟨Goal.agreementInj, h, by decide⟩
  by_cases hval : (validate q).isEmpty
  · have hg : ¬ q.goals.isEmpty := by
      intro hz
      generalize hq : q.goals = gl at h hz
      cases gl with
      | nil => cases h
      | cons _ _ => exact absurd hz (by simp)
    rw [analyzeQuery_unsupported_of_unencoded hval hg hsel] at heq
    cases heq
  · rw [analyzeQuery_invalidModel_of_diagnostics hval] at heq
    cases heq

/-- **The validator is not what stops it.** A query selecting `Goal.agreementInj` over a model that
really does commit and claim passes validation cleanly, so the refusal is entirely due to
`goalEncoded`: if a fourth `Goal` were added to `encodedGoals` without giving
`Query.Violation` a real semantics for it, the trivial predicate would reach the verdict immediately.
-/
def injQ : Query :=
  Query.mk ProtSat.Reference.Contract.Gates.authSwappedP
    ProtSat.Reference.Contract.Gates.authOrderB [Goal.agreementInj]

/-- That query is well-formed: the validator produces no diagnostic. -/
theorem injQ_wellFormed : (validate injQ).isEmpty = true := by decide

/-- It has goals. -/
theorem injQ_hasGoals : ¬ injQ.goals.isEmpty := by decide

/-- And the analyser refuses it, naming the goal. -/
theorem injQ_refused : analyzeQuery injQ = Result.unsupportedGoals [Goal.agreementInj] := by
  rw [analyzeQuery_unsupported_of_unencoded injQ_wellFormed injQ_hasGoals
    ⟨Goal.agreementInj, by simp [injQ], by decide⟩]
  rw [show unsupported injQ = [Goal.agreementInj] from by decide]

/-- The refusal is not a security verdict. -/
theorem injQ_ne_security : securityResult (analyzeQuery injQ) = false :=
  agreementInj_ne_securityResult (by simp [injQ])

/-- **And the two contracts disagree about the same goal, in the direction that matters.** The
deciding contract has a real injective monitor, and it accepts the honest replay-free run; the CNF
route's `Violation` accepts nothing, because it accepts everything. -/
theorem agreementInj_predicates_differ :
    (∀ (Cs : List Cfg) (tr : List Ev), Violation Reference.Gates.pairP Goal.agreementInj Cs tr) ∧
      ProtSat.Reference.Contract.goalViolationBool Reference.Gates.pairP Goal.agreementInj
          pairCs pairTr = false :=
  ⟨violation_agreementInj_is_true _, by decide⟩

/-- So `Violation P Goal.agreementInj` is not a conservative stand-in for injective agreement: it is
a constant. On the replay model of `ProtSat.Reference.Gates` the real monitor fires and the constant
fires too, and on the honest model the real monitor is silent while the constant still fires - the two
have no relationship at all beyond both being propositions. -/
theorem agreementInj_constant_agrees_with_nothing :
    ProtSat.Reference.Contract.goalViolationBool Reference.Gates.replayP Goal.agreementInj
        (Reference.Gates.visit Reference.Gates.replayP Reference.Gates.replayTrace)
        Reference.Gates.replayTrace = true ∧
      ProtSat.Reference.Contract.goalViolationBool Reference.Gates.pairP Goal.agreementInj
          pairCs pairTr = false ∧
      (∀ (Cs : List Cfg) (tr : List Ev),
          Violation Reference.Gates.pairP Goal.agreementInj Cs tr) :=
  ⟨by decide, by decide, violation_agreementInj_is_true _⟩

/-! ### 7. Recommendation, and the blast radius

**Recommendation: rename, do not retarget.** `Query.Violation P Goal.agreement` should stay
`ProtSat.AuthBreak` and be renamed `Goal.agreementUnordered`; a fourth constructor
`Goal.agreementOrdered` should be added whose violation is the ordered, role-crossed test, and
`Goal.agreement` should be made an abbreviation for the ordered one only once the CNF route can
represent it. The reasons, each of which is a theorem above:

* Retargeting `Goal.agreement` to the ordered predicate does not make the CNF route *stricter*, it
  makes it *incomparable*: `unordered_not_le_ordered` shows the unordered predicate reports
  violations the ordered monitor refuses, on the repository's own honest pair. A retarget would
  therefore invalidate the existing agreement soundness theorem
  (`GoalEncode.boundedAttackGoals_of_sat_agreement`, stated for
  `AuthClauses.Matching.tripleOnly` precisely because `Query.Violation` is the unordered test) and
  would not by itself make the `Matching.orderAware` default sound - the two selectors of
  `AuthClauses` already exist, so the clause side is ready and the semantic side is not.
* The ordered predicate cannot be stated over `ProtSat.Operational` at all: `AuthInst` has no
  `self` and no `idx` (`authBreak_carries_too_little`), so a retarget is not a one-line change to
  `Query.lean` - it requires either the repaired extraction or new fields on the old one, and the old
  one is what eight thousand lines of correspondence are proved against.
* Parameterising `Violation` on the monitor (a `Matching`-like index) is the honest long-term shape
  and the cheapest to state, but it changes the type of a definition that appears in the statement of
  every goal-indexed theorem in `GoalEncode.lean`.
* Independently of the rename: `Query.Violation P Goal.agreementInj` should stop being `True`. The
  repaired semantics already has `Reference.agreesInj`, `Reference.agreesInjBool` and a proved
  monitor equivalence, and `Contract.goalViolation` already uses them - so the constant is not holding
  a place for missing work, it is a live over-claim in the only goal-indexed semantics the CNF route
  reads. `boundedAttackGoals_of_agreementInj` is the reason: as long as it stays `True`, *every* query
  that selects injective agreement is an attack, which makes `boundedSafeGoals|boundedAttackGoals`
  unusable as a specification for that goal and leaves `goalEncoded` as the only thing between the
  constant and a verdict.

**Blast radius**, counted with `grep -rn` over `ProtSat/*.lean` and `*.lean` at HEAD `cf1d60a`
(the counts are occurrences of the token, in all positions including doc comments, so they bound the
edit rather than equal it):

| token | occurrences | files |
|---|---|---|
| `AuthBreak` (the old predicate) | 33 | 10 |
| `Goal.agreement`, not counting `Goal.agreementInj` | 119 | 10 |
| `Goal.agreementInj` | 21 | 3 |
| `authBreak` (the repaired monitor, incl. `authBreakBool`) | 46 | 13 |
| `Violation` | 101 | 8 |
| `goalEncoded` | 67 | 9 |
| `boundedSafeGoals` | 68 | 11 |
| `encodedGoals` | 15 | 5 |

The ten files that mention `AuthBreak` are `AuthClauses.lean`, `AuthGap.lean`, `Bounded.lean`,
`Certificate.lean`, `GoalEncode.lean`, `Operational.lean`, `Query.lean`, `Reference.lean`,
`Regressions.lean` and `Sound.lean`. Of those, the ones whose
*proofs* - not just their comments - depend on the unordered reading are
`Certificate.lean` (`authBreakBool_iff`), `Bounded.lean` (`BoundedAttack`),
`Query.lean` (`Violation`, `violation_agreement`,
`boundedAttackGoals_iff_BoundedAttack`), `GoalEncode.lean` (the agreement soundness direction and
its `tripleOnly` pairing) and `AuthGap.lean`/`Regressions.lean` (the witnesses). A rename of
`Goal.agreement` alone touches 119 sites in 10 files; adding a fourth constructor touches
`Query.encodedGoals`, `Query.validate` (which keys the authentication vacuity check off
`Goal.agreement ∈ q.goals || Goal.agreementInj ∈ q.goals`), `GoalEncode.encodeGoals`,
`AuthClauses.agreementEncode` and every gate in `Contract.Gates` and `GoalEncode.Diff`.

**What this file asks nobody to change today:** the defect is a naming collision over two semantics, and
the fix that does not disturb eight thousand lines is to stop calling both things `agreement`.
-/

end ProtSat.AgreementPredicates
