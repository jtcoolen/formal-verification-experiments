/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import ProtSat.Complete
import ProtSat.DPLL
import ProtSat.Query
import ProtSat.Regressions
import ProtSat.Reference
import ProtSat.Contract
import ProtSat.AuthGap

/-!
# ProtSat/AuthClauses.lean - agreement in the CNF (prototype, roadmap stage 4)

## What this file is

`ProtSat.Encode.violationLits` (ProtSat/Clauses.lean:679) is built only from `closedLeakLits` and
`storeLeakLits`, so the generated formula demands a **secrecy** violation and nothing else.
`ProtSat.AuthGap` proves the consequence: the same protocol and bounds are reported safe by the CNF
route (`safe_for_secrecy2`) while an agreement attack is permitted by the reference semantics
(`attacked_for_agreement2`), and `goal_hypothesis_is_needed` proves the goal hypothesis cannot be
dropped. This file is the prototype that closes that gap: it adds the agreement violation demand to
the formula, as clauses, without touching a single existing line.

## What was built

* `authPositions P` - the claim and commit annotations the model itself declares: every session,
  every program counter whose action is `Action.claim` or `Action.commit`, with its tag, its peer
  expression and its data expression. **This is the claim/commit specification, and it is data.**
  It is not a proof hypothesis and not an extra argument the caller has to get right: it is read out
  of the same `Protocol` record the reference monitor reads (`ProtSat.Reference.insts`), so the CNF
  and the monitor are asked about the same events by construction. The design choice the task asked
  about: no new specification object was invented, because `Protocol` already carries one.
* `authOccs sh P commit` - the *named occurrences* of those events: one per position, per step,
  with the value numbers its peer and data expressions denote. A position is enumerated only when
  its annotations are closed constants naming universe messages (`authNameable`); see "the
  restriction" below.
* `authOccLits` - the four literals that say "this occurrence happens": the session acts, its
  program counter is the position's, and the two annotation expressions evaluate to the two values.
* `authViolationLits` - the demand: **some commit occurrence happens**.
* `authExcuseClauses m` - for every commit occurrence `c` and every claim occurrence `k` that could
  excuse it, the clause "not both `c` is the violation and `k` happens". With `m := orderAware` the
  excuse relation is `ProtSat.Reference.claimMatches` (same tag, same data, strictly earlier, the
  claimer is the principal the committer believes it talked to and vice versa); with
  `m := tripleOnly` it is the older, unordered, triple-only membership test of `ProtSat.AuthBreak`.
  Both are provided because the two monitors the project uses disagree, and the difference is a
  property of the clauses rather than of a proof.
* `agreementEncode P B m` - `baseEncode P B` (the ten semantic groups, unchanged) conjoined with the
  agreement demand. `authEncode P B m` - `encode P B` conjoined with it, exactly as the task asked.

## The obstruction found, and why it is the interesting result

`authEncode P B := encode P B ++ <new clauses>` **cannot work on the AuthGap model**, and the reason
is not the new clauses: it is the old ones. `Authentication.P` declares no secret, so
`violationLits` is the empty list and `encode P B` contains the empty clause
(`AuthGap.empty_clause_in_encode`). A conjunction with an unsatisfiable formula is unsatisfiable, so
the agreement clauses could never be satisfied no matter how good they are. `authEncode_empty_clause`
and `authEncode_not_sat` state this for the model the task named. The fix is not to weaken the
secrecy clause but to make the violation group **goal-indexed**: the formula must demand the
violation of the goal the query selected, not always secrecy. That is what `encodeGoals` below
prototypes, and it is the first item of the integration list at the end of this header.

## The restriction, stated honestly

The prototype enumerates only authentication positions whose peer and data expressions are *closed
constants* (`Expr.constVal` names them) whose values the universe contains. The hypothesis
`authNameable (shapeOf P B) P` says that is every position of the model. It is a condition on the
model and the bounds - decidable, and satisfied by every agreement model in this repository
(`Authentication.P`, `AuthGap.P2`, `Contract.Gates.authOrderP`/`authSwappedP`) - and it is what
lets a single pair of value literals name an authentication event. Dropping it means the data of a
claim is whatever a store slot happens to hold, so the occurrence cannot be pinned to a fixed value
index: the clauses must keep the `vxe` group literal for the data and let the solver choose it, and
the excuse clauses must then be generated for *every* value index rather than one. That is a bigger
formula, not a different idea; the machinery is already in `authOccLits`, which keeps all four
literals whether or not they are pinned.

## What is NOT proved in this run

No direction of the correspondence is proved here, and the reason is structural rather than a matter
of effort: every decoding lemma of `ProtSat.Encoding` (`agrees_decRun`, `decRun_trace`,
`decodePc_of_true`, `kn_sound`) takes its hypothesis as `Sat a (encode P B)` - the *whole*
formula, secrecy violation clause included. A satisfying assignment of the agreement-only encoding
does not provide one, and on the AuthGap model none exists. So:

* **SOUND** (a model of the agreement encoding decodes to a run whose agreement monitor fails) needs
  either the goal-indexed `encode` of item 1 below, or the group-level re-statement of the
  `Encoding` decoding lemmas. The pieces that are missing and are not deep: the two trace-index
  lemmas (`(decEvsFrom P B a n).get i = decEv \u27e8...\u27e9 (steps - n + i)` and its twin for
  `decCfgsFrom`), a lemma recovering `decCode P B a i = 1 + q` from the decoded event being
  `Ev.act q m d`, and the observation that under `authNameable` the annotations of a claim are
  closed constants, so `xe_konst` plus `decXe_some_vxe` turn "the decoded run has a claim of
  triple t" into "all four literals of that claim occurrence are true" - which is what the excuse
  clause contradicts.
* **COMPLETE** (a permitted agreement attack yields a model) is the direction that makes a UNSAT
  verdict mean safety, and it is the cheaper one to state: the `Complete` group lemmas are already
  phrased per group over `RunOK`, so what is missing is `RunOK`-driven lemmas that the
  `assignOf` assignment makes the selector auxiliary true exactly when the run has that commit,
  plus the two trace-index lemmas above.
* What *is* proved instead is the pair of kernel-decided gates: an explicit verified model of the
  agreement encoding on the AuthGap attack model (`gate_agreement_attack_found`), and an explicit
  kernel refutation of the agreement encoding on a model where agreement holds (`gate_order_unsat`,
  via the subformula `orderCore`), each cross-checked against the reference enumeration in the
  `Diff` namespace.

## What is still needed to make this the DEFAULT encoding

1. **Goal-indexed `violationLits`.** Replace `Encode.violationLits sh P` by
   `Encode.violationLits sh P gs`, where `gs : List Goal` is the query's selected goals, with
   `violationLits sh P [secrecy]` reducing definitionally to today's list and
   `violationLits sh P []` reducing to `[]` (no demand clause at all, rather than an empty one).
   `encodeGoals` below is the prototype of that step and proves the equation that makes the
   regression gate hold: `encodeGoals P B [secrecy] = encode P B`.
2. **The `Complete`/`Encoding` re-indexing.** `Complete.sat_violation` and
   `Encoding.violationLits_cases`/`violation_leak` are stated for the secrecy literals only. Each
   needs a twin for the agreement literals (`authViolationLits_cases`, `violation_authBreak`), and
   `Encoding.encoding_sound` needs to return the goal it found a violation of rather than `Or.inl`.
3. **The honest-execution hypothesis.** The soundness direction needs the decoded run to be a run of
   the semantics the monitor is defined over. For `orderAware` that is `ProtSat.Reference.Rel`, which
   differs from `ProtSat.Rel` in freshness history, credential provisioning and the blocking of
   malformed annotations; the bridge is a hypothesis on today's models ("the decoded run is also a
   reference run") and a theorem once the reference semantics replaces the old one.
4. **Variable allocation.** The new auxiliaries live above `Encode.nVarsAll sh`. Making the encoding
   default means moving `bsAuth` into `Clauses` next to `bsAu`/`szPb` so that
   `Complete.assignOf` knows the block, and extending `Complete.WithinBounds` with the condition
   that makes an authentication occurrence nameable (`authNameable`).
5. **The contract socket.** `Query.encodedGoals` is `[Goal.secrecy]`; it grows to
   `[secrecy, agreement]` when (1) lands, and `Query.analyzeQuery` stops refusing agreement
   queries. Until then this file is additive and nothing that imports it changes its answer.
-/

namespace ProtSat.AuthClauses

open ProtSat Term Protocol OneHot Bounded Attacker Encode Encoding Complete Query DPLL
open Protocol

/-! ### The claim/commit specification: read out of the model -/

/-- One claim or commit annotation of the model: the session that performs it, the program counter
it sits at, the tag it carries, and the two expressions it evaluates - the peer it believes it was
talking to and the data it agrees on. This is the claim/commit specification of the encoding, and it
is data: it is read out of the same `Protocol` record the reference monitor reads. -/
structure AuthPos where
  /-- `true` for a commit, `false` for a claim (the same convention as `Reference.Inst.isCommit`). -/
  isCommit : Bool
  /-- The session performing the event. -/
  sess : Nat
  /-- The program counter the action sits at. -/
  pc : Nat
  /-- The tag the event carries. -/
  tag : Tag
  /-- The expression naming the peer the session believes it talked to. -/
  peer : Expr
  /-- The expression naming the agreed data. -/
  val : Expr
  deriving Repr, DecidableEq

/-- Every claim and commit position of the instantiated model. Sessions beyond the session list and
program counters beyond a role's length have no action, so they contribute nothing. -/
def authPositions (P : Protocol) : List AuthPos :=
  (List.range P.sessions.length).flatMap fun q =>
    (List.range (P.roleLen q)).flatMap fun c =>
      match P.actionAt q c with
      | some (Action.claim tag peer v) =>
          [{ isCommit := false, sess := q, pc := c, tag := tag, peer := peer, val := v }]
      | some (Action.commit tag peer v) =>
          [{ isCommit := true, sess := q, pc := c, tag := tag, peer := peer, val := v }]
      | _ => []

/-- Which principal session `q` plays, if there is such a session. -/
def sessSelf (P : Protocol) (q : Nat) : Option Agent := (rget P.sessions q).map fun s => s.self

/-- The principal named by value number `u`, if the universe message there is an agent name. -/
def agentAt (sh : Shape) (u : Nat) : Option Agent :=
  (rget sh.U u).bind fun t => match t with
    | Term.agent a => some a
    | _ => none

/-! ### How a commit is excused -/

/-- The two agreement monitors the project uses.

* `orderAware` mirrors `ProtSat.Reference.claimMatches`: a commit is excused by a **strictly
  earlier** claim of the same tag and data, made by the principal the committer believes it talked
  to, addressed to the committer. This is the monitor `Reference.Contract.goalViolationBool` uses,
  so it is the specification the CNF is measured against.
* `tripleOnly` mirrors the older `ProtSat.AuthBreak`: a commit is excused by any claim of the same
  (tag, peer, value) triple, wherever in the trace it happens. `ProtSat.AuthGap` is stated in this
  vocabulary, which is why both are here. -/
inductive Matching where
  | orderAware : Matching
  | tripleOnly : Matching
  deriving Repr, DecidableEq

/-! ### Named occurrences of authentication events -/

/-- One occurrence of an authentication event: the position, the step it happens at, and the value
numbers of the peer and the data it records. -/
structure AuthOcc where
  pos : AuthPos
  step : Nat
  data : Nat
  peerVal : Nat
  deriving Repr, DecidableEq

/-- The value numbers a position's annotations denote, or none when the prototype cannot name them:
the peer must be a closed agent constant, the data a closed constant, and both must be messages the
universe contains. -/
def authOccIdx (sh : Shape) (p : AuthPos) : Option (Nat × Nat) :=
  match Expr.constVal p.peer, Expr.constVal p.val with
  | some (Term.agent a), some d =>
      if Term.agent a ∈ sh.U && d ∈ sh.U then
        some (uIdx sh (some d), uIdx sh (some (Term.agent a)))
      else none
  | _, _ => none

/-- **The model condition of the prototype**: every claim and commit of the model is nameable by a
fixed pair of value literals. Decidable, and a condition on the model and the bounds rather than on
any run. -/
def authNameable (sh : Shape) (P : Protocol) : Prop :=
  ∀ p ∈ authPositions P, (authOccIdx sh p).isSome

/-- The named occurrences of the commit (or, with `commit = false`, the claim) positions of the
model, one per step of the bound. -/
def authOccs (sh : Shape) (P : Protocol) (commit : Bool) : List AuthOcc :=
  (authPositions P).filter (fun p => p.isCommit == commit) >>= fun p =>
    match authOccIdx sh p with
    | none => []
    | some (u, u') => (List.range sh.steps).map fun i =>
        { pos := p, step := i, data := u, peerVal := u' }

/-- The literals saying "this authentication occurrence happens": the session acts, its program
counter is the position's, and the two annotation expressions evaluate to the two recorded values.
These are the per-session, per-step, per-variable value literals of `ProtSat.Encode` - the same
`vxe` groups the send and check clauses already use. -/
def authOccLits (sh : Shape) (P : Protocol) (o : AuthOcc) : List Lit :=
  [pos (evAct sh o.step o.pos.sess),
    pos (vpc sh o.step o.pos.sess o.pos.pc),
    pos (vxe sh o.step o.pos.sess (eIdx P o.pos.val) o.data),
    pos (vxe sh o.step o.pos.sess (eIdx P o.pos.peer) o.peerVal)]

/-! ### The new variables -/

/-- The agreement auxiliaries live after every block `ProtSat.Clauses` allocates. -/
def bsAuth (sh : Shape) : Nat := nVarsAll sh

/-- The auxiliary variable of agreement occurrence number `k`. -/
def vauth (sh : Shape) (k : Nat) : BVar := bsAuth sh + k

/-- The auxiliary variable defining the conjunction "commit occurrence `o` happens". -/
def authOccVar (sh : Shape) (P : Protocol) (o : AuthOcc) : BVar :=
  vauth sh (ixOf o (authOccs sh P true))

/-- The total number of variables of the agreement encoding. -/
def nVarsAgreement (sh : Shape) (P : Protocol) : Nat := bsAuth sh + (authOccs sh P true).length

/-! ### The clauses -/

/-- Does the claim occurrence `k` excuse the commit occurrence `c`? -/
def claimExcuses (m : Matching) (sh : Shape) (P : Protocol) (c k : AuthOcc) : Bool :=
  !k.pos.isCommit && k.pos.tag == c.pos.tag && k.data == c.data &&
    match m with
    | Matching.tripleOnly => k.peerVal == c.peerVal
    | Matching.orderAware =>
        k.step < c.step && sessSelf P k.pos.sess == agentAt sh c.peerVal &&
          agentAt sh k.peerVal == sessSelf P c.pos.sess

/-- The Tseitin definitions of the commit-occurrence conjunctions: one `andNDef` block per commit
occurrence, exactly like `ProtSat.Encode.leakAuxClauses` does for the leak conjunctions. -/
def authAuxClauses (sh : Shape) (P : Protocol) : List (List Lit) :=
  (authOccs sh P true).flatMap fun o => (andNDef (authOccVar sh P o) (authOccLits sh P o)).clauses

/-- **The agreement violation literals**: one per way a commit can happen at all. The clause built
from them demands that some commit occurrence is present in the run. -/
def authViolationLits (sh : Shape) (P : Protocol) : List Lit :=
  (authOccs sh P true).map fun o => pos (authOccVar sh P o)

/-- The excuse clauses: for each commit occurrence and each claim occurrence that could excuse it,
the clause forbidding "this commit is the violation and that claim happened". Conditional on the
selector, so a claim that excuses one candidate does not constrain another. -/
def authExcuseClauses (m : Matching) (sh : Shape) (P : Protocol) : List (List Lit) :=
  (authOccs sh P true).flatMap fun c =>
    (authOccs sh P false).filterMap fun k =>
      if claimExcuses m sh P c k then
        some ([neg (authOccVar sh P c)] ++ (authOccLits sh P k).map Lit.flip)
      else none

/-- The whole agreement violation group: the demand, the excuse clauses and the definitions. -/
def authViolationClauses (m : Matching) (sh : Shape) (P : Protocol) : CNF :=
  cnfOf ([authViolationLits sh P] ++ authExcuseClauses m sh P ++ authAuxClauses sh P)

/-! ### The encodings -/

/-- The ten semantic clause groups of `ProtSat.Clauses.encodeGroups` without the secrecy violation
group: everything the encoding says about runs, and nothing about which question is being asked. -/
def baseGroups (sh : Shape) (P : Protocol) : List CNF :=
  [oneHotClauses sh P, initClauses sh P, frameClauses sh, evalClauses sh P,
    stepClauses sh P, dedClauses sh, pubAuxClauses sh P, knSupportClauses sh P,
    freshClauses sh P, leakAuxClauses sh P]

/-- The semantic groups as one formula. -/
def baseEncode (P : Protocol) (B : Bounds) : CNF :=
  cnfOf ((baseGroups (shapeOf P B) P).flatMap (·.clauses))

/-- The clause groups of the encoding are the semantic groups with the secrecy violation group
appended: the equation that makes the regression gate below a one-liner. -/
theorem encodeGroups_eq (sh : Shape) (P : Protocol) :
    encodeGroups sh P = baseGroups sh P ++ [violationClauses sh P] := by
  simp [encodeGroups, baseGroups]

/-- **The old formula is untouched.** `encode` is the semantic groups conjoined with the secrecy
violation clause - the new file adds clauses, it does not change one. -/
theorem encode_eq_base_append (P : Protocol) (B : Bounds) :
    encode P B = baseEncode P B ++ violationClauses (shapeOf P B) P := by
  have key : (encodeGroups (shapeOf P B) P).flatMap (·.clauses) =
      (baseGroups (shapeOf P B) P).flatMap (·.clauses)
        ++ (violationClauses (shapeOf P B) P).clauses := by
    rw [encodeGroups_eq, List.flatMap_append]
    simp
  unfold encode baseEncode
  rw [key]
  rfl

/-- **The task's `authEncode`**: the existing secrecy encoding conjoined with the agreement
violation demand. SAT means "a run in which a secrecy violation and an agreement violation are both
permitted". -/
def authEncode (P : Protocol) (B : Bounds) (m : Matching := Matching.orderAware) : CNF :=
  encode P B ++ authViolationClauses m (shapeOf P B) P

/-- **The agreement-only encoding**: the semantic groups conjoined with the agreement violation
demand and *nothing* about secrecy. SAT means "an agreement violation is permitted". This is the
form the AuthGap model needs, because its secrecy demand is unsatisfiable for a reason that has
nothing to do with agreement. -/
def agreementEncode (P : Protocol) (B : Bounds) (m : Matching := Matching.orderAware) : CNF :=
  baseEncode P B ++ authViolationClauses m (shapeOf P B) P

/-- **The goal-indexed encoding** - the shape the eventual `Encode.encode` needs. The violation group
is chosen by the goals the query selected, so a secrecy-only query gets exactly the old formula and
an agreement-only query gets the old semantic groups with the agreement demand in place of the
secrecy one. -/
def violationGroups (sh : Shape) (P : Protocol) (gs : List Goal) (m : Matching) : List CNF :=
  (if gs.elem Goal.secrecy then [violationClauses sh P] else [])
    ++ (if gs.elem Goal.agreement then [authViolationClauses m sh P] else [])

def encodeGoals (P : Protocol) (B : Bounds) (gs : List Goal)
    (m : Matching := Matching.orderAware) : CNF :=
  cnfOf ((baseGroups (shapeOf P B) P ++ violationGroups (shapeOf P B) P gs m).flatMap (·.clauses))

/-- The goal-indexed violation groups of a secrecy-only query are the old clause groups. -/
theorem violationGroups_secrecy (sh : Shape) (P : Protocol) (m : Matching) :
    violationGroups sh P [Goal.secrecy] m = [violationClauses sh P] := by
  have h1 : ([Goal.secrecy] : List Goal).elem Goal.secrecy = true := by decide
  have h2 : ([Goal.secrecy] : List Goal).elem Goal.agreement = false := by decide
  rw [violationGroups, h1, h2]
  simp

/-- **The regression gate, part 1**: a secrecy-only query gets the old formula, definitionally. -/
theorem encodeGoals_secrecy (P : Protocol) (B : Bounds) (m : Matching) :
    encodeGoals P B [Goal.secrecy] m = encode P B := by
  unfold encodeGoals encode
  rw [violationGroups_secrecy]
  rfl

/-- The goal-indexed violation groups of an agreement-only query are the new clauses alone. -/
theorem violationGroups_agreement (sh : Shape) (P : Protocol) (m : Matching) :
    violationGroups sh P [Goal.agreement] m = [authViolationClauses m sh P] := by
  have h1 : ([Goal.agreement] : List Goal).elem Goal.secrecy = false := by decide
  have h2 : ([Goal.agreement] : List Goal).elem Goal.agreement = true := by decide
  rw [violationGroups, h1, h2]
  simp

/-- **The regression gate, part 2**: an agreement-only query is the old semantic groups plus the new
clauses, so nothing of the old encoding is lost or altered. -/
theorem encodeGoals_agreement (P : Protocol) (B : Bounds) (m : Matching) :
    encodeGoals P B [Goal.agreement] m = agreementEncode P B m := by
  have key : (baseGroups (shapeOf P B) P ++ [authViolationClauses m (shapeOf P B) P]).flatMap (·.clauses)
      = (baseGroups (shapeOf P B) P).flatMap (·.clauses)
        ++ (authViolationClauses m (shapeOf P B) P).clauses := by
    rw [List.flatMap_append]
    simp
  unfold encodeGoals agreementEncode baseEncode
  rw [violationGroups_agreement, key]
  rfl

/-- And the task's conjunction of both is the old formula plus the new clauses. -/
theorem authEncode_eq (P : Protocol) (B : Bounds) (m : Matching) :
    authEncode P B m = encode P B ++ authViolationClauses m (shapeOf P B) P := rfl



/-! ### The obstruction: why `encode P B ++ ...` cannot find the AuthGap attack

The gates below are kernel computations over the generated formula, so they need the same relaxed
recursion and heartbeat limits that ProtSat/Regressions.lean and ProtSat/AuthGap.lean set. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The AuthGap attack model declares no secret, so the secrecy violation clause of the task's
`authEncode` is the empty clause - and the agreement clauses, however good, are conjoined with it.
This is the precise reason the violation group has to become goal-indexed. -/
theorem authEncode_empty_clause :
    ([] : List Lit) ∈ (authEncode Regressions.Authentication.P
      Regressions.Authentication.B).clauses := by
  decide

/-- Hence the task's literal `authEncode` is unsatisfiable on the very model the task names: the new
clauses cannot be the reason, and cannot be the fix, in that form. -/
theorem authEncode_not_sat :
    ProtSat.Unsat (authEncode Regressions.Authentication.P Regressions.Authentication.B) := by
  intro ⟨a, ha⟩
  have h := ha [] authEncode_empty_clause
  rw [clause_eval_nil] at h
  exact absurd h (by simp)

/-! ### The non-vacuity gate: an explicit satisfying assignment -/

/-- A decision list denotes a satisfying assignment as soon as every clause evaluates true under it. -/
theorem sat_of_all {f : CNF} {a : Assignment}
    (h : f.clauses.all (fun c => Clause.eval a c) = true) : Sat a f := by
  rw [List.all_eq_true] at h
  exact fun c hc => h c hc

/-- **The attack assignment**, as the reference solver returned it for the AuthGap model under the
agreement-only encoding. Undecided variables are false, so only the pairs set to true are listed.
It is checked below, not trusted: the kernel verifies every clause against it. -/
def attackAsg : List (BVar × Bool) := [(550, true), (142, true), (548, true), (140, true), (536, true), (537, true), (538, true), (539, true), (540, true), (541, true), (542, true), (543, true), (544, true), (545, true), (546, true), (128, true), (524, true), (525, true), (526, true), (527, true), (528, true), (529, true), (530, true), (531, true), (532, true), (533, true), (534, true), (116, true), (476, true), (477, true), (478, true), (479, true), (480, true), (481, true), (482, true), (483, true), (484, true), (485, true), (486, true), (276, true), (440, true), (441, true), (442, true), (443, true), (444, true), (445, true), (446, true), (447, true), (448, true), (449, true), (450, true), (240, true), (404, true), (405, true), (406, true), (407, true), (408, true), (409, true), (410, true), (411, true), (412, true), (413, true), (414, true), (204, true), (368, true), (369, true), (370, true), (371, true), (372, true), (373, true), (374, true), (375, true), (376, true), (377, true), (378, true), (168, true), (0, true), (288, true), (2, true), (290, true), (19, true), (31, true), (56, true), (57, true), (59, true), (60, true), (68, true), (69, true), (71, true), (72, true), (145, true), (345, true), (346, true), (347, true), (348, true), (349, true), (350, true), (351, true), (352, true), (353, true), (354, true), (156, true), (356, true), (357, true), (358, true), (359, true), (360, true), (361, true), (362, true), (363, true), (364, true), (365, true), (366, true), (181, true), (381, true), (382, true), (383, true), (384, true), (385, true), (386, true), (387, true), (388, true), (389, true), (390, true), (192, true), (392, true), (393, true), (394, true), (395, true), (396, true), (397, true), (398, true), (399, true), (400, true), (401, true), (402, true), (217, true), (417, true), (418, true), (419, true), (420, true), (421, true), (422, true), (423, true), (424, true), (425, true), (426, true), (228, true), (428, true), (429, true), (430, true), (431, true), (432, true), (433, true), (434, true), (435, true), (436, true), (437, true), (438, true), (253, true), (453, true), (454, true), (455, true), (456, true), (457, true), (458, true), (459, true), (460, true), (461, true), (462, true), (264, true), (464, true), (465, true), (466, true), (467, true), (468, true), (469, true), (470, true), (471, true), (472, true), (473, true), (474, true), (6, true), (294, true), (55, true), (648, true), (81, true), (489, true), (490, true), (491, true), (492, true), (493, true), (494, true), (495, true), (496, true), (497, true), (498, true), (499, true), (500, true), (501, true), (502, true), (503, true), (504, true), (5, true), (43, true)]

/-- **The headline gate.** The agreement clauses are satisfiable on the AuthGap attack model - the
model `AuthGap.safe_for_secrecy2` proves *safe* through the CNF route. The old clauses could not
even state the question; these do, and a model of them exists. -/
theorem gate_agreement_attack_found :
    ProtSat.Satisfiable (agreementEncode Regressions.Authentication.P
      Regressions.Authentication.B Matching.orderAware) :=
  ⟨DPLL.asgVal attackAsg,
   sat_of_all (by decide : (agreementEncode Regressions.Authentication.P
      Regressions.Authentication.B Matching.orderAware).clauses.all
      (fun c => Clause.eval (DPLL.asgVal attackAsg) c) = true)⟩

/-- **The second attack gate.** On `Contract.Gates.authSwappedP` - commit first, the matching
claim after - the ordered clauses are satisfiable too, and so are the unordered ones: the model can
reach the commit without ever performing the claim, and that alone is an agreement violation. What the
two matchings disagree about is *which runs* witness it - under `tripleOnly` the two-step trace
commit-then-claim is excused, under `orderAware` it is not - and the disagreement is a property of
the generated clauses, not of a proof. -/
def swappedAsg : List (BVar × Bool) := [(448, true), (449, true), (450, true), (451, true), (452, true), (120, true), (442, true), (443, true), (444, true), (445, true), (446, true), (114, true), (436, true), (437, true), (438, true), (439, true), (440, true), (108, true), (430, true), (431, true), (432, true), (433, true), (434, true), (102, true), (400, true), (401, true), (402, true), (403, true), (404, true), (405, true), (406, true), (407, true), (408, true), (72, true), (394, true), (395, true), (396, true), (397, true), (398, true), (232, true), (376, true), (377, true), (378, true), (379, true), (380, true), (214, true), (358, true), (359, true), (360, true), (361, true), (362, true), (196, true), (340, true), (341, true), (342, true), (343, true), (344, true), (178, true), (322, true), (323, true), (324, true), (325, true), (326, true), (160, true), (304, true), (305, true), (306, true), (307, true), (308, true), (142, true), (244, true), (245, true), (35, true), (567, true), (83, true), (411, true), (412, true), (413, true), (414, true), (415, true), (416, true), (417, true), (418, true), (13, true), (251, true), (47, true), (6, true), (126, true), (127, true), (128, true), (129, true), (0, true), (238, true), (239, true), (3, true), (241, true), (242, true), (23, true), (29, true), (54, true), (55, true), (60, true), (61, true), (66, true), (67, true), (130, true), (292, true), (293, true), (294, true), (295, true), (296, true), (140, true), (302, true), (148, true), (310, true), (311, true), (312, true), (313, true), (314, true), (158, true), (320, true), (166, true), (328, true), (329, true), (330, true), (331, true), (332, true), (176, true), (338, true), (184, true), (346, true), (347, true), (348, true), (349, true), (350, true), (194, true), (356, true), (202, true), (364, true), (365, true), (366, true), (367, true), (368, true), (212, true), (374, true), (220, true), (382, true), (383, true), (384, true), (385, true), (386, true), (230, true), (392, true), (9, true), (247, true), (248, true), (41, true), (15, true), (253, true), (254, true), (53, true)]

theorem gate_swapped_attack_found :
    ProtSat.Satisfiable (agreementEncode ProtSat.Reference.Contract.Gates.authSwappedP
      ProtSat.Reference.Contract.Gates.authOrderB Matching.orderAware) :=
  ⟨DPLL.asgVal swappedAsg,
   sat_of_all (by decide : (agreementEncode ProtSat.Reference.Contract.Gates.authSwappedP
      ProtSat.Reference.Contract.Gates.authOrderB Matching.orderAware).clauses.all
      (fun c => Clause.eval (DPLL.asgVal swappedAsg) c) = true)⟩

/-- The new clauses are not vacuous in the other direction either: the excuse clauses really are
generated, so the solver is being told something about which claims excuse which commits. -/
theorem gate_excuse_clauses_present :
    (authExcuseClauses Matching.orderAware
      (shapeOf ProtSat.Reference.Contract.Gates.authOrderP
        ProtSat.Reference.Contract.Gates.authOrderB)
      ProtSat.Reference.Contract.Gates.authOrderP) ≠ [] := by
  decide

/-! ### The safety gate: a kernel-checked core of the ordered model -/

/-- If every clause of `g` is a clause of `f`, unsatisfiability transfers from `g` to `f`: a
model of the bigger formula is a model of the smaller one. -/

theorem unsat_of_clauses_subset {f g : CNF}
    (h : ∀ c ∈ g.clauses, c ∈ f.clauses) (hg : ProtSat.Unsat g) : ProtSat.Unsat f := by
  intro ⟨a, ha⟩
  exact hg ⟨a, fun c hc => ha c (h c hc)⟩

abbrev shOrder : Shape :=
  shapeOf ProtSat.Reference.Contract.Gates.authOrderP ProtSat.Reference.Contract.Gates.authOrderB

abbrev orderP : Protocol := ProtSat.Reference.Contract.Gates.authOrderP

abbrev orderB : ProtSat.Bounded.Bounds := ProtSat.Reference.Contract.Gates.authOrderB

theorem mem_baseGroups_oneHot : oneHotClauses shOrder orderP ∈ baseGroups shOrder orderP := by
  unfold baseGroups; exact List.mem_cons.mpr (Or.inl rfl)

theorem mem_baseGroups_init : initClauses shOrder orderP ∈ baseGroups shOrder orderP := by
  unfold baseGroups
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem mem_baseGroups_frame : frameClauses shOrder ∈ baseGroups shOrder orderP := by
  unfold baseGroups
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

theorem mem_baseGroups_eval : evalClauses shOrder orderP ∈ baseGroups shOrder orderP := by
  unfold baseGroups
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
/-- The clause list of a conjunction of formulas. -/
theorem clauses_append (f g : CNF) : (f ++ g).clauses = f.clauses ++ g.clauses := rfl

/-- Every clause of a semantic group is a clause of the agreement encoding. -/
theorem mem_agreementEncode_group {g : CNF} (hg : g ∈ baseGroups shOrder orderP) :
    ∀ c ∈ g.clauses, c ∈ (agreementEncode orderP orderB Matching.orderAware).clauses :=
  fun _c hc => List.mem_append_left _ (List.mem_flatMap.mpr ⟨g, hg, hc⟩)

def orderCoreClauses : List (List Lit) :=
  (authViolationClauses Matching.orderAware shOrder orderP).clauses
    ++ (initPcClauses shOrder 0
      ++ ((pcOh shOrder 1 0).clauses.clauses
        ++ (frameSessClauses shOrder 0 0
          ++ (evalGate shOrder orderP 0 0 (Expr.nonce 5)
            ++ evalGate shOrder orderP 0 0 (Expr.agent 0)))))

def orderCore : CNF := cnfOf orderCoreClauses

theorem agreementEncode_clauses :
    (agreementEncode orderP orderB Matching.orderAware).clauses =
      (baseGroups shOrder orderP).flatMap (·.clauses)
        ++ (authViolationClauses Matching.orderAware shOrder orderP).clauses := by
  unfold agreementEncode baseEncode
  rw [clauses_append]
  rfl

theorem orderCore_subset :
    ∀ c ∈ orderCore.clauses,
      c ∈ (agreementEncode orderP orderB Matching.orderAware).clauses := by
  decide
theorem orderCore_dpll_none : DPLL.dpll orderCore = none := by decide

theorem gate_order_unsat :
    ProtSat.Unsat (agreementEncode orderP orderB Matching.orderAware) :=
  unsat_of_clauses_subset orderCore_subset (DPLL.dpll_complete orderCore_dpll_none)


/-- **The model condition is not a hypothesis the gates have to assume.** Every agreement model this
repository uses satisfies `authNameable`: each claim and commit names its peer and its data by a
closed constant the universe contains. Decided, not asserted. -/
theorem authNameable_gates :
    authNameable (shapeOf Regressions.Authentication.P Regressions.Authentication.B)
      Regressions.Authentication.P
      ∧ authNameable (shapeOf ProtSat.Reference.Contract.Gates.authOrderP
        ProtSat.Reference.Contract.Gates.authOrderB) ProtSat.Reference.Contract.Gates.authOrderP
      ∧ authNameable (shapeOf ProtSat.Reference.Contract.Gates.authSwappedP
        ProtSat.Reference.Contract.Gates.authOrderB) ProtSat.Reference.Contract.Gates.authSwappedP
      ∧ authNameable (shapeOf AuthGap.P2 AuthGap.B2) AuthGap.P2 := by
  unfold authNameable
  decide

/-- And each of them really has a commit position, so the demand clause is a demand and not the
empty disjunction over nothing - the failure mode ~~AuthGap.why_the_formula_is_unsat~~ records for the
secrecy clause. -/
theorem authPositions_gates_nonempty :
    (authPositions Regressions.Authentication.P).any (fun p => p.isCommit)
      ∧ (authPositions ProtSat.Reference.Contract.Gates.authOrderP).any (fun p => p.isCommit)
      ∧ (authPositions ProtSat.Reference.Contract.Gates.authSwappedP).any (fun p => p.isCommit)
      ∧ (authPositions AuthGap.P2).any (fun p => p.isCommit) :=
  by decide

/-! ### The differential gate: the CNF and the reference monitor answer the same question -/

namespace Diff

open ProtSat.Reference.Contract

/-- **Differential, attacked side.** On the AuthGap model both routes say *attacked*: the CNF has a
model (proved above by an explicit certificate, not by trusting the solver) and the reference
enumeration finds the violating execution. -/
theorem diff_authentication :
    ProtSat.Satisfiable (agreementEncode Regressions.Authentication.P
        Regressions.Authentication.B Matching.orderAware) ∧
      attackFound (Query.mk Regressions.Authentication.P Regressions.Authentication.B
        [Goal.agreement]) = true :=
  ⟨gate_agreement_attack_found, by decide⟩

/-- **Differential, attacked side, ordering model.** The same on the swapped model. -/
theorem diff_authSwapped :
    ProtSat.Satisfiable (agreementEncode Gates.authSwappedP Gates.authOrderB
        Matching.orderAware) ∧
      attackFound (Query.mk Gates.authSwappedP Gates.authOrderB [Goal.agreement]) = true :=
  ⟨gate_swapped_attack_found, by decide⟩

/-- **Differential, safe side.** On the ordered model both routes say *safe*: the CNF is
unsatisfiable and the enumeration finds no attack. -/
theorem diff_authOrder :
    ProtSat.Unsat (agreementEncode Gates.authOrderP Gates.authOrderB Matching.orderAware) ∧
      attackFound (Query.mk Gates.authOrderP Gates.authOrderB [Goal.agreement]) = false :=
  ⟨gate_order_unsat, by decide⟩

end Diff

end ProtSat.AuthClauses

