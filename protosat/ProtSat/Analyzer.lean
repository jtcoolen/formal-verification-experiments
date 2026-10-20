/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import ProtSat.Certificate
import ProtSat.DPLL
import ProtSat.Complete

/-!
# ProtSat: the end-to-end proof-producing analyser (specification sections 7, 8F, 8H)

## The pipeline

    analyze P B =  if the bounds are too small to state the question then boundsTooSmall
                   else match dpll (encode P B) with
                     | none     => encodingUnsat
                     | some asg => attack (certOf P B asg)

1. ProtSat.Encode.encode compiles the bounded executions of P into a CNF (section 5);
2. ProtSat.DPLL.dpll searches for a model of that CNF (section 6);
3. ProtSat.Encoding turns a model into a concrete bounded run of the operational semantics
   (section 8A);
4. ProtSat.Analyzer.certOf packages that run as a ProtSat.Certificate.Certificate, and
   ProtSat.Certificate.checkCertificate re-validates it from scratch (section 7).

## What is guaranteed

The pipeline is proved correct in both directions *about the CNF it generates*.  What the CNF
asks is the bounded question "does some execution of at most B.steps events inside the universe
univ P B leak a declared secret", so an `encodingUnsat` answer is a statement about leaks, not
about the whole of `ProtSat.Bounded.BoundedAttack` (which also admits authentication-agreement
violations).  ProtSat.Query is the layer that states which verdicts carry which security claim.

* dpll_sound (8D) makes the model real;
* encoding_sound (8A) makes the decoded run a genuine ProtSat.Rel execution that leaks;
* checkCertificate_sound (8C) makes the certificate independently checkable: the checker
  imports neither the CNF nor the solver, so an accepted certificate is evidence that does
  not depend on trusting the encoder or the solver;
* analyze_attack_sound (8F) chains the three: an attack verdict yields a checked
  certificate and hence a valid bounded attack trace.

## Termination (specification 8H)

Every stage is a terminating computation for a structural reason checked by the kernel:
encode is a finite concatenation over the shape's index sets; dpll recurses on its list of
branching variables with unit propagation recursing on its fuel; certOf recurses on the
step bound; checkCertificate is a fold over the certificate's step list.  Nothing in the
pipeline takes fuel from the caller, and nothing uses partiality or native_decide.
-/

namespace ProtSat.Analyzer

open ProtSat Term OneHot Bounded Attacker Encode Encoding Certificate DPLL
open Protocol

/-! ### Deciding the universe hypothesis -/

/-- The executable form of ProtSat.Encode.univClosed: the condition is quantified over the
finite list allExprs P, so it is a Boolean test.  The analyser runs it first: if the universe
does not even contain the messages the protocol denotes with closed expressions, the bounds
are too small to state the question and no verdict is meaningful. -/
def univClosedBool (sh : Shape) (P : Protocol) : Bool :=
  (allExprs P).all fun e => admissible sh (Expr.constVal e)

/-- The Boolean test agrees with the Prop it decides. -/
theorem univClosedBool_iff (sh : Shape) (P : Protocol) :
    univClosedBool sh P = true <-> univClosed sh P := by
  classical
  simp only [univClosedBool, univClosed, List.all_eq_true]

/-! ### Building a certificate out of a satisfying assignment -/

/-- The certificate steps of the decoded run, restricted to its last k steps: the i-th
element pairs the event taken at step i with the configuration reached after it.  Built by
recursion on k, prepending the earliest step, so that the inductions below match the
cons-structure of ProtSat.Encoding.decEvsFrom. -/
def stepsOf (P : Protocol) (B : Bounds) (a : Assignment) : Nat -> List CertStep
  | 0 => []
  | k + 1 =>
      { ev := decEv (shapeOf P B) P a (B.steps - (k + 1)),
        after := decRun P B a (B.steps - k) } :: stepsOf P B a k

/-- The certificate the analyser produces from a satisfying assignment: the decoded run,
packaged as data.  Nothing here trusts the encoding: the checker that consumes this object
recomputes every transition from ProtSat.Operational. -/
def certOf (P : Protocol) (B : Bounds) (a : Assignment) : Certificate :=
  { init := initCfg P, steps := stepsOf P B a B.steps }

/-- decRun at step 0 is the initial configuration. -/
theorem decRun_zero (P : Protocol) (B : Bounds) (a : Assignment) :
    decRun P B a 0 = initCfg P := rfl

/-- The events of the certificate steps are the decoded events. -/
theorem stepsOf_ev (P : Protocol) (B : Bounds) (a : Assignment) :
    ∀ (k : Nat), k ≤ B.steps ->
      (stepsOf P B a k).map (fun s => s.ev) = decEvsFrom P B a k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      show ({ ev := decEv (shapeOf P B) P a (B.steps - (k + 1)), after := _ }
          :: stepsOf P B a k).map (fun s => s.ev) = decEvsFrom P B a (k + 1)
      rw [decEvsFrom, List.map_cons, ih (by omega)]

/-- The configurations visited by the certificate steps are the decoded configurations. -/
theorem stepsOf_cfgs (P : Protocol) (B : Bounds) (a : Assignment) :
    ∀ (k : Nat), k ≤ B.steps ->
      decRun P B a (B.steps - k) :: (stepsOf P B a k).map (fun s => s.after)
        = decCfgsFrom P B a k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      show decRun P B a (B.steps - (k + 1))
          :: List.map (fun s => s.after)
            ({ ev := _, after := decRun P B a (B.steps - k) } :: stepsOf P B a k) = _
      rw [decCfgsFrom, List.map_cons, ih (by omega)]

/-- Every certificate step is accepted by the step checker: the decoded event really takes
decRun i to decRun (i+1) - which is what ProtSat.Encoding.rel_agrees says - and
ProtSat.Certificate.relDecide_complete turns that proof into a Boolean true. -/
theorem stepsOf_ok (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    ∀ (k : Nat), k ≤ B.steps ->
      checkSteps P (decRun P B a (B.steps - k)) (stepsOf P B a k) = true := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hi : B.steps - (k + 1) < B.steps := by omega
      have hag := agrees_decRun h hU (B.steps - (k + 1)) (by omega)
      have hstep := rel_agrees hU h hi hag
      have hdec : decStep P B a (decRun P B a (B.steps - (k + 1))) (B.steps - (k + 1))
          = decRun P B a (B.steps - k) := by
        have h1 : B.steps - k = (B.steps - (k + 1)) + 1 := by omega
        rw [h1]
        show decStep P B a (decRun P B a (B.steps - (k + 1))) (B.steps - (k + 1))
            = decStep P B a (decRun P B a (B.steps - (k + 1))) (B.steps - (k + 1))
        rfl
      show checkSteps P (decRun P B a (B.steps - (k + 1)))
          ({ ev := decEv (shapeOf P B) P a (B.steps - (k + 1)),
             after := decRun P B a (B.steps - k) } :: stepsOf P B a k) = true
      rw [checkSteps, Bool.and_eq_true]
      refine ⟨relDecide_complete (hdec ▸ hstep.1), ih (by omega)⟩

/-- The trace of the certificate the analyser produces is the decoded run. -/
theorem certOf_trace (P : Protocol) (B : Bounds) (a : Assignment) :
    certTrace (certOf P B a) = decEvsFrom P B a B.steps :=
    stepsOf_ev P B a B.steps (Nat.le_refl _)

/-- The configurations visited by the certificate are the decoded configurations. -/
theorem certOf_cfgs (P : Protocol) (B : Bounds) (a : Assignment) :
    certCfgs (certOf P B a) = decCfgsFrom P B a B.steps := by
  show initCfg P :: List.map (fun s => s.after) (stepsOf P B a B.steps) = _
  rw [← stepsOf_cfgs P B a B.steps (Nat.le_refl _)]
  have h0 : decRun P B a (B.steps - B.steps) = initCfg P := by
    rw [Nat.sub_self]; exact decRun_zero P B a
  rw [h0]

/-- **The certificate built from a satisfying assignment passes the independent checker**
(specification section 7: the certificate is checked, not trusted). -/
theorem certOf_checked (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    checkCertificate P (certOf P B a) = true := by
  have hle : runsLeaksBool P (certCfgs (certOf P B a)) = true := by
    rw [runsLeaksBool_iff, certOf_cfgs]
    obtain ⟨i, hi, hleak⟩ := violation_leak hU h
    have hmem : decRun P B a i ∈ decCfgsFrom P B a B.steps := by
      have h1 : decRun P B a (B.steps - (B.steps - i)) ∈ decCfgsFrom P B a B.steps :=
        decCfgsFrom_mem P B a B.steps (B.steps - i) (by omega)
      rw [Nat.sub_sub_self (by omega : i ≤ B.steps)] at h1
      exact h1
    exact ⟨decRun P B a i, hmem, hleak⟩
  have hcs : checkSteps P (certOf P B a).init (certOf P B a).steps = true := by
    show checkSteps P (initCfg P) (stepsOf P B a B.steps) = true
    have h0 : decRun P B a (B.steps - B.steps) = initCfg P := by
      rw [Nat.sub_self]; exact decRun_zero P B a
    rw [← h0]
    exact stepsOf_ok hU h B.steps (Nat.le_refl _)
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨⟨beq_iff_eq.mpr rfl, hcs⟩, Or.inl hle⟩

/-! ### The analyser -/

/-- The answer of the low-level analyser.

The names state exactly what each answer is, because the two are not the same claim:

* `boundsTooSmall`: the declared bounds do not even satisfy the closure hypothesis the
  encoding theorems need, so neither of the other answers would mean anything;
* `encodingUnsat`: the solver proved that the *generated CNF* has no model.  This is a fact
  about a Boolean formula.  It is **not** yet a security verdict: the violation clause of the
  encoding (ProtSat.Encode.violationLits) demands a declared-secret leak, so an
  `encodingUnsat` answer says nothing about executions that break authentication agreement
  without leaking a secret.  See ProtSat.Query for the contract that keeps the two apart, and
  ProtSat.Regressions.Authentication for a query where the two genuinely differ.
* `attack c`: a certificate that the independent checker accepts. -/
inductive Verdict : Type
  | boundsTooSmall : Verdict
  | encodingUnsat : Verdict
  | attack : Certificate -> Verdict
  deriving Repr

/-- **The analyser** (specification section 7). -/
def analyze (P : Protocol) (B : Bounds) : Verdict :=
  if ! (univClosedBool (shapeOf P B) P) then Verdict.boundsTooSmall
  else match dpll (encode P B) with
    | none => Verdict.encodingUnsat
    | some asg => Verdict.attack (certOf P B (asgVal asg))

/-- The two facts the attack verdict is made of, isolated so the case analysis over the
verdict happens once. -/
theorem analyze_attack_cases {P : Protocol} {B : Bounds} {c : Certificate}
    (h : analyze P B = Verdict.attack c) :
    univClosed (shapeOf P B) P ∧ ∃ a, Sat a (encode P B) ∧ c = certOf P B a := by
  rw [analyze] at h
  by_cases hu : univClosedBool (shapeOf P B) P
  · rw [if_neg (by simp [hu])] at h
    rcases option_cases (dpll (encode P B)) with hnone | ⟨asg, hsat⟩
    · simp only [hnone] at h; cases h
    · simp only [hsat] at h
      cases h
      exact ⟨(univClosedBool_iff (shapeOf P B) P).mp hu, asgVal asg, dpll_sound hsat, rfl⟩
  · rw [if_pos (by simp [hu])] at h
    cases h

/-- **Specification 8F (end-to-end attack soundness).**  If the analyser reports an attack,
the certificate it returns is accepted by the independent checker, and therefore the
protocol really has a bounded attack trace: a sequence of protocol actions and adversary
deductions that ProtSat.Operational accepts and that violates the declared security
property. -/
theorem analyze_attack_sound {P : Protocol} {B : Bounds} {c : Certificate}
    (h : analyze P B = Verdict.attack c) :
    checkCertificate P c = true ∧ Attack P (certTrace c) := by
  obtain ⟨hU, a, ha, rfl⟩ := analyze_attack_cases h
  exact ⟨certOf_checked hU ha, checkCertificate_sound (certOf P B a)
    (certOf_checked hU ha)⟩

/-- **Specification 8F with the bound stated.**  The attack the analyser reports is a
bounded attack: its trace length is at most the step bound the caller declared. -/
theorem analyze_attack_bounded {P : Protocol} {B : Bounds} {c : Certificate}
    (h : analyze P B = Verdict.attack c) :
    Attack P (certTrace c) ∧ (certTrace c).length ≤ B.steps := by
  obtain ⟨hU, a, ha, rfl⟩ := analyze_attack_cases h
  refine ⟨checkCertificate_sound (certOf P B a) (certOf_checked hU ha), ?_⟩
  rw [certOf_trace, decEvsFrom_length]

/-! ### Specification 8G: end-to-end bounded safety -/

open ProtSat.Complete

/-- **Specification 8G (end-to-end bounded *secrecy*).**  If the analyser reports
`encodingUnsat` then there is no trace of at most B.steps steps that ProtSat.Operational accepts
from the initial configuration and whose visited configurations **leak a declared secret** -
provided the bounds can name such a run (ProtSat.Complete.WithinBounds) and cover the protocol's
declarations (ProtSat.Encode.univClosed, ProtSat.Complete.SecretsOK); the subterm-closure condition
`Complete.univSub` is no longer asked for - `Complete.univSub_shapeOf` proves it of the shape.

This is deliberately not stated as "the protocol has no bounded attack":
ProtSat.Bounded.BoundedAttack also counts a violation of non-injective agreement, and the
generated CNF has no clause for one.  The gap is ProtSat.Regressions.Authentication, and the
contract that refuses to call `encodingUnsat` a security verdict for such a query is
ProtSat.Query.analyzeQuery_unsupported_of_unencoded.

The proof is the composition of the two halves of the correspondence: had such a run existed,
ProtSat.Complete.encoding_complete (8B) would have produced a satisfying assignment of the
generated CNF; but a SAFE verdict means the solver returned none, and ProtSat.DPLL.dpll_complete
(8E) turns that into a proof that the CNF has no model at all.  Contradiction.

Two honest limitations, both of them the point of the specification's warnings:
* the verdict is *bounded*.  It says nothing about runs longer than B.steps, about messages
outside the universe, or about principals and nonces outside the declared domains;
* the violation condition the encoding demands is the declared secrecy property (the two forms
of ProtSat.Secret).  Authentication agreement is recorded in the trace and re-checked by the
certificate checker, but a SAFE verdict is a statement about the secrecy violation the CNF
asks for. -/
theorem analyze_safe_sound {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P)
    (hsec : SecretsOK (shapeOf P B) P) (h : analyze P B = Verdict.encodingUnsat) :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg),
        Runs P (initCfg P) tr Cs ∧ tr.length ≤ B.steps ∧ runsLeaks P Cs ∧
          WithinBounds P B (cfgAt Cs) (evAt tr) := by
  intro hsafe
  obtain ⟨tr, Cs, hrun, hlen, hleak, hbnd⟩ := hsafe
  obtain ⟨a, ha⟩ :=
    encoding_complete (P := P) (B := B) (tr := tr) (Cs := Cs) hU hsec hrun hlen hleak hbnd
  -- a SAFE verdict means the solver answered none
  have hnone : dpll (encode P B) = none := by
    rw [analyze] at h
    by_cases hu : univClosedBool (shapeOf P B) P
    · rw [if_neg (by simp [hu])] at h
      cases h' : dpll (encode P B) with
      | none => rfl
      | some asg =>
          rw [h'] at h
          cases h
    · rw [if_pos (by simp [hu])] at h
      cases h
  exact (DPLL.dpll_complete hnone) ⟨a, ha⟩

/-- **Specification 8G, contrapositive form.**  A bounded attack makes the analyser report
something other than SAFE.  Stated this way the theorem is the one a user of the tool actually
needs: the only way to see SAFE is that no bounded attack exists. -/
theorem analyze_not_safe_of_attack {P : Protocol} {B : Bounds}
    (hU : univClosed (shapeOf P B) P)
    (hsec : SecretsOK (shapeOf P B) P)
    (tr : List Ev) (Cs : List Cfg) (hrun : Runs P (initCfg P) tr Cs)
    (hlen : tr.length ≤ B.steps) (hleak : runsLeaks P Cs)
    (hbnd : WithinBounds P B (cfgAt Cs) (evAt tr)) :
    analyze P B ≠ Verdict.encodingUnsat := by
  intro hsafe
  exact (analyze_safe_sound hU hsec hsafe) ⟨tr, Cs, hrun, hlen, hleak, hbnd⟩

/-! ### Specification 8H: termination of the four stages -/

/-- A finite list of natural numbers is bounded: this is all the termination arguments below
need, because every stage of the pipeline recurses over such a list. -/
theorem exists_gt_of_mem (l : List Nat) : ∃ n : Nat, ∀ v ∈ l, v < n := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨max x n + 1, by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · omega
        · have := hn v hv
          omega⟩

/-- **Specification 8H (termination of the solver).**  DPLL always answers, and its answer is
right in both directions: it returns none exactly when the formula has no model.  The recursion
is structural on the list of distinct variables of the formula (ProtSat.DPLL.dpllAux branches on
its tail), and that list is finite by ProtSat.exists_gt_of_mem, so the search tree has finite
depth and the solver needs no fuel from the caller. -/
theorem dpll_none_iff_unsat (F : CNF) : DPLL.dpll F = none <-> ProtSat.Unsat F :=
  ⟨fun h => DPLL.dpll_complete h, fun h => by
    cases h' : DPLL.dpll F with
    | none => rfl
    | some asg =>
        exact absurd (DPLL.dpll_sound h') (by
          intro e
          exact h ⟨_, DPLL.dpll_sound h'⟩)⟩

/-- **Specification 8H (termination of the bounded state construction).**  Every index set the
encoding enumerates over is a finite non-empty list of explicit size: the sessions, program
counters, store slots, universe values, nonce choices, expression-table entries, event
alternatives and auxiliary blocks.  The bounded state is therefore a finite object, and the
encoding is a finite concatenation over it. -/
theorem shape_finite (P : Protocol) (B : Bounds) :
    0 < shS (shapeOf P B) ∧ 0 < shPc (shapeOf P B) ∧ 0 < shV (shapeOf P B) ∧
      0 < shVal (shapeOf P B) ∧ 0 < shD (shapeOf P B) ∧ 0 < shE (shapeOf P B) ∧
      0 < shEv (shapeOf P B) ∧
      0 < nVarsAll (shapeOf P B) ∧
      (shapeOf P B).steps = B.steps ∧ (shapeOf P B).U = univ P B ∧
      (shapeOf P B).D = P.nonceDomain := by
  refine ⟨shS_pos _, shPc_pos _, shV_pos _, shVal_pos _, shD_pos _, shE_pos _, shEv_pos _,
    Nat.succ_pos _, rfl, rfl, rfl⟩

/-- **Specification 8H (termination of the encoding).**  The generated CNF is a finite list of
clauses over a finite vocabulary: there is a number that bounds every variable the formula
mentions, so the solver's search space - assignments to those variables - is finite. -/
theorem encode_vocab_finite (P : Protocol) (B : Bounds) :
    ∃ n : Nat, ∀ v ∈ DPLL.litVars (encode P B).clauses, v < n :=
  exists_gt_of_mem _

/-- **Specification 8H (termination of certificate checking).**  The checker is a Boolean-valued
total function: it folds over the certificate's own step list, whose length is part of the
certificate, so it terminates without fuel and its answer is computable by evaluation.  The
substantive claim is not that it halts but that what it accepts is a real trace
(ProtSat.Certificate.checkCertificate_sound) and that what the analyser produces it accepts
(ProtSat.Analyzer.certOf_checked). -/
theorem checkCertificate_eq_decide (P : Protocol) (c : Certificate) :
    decide (checkCertificate P c = true) = checkCertificate P c := by
  cases h : checkCertificate P c <;> simp [h]

/-- **Specification 8H (the whole pipeline).**  For every protocol and every bounds record the
analyser returns one of its three verdicts: the analysis is a decision procedure on the declared
bounds, not a partial search. -/
theorem analyze_verdict_cases (P : Protocol) (B : Bounds) :
    analyze P B = Verdict.boundsTooSmall ∨ analyze P B = Verdict.encodingUnsat ∨
      ∃ c, analyze P B = Verdict.attack c := by
  by_cases hu : univClosedBool (shapeOf P B) P
  · rw [analyze]
    rw [if_neg (by simp [hu])]
    rcases option_cases (dpll (encode P B)) with hnone | ⟨asg, hsat⟩
    · exact Or.inr (Or.inl (by rw [hnone]))
    · exact Or.inr (Or.inr ⟨_, by rw [hsat]⟩)
  · left
    rw [analyze, if_pos (by simp [hu])]

end ProtSat.Analyzer
