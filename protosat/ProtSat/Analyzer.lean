/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import ProtSat.Certificate
import ProtSat.DPLL

/-!
# ProtSat: the end-to-end proof-producing analyser (specification sections 7, 8F, 8H)

## The pipeline

    analyze P B =  if the bounds are too small to state the question then boundsTooSmall
                   else match dpll (encode P B) with
                     | none     => safe
                     | some asg => attack (certOf P B asg)

1. ProtSat.Encode.encode compiles the bounded executions of P into a CNF (section 5);
2. ProtSat.DPLL.dpll searches for a model of that CNF (section 6);
3. ProtSat.Encoding turns a model into a concrete bounded run of the operational semantics
   (section 8A);
4. ProtSat.Analyzer.certOf packages that run as a ProtSat.Certificate.Certificate, and
   ProtSat.Certificate.checkCertificate re-validates it from scratch (section 7).

## What is guaranteed

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

/-- The answer of the analyser.  boundsTooSmall means the declared bounds do not even
satisfy the closure hypothesis the encoding theorems need, so neither of the other verdicts
would mean anything; safe means the solver proved the CNF unsatisfiable; attack carries a
certificate that the independent checker accepts. -/
inductive Verdict : Type
  | boundsTooSmall : Verdict
  | safe : Verdict
  | attack : Certificate -> Verdict
  deriving Repr

/-- **The analyser** (specification section 7). -/
def analyze (P : Protocol) (B : Bounds) : Verdict :=
  if ! (univClosedBool (shapeOf P B) P) then Verdict.boundsTooSmall
  else match dpll (encode P B) with
    | none => Verdict.safe
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

end ProtSat.Analyzer
