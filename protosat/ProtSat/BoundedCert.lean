/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Certificate
import ProtSat.Bounded
import ProtSat.Regressions

/-!
# ProtSat: certificates that carry their bounds (roadmap stage 5, first part)

## The gap this closes

`ProtSat.Certificate.checkCertificate` re-derives every transition and re-finds the violation, and
it imports neither the CNF nor the solver - which is what makes an attack verdict trustworthy. But it
checks nothing about the *bounds*. `ProtSat.Bounded.BoundedAttack P B` requires a trace of at most
`B.steps` events all of whose configurations lie inside `univ P B`, so
`ProtSat.Analyzer.analyze_attack_sound` yields `Attack` plus a length inequality rather than
`BoundedAttack`: the universe half was verified nowhere. `ProtSat.Regressions.Authentication` and
`ProtSat.Regressions.Bounds` each had to prove the universe fact separately by `decide`.

## What is here

`checkBounded P B c` is the certificate checker plus the two bound conditions, and
`checkBounded_sound` proves that accepting it yields `BoundedAttack P B` - the complete public
bounded predicate, with no hypothesis beyond the certificate and the bounds.

`out_of_universe_accepted_by_old_checker` and `out_of_universe_rejected` show the extra conditions
are not decoration: a run that is a legal `Rel` execution and really does leak is accepted by
`checkCertificate` and rejected by `checkBounded`, because the attacker's knowledge leaves the
universe. `too_long_rejected` is the step bound biting on the same certificate.
-/

namespace ProtSat.BoundedCert

open ProtSat Term Bounded Certificate

/-- The executable form of `ProtSat.Bounded.runsInUniverse`. -/
def runsInUniverseBool (Cs : List Cfg) (U : List Term) : Bool :=
  Cs.all (fun C => cfgInUniverse C U)

theorem runsInUniverseBool_iff (Cs : List Cfg) (U : List Term) :
    runsInUniverseBool Cs U = true <-> runsInUniverse Cs U := by
  rw [runsInUniverseBool, runsInUniverse, List.all_eq_true]

/-- **The bounded certificate checker**: the certificate is a legal run, it violates a declared
property, it is no longer than the step bound, and every configuration it visits lies inside the
message universe. -/
def checkBounded (P : Protocol) (B : Bounds) (c : Certificate) : Bool :=
  (checkCertificate P c && decide (c.steps.length ≤ B.steps)) &&
    runsInUniverseBool (certCfgs c) (univ P B)

/-- The three things `checkCertificate` conjoins, extracted one at a time. -/
theorem checkCertificate_init {P : Protocol} {c : Certificate}
    (h : checkCertificate P c = true) : c.init == initCfg P := by
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

theorem checkCertificate_steps {P : Protocol} {c : Certificate}
    (h : checkCertificate P c = true) : checkSteps P c.init c.steps = true := by
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

theorem checkCertificate_violation {P : Protocol} {c : Certificate}
    (h : checkCertificate P c = true) :
    runsLeaksBool P (certCfgs c) = true ∨
      authBreakBool P (certCfgs c) (certTrace c) = true := by
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Bool.or_eq_true_iff.mp h.2

/-- **Soundness of the bounded checker.** An accepted certificate is a bounded attack: the complete
public predicate, not an attack plus a length inequality. -/
theorem checkBounded_sound {P : Protocol} {B : Bounds} {c : Certificate}
    (h : checkBounded P B c = true) : BoundedAttack P B := by
  classical
  rw [checkBounded, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hchk, hlen⟩, huniv⟩ := h
  have hruns : Runs P (initCfg P) (certTrace c) (certCfgs c) := by
    have h1 : Runs P c.init (certTrace c) (certCfgs c) :=
      checkSteps_runs P c.steps c.init (checkCertificate_steps hchk)
    rw [beq_iff_eq.mp (checkCertificate_init hchk)] at h1
    exact h1
  have hlen' : (certTrace c).length ≤ B.steps := by
    rw [certTrace, List.length_map]
    exact of_decide_eq_true hlen
  have huniv' : runsInUniverse (certCfgs c) (univ P B) :=
    (runsInUniverseBool_iff _ _).mp huniv
  have hviol := checkCertificate_violation hchk
  rcases hviol with hleak | hbreak
  · rw [BoundedAttack]
    exact ⟨certTrace c, certCfgs c, ⟨hruns, hlen', huniv'⟩,
      Or.inl ((runsLeaksBool_iff P (certCfgs c)).mp hleak)⟩
  · rw [BoundedAttack]
    exact ⟨certTrace c, certCfgs c, ⟨hruns, hlen', huniv'⟩,
      Or.inr ((authBreakBool_iff P (certCfgs c) (certTrace c)).mp hbreak)⟩

/-- The commit-only authentication witness is bounded, and the bounded checker accepts it. -/
theorem auth_bounded :
    checkBounded Regressions.Authentication.P Regressions.Authentication.B
      Regressions.Authentication.c = true := by decide

/-- The transient-pair witness is bounded too - every configuration stays inside the universe even
though an intermediate value does not - so the bounded checker accepts it. -/
theorem bounds_bounded :
    checkBounded Regressions.Bounds.P Regressions.Bounds.B Regressions.Bounds.cert = true := by
  decide

/-! ### The gap the old checker left open -/

/-- A protocol whose session receives a message and then publishes a declared secret. -/
def leakP : Protocol :=
  { roles := [{ acts := [Action.recv 0 0, Action.send 0 (Expr.shrk 0 0)] }]
    sessions := [{ role := 0, self := 0, peer := 0 }]
    agents := [0]
    nonceDomain := []
    compromised := []
    secrets := [Secret.closed (Expr.shrk 0 0)]
    auths := [] }

/-- Three events: derive, deliver, publish. -/
def leakB : Bounds := { steps := 3, rounds := 0 }

/-- The message the attacker builds: a pair of known names. A legal deduction, and outside the
universe of these bounds. -/
def pairOut : Term := Term.pair (Term.agent 0) (Term.agent 0)

/-- The run: deduce the pair, deliver it, and let the session publish the declared secret. -/
def outCert : Certificate :=
  { init := initCfg leakP,
    steps := [{ ev := Ev.ded pairOut, after := succDed (initCfg leakP) pairOut },
              { ev := Ev.act 0 pairOut 0,
                after := succStore (succDed (initCfg leakP) pairOut) 0 0 pairOut },
              { ev := Ev.act 0 pairOut 0,
                after := succSend (succStore (succDed (initCfg leakP) pairOut) 0 0 pairOut)
                  0 (Term.key (Key.shrk 0 0)) }] }

/-- The pair really is outside the universe the bounds generate. -/
theorem pair_not_in_univ : pairOut ∉ univ leakP leakB := by decide

/-- **The old checker accepts it**: every step is a legal transition and the published message is a
declared secret. -/
theorem out_of_universe_accepted_by_old_checker : checkCertificate leakP outCert = true := by
  decide

/-- It is a genuine attack in the unbounded sense. -/
theorem out_of_universe_attack : Attack leakP (certTrace outCert) :=
  checkCertificate_sound outCert out_of_universe_accepted_by_old_checker

/-- **The bounded checker rejects it**: the run leaves the universe, so it is not an answer to the
question "is there an attack inside these bounds". -/
theorem out_of_universe_rejected : checkBounded leakP leakB outCert = false := by decide

/-- The step bound bites too: the same certificate is rejected when the declared bound is shorter
than the run, even though nothing leaves the universe in the first two steps. -/
theorem too_long_rejected :
    checkBounded leakP { steps := 2, rounds := 0 } outCert = false := by decide

end ProtSat.BoundedCert