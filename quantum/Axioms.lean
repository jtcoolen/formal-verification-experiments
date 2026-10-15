/-
Axiom audit of the principal theorems.

Run with:  lake env lean Axioms.lean

The expected output lists only the three standard logical dependencies of Mathlib
(propext, Quot.sound, Classical.choice). There are no project-specific axioms: nothing in
Quantum/ uses sorry, admit, axiom, native_decide or partial.
-/
import Quantum
import Shor

#print axioms Quantum.denote_isUnitary
#print axioms Quantum.checkCertificate_sound
#print axioms Quantum.Opt.optimize_sound
#print axioms Quantum.Opt.greedy_phaseEquivalent
#print axioms Quantum.Examples.soundA
#print axioms Quantum.Examples.soundE
#print axioms Quantum.Examples.soundFG
#print axioms Quantum.Examples.soundJ
#print axioms Quantum.Examples.denotationFG
#print axioms Quantum.BugRegression.c1_to_z
#print axioms Quantum.BugRegression.q_fuse
#print axioms Quantum.BugRegression.crz_twoPi_not_id
#print axioms Quantum.ControlPhase.crz_twoPi_not_phase_one
#print axioms Quantum.ladder_exact
#print axioms Quantum.ladder_saves
#print axioms Quantum.toffoli_constProp_le
#print axioms Quantum.qubitWidth_le
#print axioms Quantum.supports_default
#print axioms Shor.order_dvd
#print axioms Shor.shor_factor
#print axioms Shor.factor_15
#print axioms Shor.rsa_roundtrip_33
#print axioms Shor.ECDLP.recovery
