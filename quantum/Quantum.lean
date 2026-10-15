/-
A formally verified, proof-producing quantum circuit optimizer.

* Quantum/Angle.lean        exact symbolic angles (rational + rational*pi), no floating point
* Quantum/Syntax.lean       qubit-indexed circuit syntax, gate inverses
* Quantum/Gates.lean        the 2x2 / 4x4 gate matrices and their exact identities
* Quantum/Embed.lean        embedding a gate into an n-qubit register
* Quantum/Rotations.lean    Rz / Rx / Ry / CRz with exact angle semantics
* Quantum/Semantics.lean    denote : Circuit n -> Operator n, unitarity, gate actions
* Quantum/Equivalence.lean  equivalence modulo global phase
* Quantum/Contexts.lean     sequential contexts and contextual congruence
* Quantum/Rewrites.lean     the verified rewrite library (34 rules)
* Quantum/Certificates.lean the independent executable certificate checker
* Quantum/Cost.lean         gate count / two-qubit count / T count, lexicographic policy
* Quantum/QuantumEGraph.lean OptiSat adapter: e-nodes, phase quotient, extraction instance
* Quantum/Optimizer.lean    bounded equality saturation + certificate synthesis
* Quantum/ControlPhase.lean why global phase must not be moved under a control
* Quantum/Examples.lean     the machine-checked examples A-J
* Quantum/BugRegression.lean adversarial regression tests (must all be rejected)
-/
import Quantum.Syntax
import Quantum.Angle
import Quantum.Gates
import Quantum.Embed
import Quantum.Rotations
import Quantum.Semantics
import Quantum.Equivalence
import Quantum.Contexts
import Quantum.Rewrites
import Quantum.Certificates
import Quantum.Cost
import Quantum.QuantumEGraph
import Quantum.Optimizer
import Quantum.ControlPhase
import Quantum.Examples
import Quantum.BugRegression
import Quantum.Correctness
