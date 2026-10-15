/-
Shor's algorithm, classically verified.

* Shor/Arith.lean - modular exponentiation, the multiplicative order as a minimum over an
  explicit finite set, order_spec / order_min / order_dvd, and a Chinese-remainder combination
  principle;
* Shor/RSA.lean - the order-to-factor lemma (shor_factor), the square root of one produced by an
  even order, fully verified concrete factorizations of 15 and 21, and exhaustive RSA round-trip
  checks;
* Shor/ECDLP.lean - the elliptic-curve group law instance and the discrete-log recovery.

The quantum half (the circuits that produce the period) lives in the Quantum package: the same
deeply embedded circuit language, the same matrix semantics, and the same certificate checker,
so any optimization applied to it is certified in exactly the same sense.
-/
import Shor.Arith
import Shor.RSA
import Shor.ECDLP
import Shor.QFT
