# Symbolic protocol verification, bounded model checking and verified SAT solvers

Prior art for the ProtSat project (specification: a formally verified, proof-producing
SAT-based cryptographic protocol analyser in Lean 4).

## The protocol and attacker model

* **Dolev-Yao** - D. Dolev, A. Yao, *On the Security of Public Key Protocols*, IEEE
  Transactions on Information Theory 29(2), 1983.  The perfect-cryptography algebra
  and the omniscient network attacker.  Our inductive relation
  `ProtSat.Attacker.Ded` is exactly their deduction judgement (replay, pairing,
  projection, encryption/decryption, hashing), plus the standard explicit
  public-key/private-key constructors.
* **Needham-Schroeder** - R. Needham, M. Schroeder, *Using encryption for
  authentication in large networks of computers*, CACM 21(12), 1978.  Section 9.4
  models the original public-key protocol.
* **Lowe's attack and the fix** - G. Lowe, *Breaking and fixing a major
  security flaw*, IJIT 2(2), 2003.  The attack is a failure of *non-injective
  agreement*: B commits on a triple that A never claimed, which is exactly the
  property `ProtSat.Operational.AuthBreak` formalises.  Sections 9.5 and 9.6
  model the vulnerable protocol and the corrected one.
* **Inductive approach** - L. Paulson, *The Inductive Approach to Verifying Cryptographic
  Protocols*, JCS 1997, and the Isabelle `inductive` event model.  Our
  `Runs`/`Rel` presentation follows the same shape (inductive traces, inductive
  attacker), but the attacker's steps are made *explicit events* so that a bound on
  the number of steps bounds the attacker's derivation depth - which is what makes
  the SAT encoding complete for the traces it claims to cover.
* **Subterm property / decidability** - M. Burrell, F. Dupressoir, B. Warinschi,
  *Fundamental limits of verification with indistinguishability* and, for the
  symbolic side, A. Weber, M. Kaminski, *Inductive rewriting* / J.-P. Boudet,
  H. Comon, *Diophantine equations with a set of unknown terms*, and the
  "tight proofs" argument: for subterm-convergent theories every deduction has a
  derivation whose intermediate terms are subterms of the initial knowledge and the
  goal.  We do **not** reprove the subterm property; instead `ProtSat.Attacker`
  states completeness *relative to the finite universe* (specification section 2.2)
  and adds `ded_dedIn`: every derivation lives inside *some* finite universe, which
  is the property the analyser actually needs.

## Bounded model checking of protocols

* **Comon-Korshev** - H. Comon, V. Cortier, *Tree automata with constraints: an
  application to cryptographic protocols*, JCS 2008; and V. Cortier, B. Warinschi
  surveys.  BMC over a finite set of "illustrations" of the attacker's recipes.
* **Rushby's Brute** - J. Rushby, *New techniques for the model-checking of security
  protocols*, FTRFT 2004 / the Brute tool: encode a bounded number of sessions and
  steps as a propositional formula and hand it to a SAT solver.  This is the design
  our section 5 follows: state variables per step, one-hot encodings of finite-domain
  components, Tseitin clauses for the transition relation, and a violation clause.
* **Gavare et al.**, *SAT-based bounded model checking for security protocols* and the
  MSAT/Clifford-Raftery line: the same recipe, with the message universe as an
  explicit parameter.  Our `ProtSat.Bounded` makes the universe, the depth bound and
  the session/step bounds parameters of the theorem statements, so the
  bounded-safety / unbounded-security distinction (specification section 11) is
  impossible to hide.
* **Why bounded safety is not security** - the standard caveat, stated explicitly in
  the README: SAFE means "no attack with at most S sessions, L steps and messages of
  depth at most D", and the completeness theorem is proved *relative to that universe*.

## Verified SAT solvers

* **Aguillon, Bayer, Benzmüller, Herbrand, et al.**, *Verified (Model) Checking*, and
  the Coq DPLL developments: **Ben Ammar, Pichon-Pharabod, Dayres, Scherrer,
  Rey, Müller, ** *Verified SAT and SMT solving*, CPP 2017 (the Coq verified DPLL
  solver of Rey et al. is the closest template): unit propagation with a
  soundness lemma, branching on the variable list, termination by the number of
  remaining variables, and the two theorems "SAT implies a model" and "UNSAT implies
  unsatisfiable".
* **Harrison**, *Handbook of practical logic and automated reasoning*, chap. on DPLL:
  the same proof structure in HOL Light.
* **LeanSMT / Mathlib's `simp`-based SAT**: Mathlib has no verified DPLL solver we
  could reuse, hence ProtSat.DPLL.
* **OptiSat (LambdaSat)** - the equality-saturation engine vendored in
  `quantum/LambdaSat` and documented in [optisat.md](optisat.md) is *not* a SAT
  solver (it is e-graphs + ILP extraction), but its architecture is the template this
  repository uses again here: an unverified search proposes a witness, an independent
  decidable checker validates it, and only the checker is inside the trust boundary.
  See `LambdaSat/ILPCheck.lean` for the analogue of `ProtSat/Certificate.lean`.

## Positioning of ProtSat

The specification's principal objective is the *correspondence* between symbolic
protocol attacks and satisfying assignments of the generated formula.  The pieces:

| theorem | specification | module |
|---|---|---|
| encoding soundness | 8A | ProtSat.Encode |
| encoding completeness | 8B | ProtSat.Encode |
| certificate soundness | 8C | ProtSat.Certificate |
| solver soundness | 8D | ProtSat.DPLL |
| solver completeness | 8E | ProtSat.DPLL |
| end-to-end attack soundness | 8F | ProtSat.Analyzer |
| end-to-end bounded safety | 8G | ProtSat.Analyzer |
| termination | 8H | each module |
