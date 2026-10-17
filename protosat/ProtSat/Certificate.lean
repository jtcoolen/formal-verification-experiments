/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Operational

/-!
# ProtSat: independent attack certificates (specification sections 7 and 8C)

## What a certificate is

A `Certificate` for a protocol `P` is a *concrete execution*: an initial
configuration (which must equal `ProtSat.initCfg P`) followed by a list of
`CertStep`s, each recording one event `ev : Ev` and the full configuration
`after : Cfg` that the certificate claims results from it.  The configuration
*before* a step is the previous entry (or `init` for the first step), so the
certificate is pure data: it can be serialized, shipped across a network, and
-- most importantly -- checked by a program that knows nothing about how it was
produced.

The checker `checkCertificate P c` is a plain `Bool`-valued computation that
verifies, by direct evaluation:

1. `c.init` is the initial configuration of `P` (`initCfg P`);
2. every step is a genuine transition of the *operational semantics*:
   `relDecide P C s.ev s.after = true`, where `C` is the previous
   configuration.  `relDecide` mirrors each introduction rule of `Rel`
   (`rIdle`, `rDed`, `rFresh`, `rSend`, `rRecv`, `rAssign`, `rCheck`,
   `rSecret`, `rClaim`, `rCommit`) by a Boolean test, and `relDecide_sound`
   proves that a `true` result really yields `Rel P C e C'`;
3. the resulting run violates a declared security property: either some
   visited configuration satisfies the Boolean leak test `leakBool` (a
   declared closed secret, or a declared session-store secret, is in the
   attacker's knowledge -- mirroring `Leak`), or the trace exhibits a `commit`
   with no matching `claim` (mirroring `AuthBreak`).

Because the violation is *recomputed* from the configurations themselves, the
certificate carries nothing that is taken on faith: there is no "witness"
field the checker would have to trust.

## Why checking beats re-solving

The SAT route to an attack is: build the encoding (specification sections
5--6), run a solver, decode a model.  Trusting that result means trusting the
*whole* pipeline: encoding, solver, and decoder.  A certificate shortens the
trusted base to (a) the operational semantics `ProtSat.Operational`, (b) the
small Boolean checker in this file, and (c) the Lean kernel.  Checking is a
linear fold over the step list doing only list membership tests and
configuration comparisons -- asymptotically cheaper than solving -- and each
check of a concrete certificate is a closed `Bool` reduction that the kernel
performs by `decide`.  This module imports `ProtSat.Operational` and *nothing*
from `ProtSat.CNF`, `ProtSat.OneHot`, `ProtSat.Bounded`, `ProtSat.Encode`,
`ProtSat.Clauses`, `ProtSat.Encoding` or `ProtSat.DPLL`: the checker is
independent of the SAT encoding, as specification section 7 requires.

## The one-step deduction test

`rDed` requires `OneStep C.kn t`.  `OneStep` is an inductive `Prop` and is not
executable, so we provide `oneStepBool`, a Boolean test that enumerates the
eleven Dolev-Yao rules over the messages currently in the knowledge base, and
prove `oneStepBool_iff`: `oneStepBool K t = true <-> OneStep K t`.  The forward
direction is the *soundness* of the test (every accepted step is a real rule
instance -- no encryption is broken without its key, no nonce is invented),
the backward direction its *completeness* (every rule instance is accepted).
The constructor/destructor pairs (pairing/projection, encryption/decryption)
are each checked with their real premises; the `certRound` example at the end
exercises the `encS_then_decS` round trip of specification 2.4.

## Main theorems

* `oneStepBool_iff` -- the Boolean deduction test agrees with `OneStep`.
* `relDecide_sound` -- a `true` local decision is a real `Rel` step.
* `relDecide_complete` -- every real `Rel` step decides `true`.
* `checkCertificate_sound` -- an accepted certificate is an `Attack P tr`
  (specification 8C).
* `checkCertificate_authbreak` -- the `AuthBreak` disjunct, stated separately.
* `certificate_of_runs` -- every leaking `Runs` yields an accepted
  certificate (no false rejection of honest proofs).
-/

namespace ProtSat

open Term
open ProtSat.Attacker

/-! ### A Boolean one-step deduction test -/

/-- The *constructor* half of the one-step test: is `t` the conclusion of one
of the six rules whose conclusion has `t`'s own shape (`agent`, `pub`,
`pairI`, `encSI`, `encAI`, `hashI`)?  The two public-information rules have no
premises, so they only inspect the shape of `t`. -/
def oneStepConstructors (K : List Term) (t : Term) : Bool :=
  match t with
  | Term.agent _ => true
  | Term.key (Key.pub _) => true
  | Term.pair x y => decide (x ∈ K) && decide (y ∈ K)
  | Term.encS m k => decide (m ∈ K) && decide (Term.key k ∈ K)
  | Term.encA m _ => decide (m ∈ K)
  | Term.hash m => decide (m ∈ K)
  | _ => false

/-- The *destructor* half of the one-step test: is `t` the conclusion of one of
the four rules `fstE`, `sndE`, `encSD`, `encAD`?  Their premises are messages
*containing* `t` as a component, so we scan the knowledge base: a pair in `K`
yields either component; a symmetric ciphertext in `K` yields its plaintext
only if its key is also in `K`; an asymmetric ciphertext yields its plaintext
only if the matching private key is in `K`. -/
def oneStepDestructors (K : List Term) (t : Term) : Bool :=
  K.any fun u =>
    match u with
    | Term.pair x y => x == t || y == t
    | Term.encS m k => m == t && decide (Term.key k ∈ K)
    | Term.encA m a => m == t && decide (Term.key (Key.priv a) ∈ K)
    | _ => false

/-- `oneStepBool K t`: the executable one-step deduction test.
`oneStepBool K t = true` iff `t` is the conclusion of one instance of one of
the eleven Dolev-Yao rules of `ProtSat.Attacker.OneStep` all of whose premises
lie in `K`.  Its correctness is `oneStepBool_iff` (specification sections 2.4
and 7). -/
def oneStepBool (K : List Term) (t : Term) : Bool :=
  decide (t ∈ K) || (oneStepConstructors K t || oneStepDestructors K t)

/-- **Correctness of the Boolean deduction test** (specification sections 2.4
and 7).  `oneStepBool K t` accepts exactly the one-step conclusions of the
declarative relation `OneStep`: soundness (the forward direction -- nothing the
rules cannot derive is accepted; in particular no encryption is broken without
its key and no nonce is invented) and completeness (the backward direction --
every rule instance is recognized). -/
theorem oneStepBool_iff (K : List Term) (t : Term) :
    oneStepBool K t = true <-> OneStep K t := by
  constructor
  · -- soundness of the Boolean test
    intro h
    rw [oneStepBool, Bool.or_eq_true] at h
    rcases h with hmem | hrest
    · exact OneStep.known (of_decide_eq_true hmem)
    · rw [Bool.or_eq_true] at hrest
      rcases hrest with hcon | hdes
      · -- accepted by a constructor rule
        cases t with
        | agent A => exact OneStep.agent
        | key k =>
            cases k with
            | pub A => exact OneStep.pub
            | shrk a b | priv a => simp [oneStepConstructors] at hcon
        | nonce N => simp [oneStepConstructors] at hcon
        | pair x y =>
            rw [oneStepConstructors] at hcon
            rw [Bool.and_eq_true] at hcon
            rcases hcon with ⟨h1, h2⟩
            exact OneStep.pairI (of_decide_eq_true h1) (of_decide_eq_true h2)
        | encS m k =>
            rw [oneStepConstructors] at hcon
            rw [Bool.and_eq_true] at hcon
            rcases hcon with ⟨h1, h2⟩
            exact OneStep.encSI (of_decide_eq_true h1) (of_decide_eq_true h2)
        | encA m a =>
            rw [oneStepConstructors] at hcon
            exact OneStep.encAI (of_decide_eq_true hcon)
        | hash m =>
            rw [oneStepConstructors] at hcon
            exact OneStep.hashI (of_decide_eq_true hcon)
      · -- accepted by a destructor rule: extract the premise witness from K
        obtain ⟨u, hu, he⟩ := List.any_eq_true.mp hdes
        cases u with
        | agent A | nonce N | key k | hash m => simp at he
        | pair x y =>
            simp only at he
            rw [Bool.or_eq_true] at he
            rcases he with he | he
            · have hx : x = t := beq_iff_eq.mp he
              subst hx
              exact OneStep.fstE hu
            · have hy : y = t := beq_iff_eq.mp he
              subst hy
              exact OneStep.sndE hu
        | encS m k =>
            simp only at he
            rw [Bool.and_eq_true] at he
            rcases he with ⟨h1, h2⟩
            have hm : m = t := beq_iff_eq.mp h1
            subst hm
            exact OneStep.encSD hu (of_decide_eq_true h2)
        | encA m a =>
            simp only at he
            rw [Bool.and_eq_true] at he
            rcases he with ⟨h1, h2⟩
            have hm : m = t := beq_iff_eq.mp h1
            subst hm
            exact OneStep.encAD hu (of_decide_eq_true h2)
  · -- completeness of the Boolean test
    intro h
    induction h with
    | known ht =>
        rw [oneStepBool, Bool.or_eq_true]
        left
        exact decide_eq_true ht
    | agent =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        left
        simp only [oneStepConstructors]
    | pub =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        left
        simp only [oneStepConstructors]
    | pairI hx hy =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        left
        simp only [oneStepConstructors, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hx, hy⟩
    | @fstE x y hp =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        right
        unfold oneStepDestructors
        exact List.any_eq_true.mpr ⟨Term.pair x y, hp, by simp⟩
    | @sndE x y hp =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        right
        unfold oneStepDestructors
        exact List.any_eq_true.mpr ⟨Term.pair x y, hp, by simp⟩
    | encSI hm hk =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        left
        simp only [oneStepConstructors, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hm, hk⟩
    | @encSD m k he hk =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        right
        unfold oneStepDestructors
        exact List.any_eq_true.mpr ⟨Term.encS m k, he, by simp [hk]⟩
    | encAI hm =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        left
        simp only [oneStepConstructors, decide_eq_true_eq]
        exact hm
    | @encAD m a he hk =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        right
        unfold oneStepDestructors
        exact List.any_eq_true.mpr ⟨Term.encA m a, he, by simp [hk]⟩
    | hashI hm =>
        rw [oneStepBool, Bool.or_eq_true]
        right
        rw [Bool.or_eq_true]
        left
        simp only [oneStepConstructors, decide_eq_true_eq]
        exact hm

/-! ### A decidable specification of one transition -/

/-- `relDecide P C e C'`: the Boolean specification of the transition relation
`ProtSat.Rel P C e C'`.  It looks up the current action `P.actionAt q (pcOf C q)`
and checks (i) the enabling condition of the corresponding `Rel` constructor
and (ii) that `C'` is *exactly* the successor configuration the semantics
prescribes (`succDed`, `succStore`, `succSend`, `succAdvance`, or `C` itself).
`relDecide_sound` proves that `true` implies `Rel`; `relDecide_complete`
proves the converse, so the two specifications coincide. -/
def relDecide (P : Protocol) (C : Cfg) (e : Ev) (C' : Cfg) : Bool :=
  match e with
  | Ev.idle => C' == C
  | Ev.ded t => oneStepBool C.kn t && C' == succDed C t
  | Ev.act q m d =>
      match P.actionAt q (pcOf C q) with
      | some (Action.fresh x _) =>
          decide (d ∈ P.nonceDomain) && ! (nonceUsed C d) &&
            C' == succStore C q x (Term.nonce d)
      | some (Action.send _ e') =>
          match Expr.eval e' (storeOf C q) with
          | some t => C' == succSend C q t
          | none => false
      | some (Action.recv _ x) => decide (m ∈ C.kn) && C' == succStore C q x m
      | some (Action.assign x e') =>
          match Expr.eval e' (storeOf C q) with
          | some t => C' == succStore C q x t
          | none => false
      | some (Action.check e1 e2) =>
          match Expr.eval e1 (storeOf C q), Expr.eval e2 (storeOf C q) with
          | some v1, some v2 => v1 == v2 && C' == succAdvance C q
          | _, _ => false
      | some (Action.secret _) => C' == succAdvance C q
      | some (Action.claim _ _ _) => C' == succAdvance C q
      | some (Action.commit _ _ _) => C' == succAdvance C q
      | none => false

/-- **Local soundness of the transition test** (the core step of specification
8C).  If `relDecide P C e C'` evaluates to `true`, then `Rel P C e C'` holds:
each branch of the proof applies exactly the `Rel` constructor that the
corresponding branch of `relDecide` mirrors -- `rIdle`, `rDed`, `rFresh`,
`rSend`, `rRecv`, `rAssign`, `rCheck`, `rSecret`, `rClaim`, `rCommit`. -/
theorem relDecide_sound (P : Protocol) (C C' : Cfg) (e : Ev)
    (h : relDecide P C e C' = true) : Rel P C e C' := by
  cases e with
  | idle =>
      rw [relDecide] at h
      rw [beq_iff_eq] at h
      cases h
      exact Rel.rIdle _ _
  | ded t =>
      rw [relDecide, Bool.and_eq_true] at h
      rcases h with ⟨h1, h2⟩
      rw [beq_iff_eq] at h2
      cases h2
      exact Rel.rDed ((oneStepBool_iff _ _).mp h1)
  | act q m d =>
      rw [relDecide] at h
      cases hA : P.actionAt q (pcOf C q) with
      | none => simp only [hA, Bool.false_eq_true] at h
      | some a =>
          cases a with
          | fresh x _N =>
              simp only [hA] at h
              rw [Bool.and_eq_true] at h
              rcases h with ⟨h12, h3⟩
              rw [Bool.and_eq_true] at h12
              rcases h12 with ⟨h1, h2⟩
              have hn : nonceUsed C d = false := by simpa using h2
              rw [beq_iff_eq] at h3
              cases h3
              exact Rel.rFresh hA (of_decide_eq_true h1) hn
          | send _a e' =>
              cases he : Expr.eval e' (storeOf C q) with
              | none => simp only [hA, he, Bool.false_eq_true] at h
              | some t =>
                  simp only [hA, he] at h
                  rw [beq_iff_eq] at h
                  cases h
                  exact Rel.rSend hA he
          | recv _a x =>
              simp only [hA] at h
              rw [Bool.and_eq_true] at h
              rcases h with ⟨h1, h2⟩
              rw [beq_iff_eq] at h2
              cases h2
              exact Rel.rRecv hA (of_decide_eq_true h1)
          | assign x e' =>
              cases he : Expr.eval e' (storeOf C q) with
              | none => simp only [hA, he, Bool.false_eq_true] at h
              | some t =>
                  simp only [hA, he] at h
                  rw [beq_iff_eq] at h
                  cases h
                  exact Rel.rAssign hA he
          | check e1 e2 =>
              cases h1 : Expr.eval e1 (storeOf C q) with
              | none => simp only [hA, h1, Bool.false_eq_true] at h
              | some v1 =>
                  cases h2 : Expr.eval e2 (storeOf C q) with
                  | none => simp only [hA, h1, h2, Bool.false_eq_true] at h
                  | some v2 =>
                      simp only [hA, h1, h2] at h
                      rw [Bool.and_eq_true] at h
                      rcases h with ⟨hb, hc⟩
                      rw [beq_iff_eq] at hb hc
                      cases hb
                      cases hc
                      exact Rel.rCheck hA h1 h2
          | secret _e' =>
              simp only [hA] at h
              rw [beq_iff_eq] at h
              cases h
              exact Rel.rSecret hA
          | claim _tag _peer _v =>
              simp only [hA] at h
              rw [beq_iff_eq] at h
              cases h
              exact Rel.rClaim hA
          | commit _tag _peer _v =>
              simp only [hA] at h
              rw [beq_iff_eq] at h
              cases h
              exact Rel.rCommit hA

/-- **Local completeness of the transition test.**  Every real step of the
operational semantics is accepted by `relDecide`.  Together with
`relDecide_sound` this says the Boolean test is an exact decision procedure
for one step of `Rel`. -/
theorem relDecide_complete {P : Protocol} {C C' : Cfg} {e : Ev}
    (h : Rel P C e C') : relDecide P C e C' = true := by
  induction h with
  | rIdle => exact beq_iff_eq.mpr rfl
  | rDed hstep =>
      rw [relDecide, (oneStepBool_iff _ _).mpr hstep, Bool.true_and]
      exact beq_iff_eq.mpr rfl
  | rFresh ha hd hn =>
      rw [relDecide]
      simp only [ha, hd, hn]
      exact beq_iff_eq.mpr rfl
  | rSend ha he =>
      rw [relDecide]
      simp only [ha, he]
      exact beq_iff_eq.mpr rfl
  | rRecv ha hm =>
      rw [relDecide]
      simp only [ha, hm]
      exact beq_iff_eq.mpr rfl
  | rAssign ha he =>
      rw [relDecide]
      simp only [ha, he]
      exact beq_iff_eq.mpr rfl
  | rCheck ha h1 h2 =>
      rw [relDecide]
      simp only [ha, h1, h2, Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr rfl, beq_iff_eq.mpr rfl⟩
  | rSecret ha =>
      rw [relDecide]
      simp only [ha]
      exact beq_iff_eq.mpr rfl
  | rClaim ha =>
      rw [relDecide]
      simp only [ha]
      exact beq_iff_eq.mpr rfl
  | rCommit ha =>
      rw [relDecide]
      simp only [ha]
      exact beq_iff_eq.mpr rfl

/-! ### Boolean tests for the security properties -/

/-- `leakBool P C`: the executable version of `ProtSat.Leak P C`.  It is true
when the attacker's knowledge contains the value of a declared *closed*
secret, or when some session `q` holds a value in its store for a declared
*store* secret `(q, x)` and the attacker knows that value.  `leakBool_iff`
proves it equivalent to `Leak`. -/
def leakBool (P : Protocol) (C : Cfg) : Bool :=
  P.closedSecretTerms.any (fun s => decide (s ∈ C.kn))
  || P.secrets.any (fun sc =>
      match sc with
      | Secret.store q x =>
          match sessAt C q with
          | some st =>
              match readVar x st.store with
              | some v => decide (v ∈ C.kn)
              | none => false
          | none => false
      | Secret.closed _ => false)

/-- The Boolean leak test agrees with the declarative `Leak`. -/
theorem leakBool_iff (P : Protocol) (C : Cfg) : leakBool P C = true <-> Leak P C := by
  rw [Leak, leakBool, Bool.or_eq_true]
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨s, hs, hmem⟩ := List.any_eq_true.mp h
      exact Or.inl ⟨s, hs, of_decide_eq_true hmem⟩
    · obtain ⟨sc, hsc, htest⟩ := List.any_eq_true.mp h
      cases sc with
      | closed _e => simp at htest
      | store q x =>
          simp at htest
          cases hq : sessAt C q with
          | none => simp [hq] at htest
          | some st =>
              cases hv : readVar x st.store with
              | none => simp [hq, hv] at htest
              | some v =>
                  simp [hq, hv] at htest
                  exact Or.inr ⟨q, x, v, hsc, by rw [hq]; simp [hv], htest⟩
  · intro h
    rcases h with ⟨s, hs, hmem⟩ | ⟨q, x, v, hsc, hmap, hmem⟩
    · left
      exact List.any_eq_true.mpr ⟨s, hs, decide_eq_true hmem⟩
    · right
      refine List.any_eq_true.mpr ⟨Secret.store q x, hsc, ?_⟩
      cases hq : sessAt C q with
      | none =>
          rw [hq] at hmap
          simp at hmap
      | some st =>
          cases hv : readVar x st.store with
          | none =>
              rw [hq] at hmap
              simp [hv] at hmap
          | some v' =>
              rw [hq] at hmap
              simp [hv] at hmap
              cases hmap
              simp only [hq, hv]
              exact decide_eq_true hmem

/-- `runsLeaksBool P Cs`: the executable version of `ProtSat.runsLeaks P Cs`
(some visited configuration leaks). -/
def runsLeaksBool (P : Protocol) (Cs : List Cfg) : Bool :=
  Cs.any (leakBool P)

/-- The Boolean list test agrees with `runsLeaks`. -/
theorem runsLeaksBool_iff (P : Protocol) (Cs : List Cfg) :
    runsLeaksBool P Cs = true <-> runsLeaks P Cs := by
  induction Cs with
  | nil => simp [runsLeaksBool, runsLeaks]
  | cons C rest ih =>
      rw [runsLeaksBool, List.any_cons, Bool.or_eq_true, runsLeaks]
      constructor
      · rintro (hleak | hrest)
        · exact ⟨C, List.Mem.head _, (leakBool_iff P C).mp hleak⟩
        · obtain ⟨x, hx, hl⟩ := ih.mp hrest
          exact ⟨x, List.Mem.tail _ hx, hl⟩
      · rintro ⟨x, hx, hleak⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · left; exact (leakBool_iff _ _).mpr hleak
        · right; exact ih.mpr ⟨x, hx, hleak⟩

/-- `authBreakBool P Cs tr`: the executable version of `ProtSat.AuthBreak`.
It scans the committed `(tag, peer, value)` triples of the run and returns
`true` when some commit was never claimed. -/
def authBreakBool (P : Protocol) (Cs : List Cfg) (tr : List Ev) : Bool :=
  (commitsOf P Cs tr).any (fun c => ! decide (c ∈ claimsOf P Cs tr))

/-- The Boolean agreement test agrees with `AuthBreak`. -/
theorem authBreakBool_iff (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    authBreakBool P Cs tr = true <-> AuthBreak P Cs tr := by
  unfold authBreakBool AuthBreak
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, h⟩
    have h2 : decide (c ∈ claimsOf P Cs tr) = false := by simpa using h
    exact ⟨c, hc, of_decide_eq_false h2⟩
  · rintro ⟨c, hc, hnotin⟩
    exact ⟨c, hc, by simp [hnotin]⟩

/-! ### Certificates -/

/-- One step of a certificate: the event `ev` and the configuration `after`
that the certificate claims results from it.  The configuration *before* the
step is the previous entry, or `Certificate.init` for the first step; the
checker recomputes the successor from the semantics and compares it against
`after`, so a certificate cannot lie about what a step does. -/
structure CertStep where
  /-- The event: `Ev.idle`, an attacker deduction `Ev.ded t`, or a session
  action `Ev.act q m d`. -/
  ev : Ev
  /-- The configuration after the step. -/
  after : Cfg
  deriving Repr, DecidableEq

/-- An attack certificate: a claimed execution of a protocol.
`init` must be the initial configuration `initCfg P`; `steps` lists one
`CertStep` per transition.  The security violation is *not* a trusted field:
the checker recomputes the leak (or the authentication break) from the
configurations themselves, so a certificate carries no claim that is taken on
faith. -/
structure Certificate where
  /-- The claimed initial configuration (checked against `initCfg P`). -/
  init : Cfg
  /-- The claimed execution steps. -/
  steps : List CertStep
  deriving Repr

/-- The trace of a certificate: the list of its events. -/
def certTrace (c : Certificate) : List Ev := c.steps.map (fun s => s.ev)

/-- The configurations visited by a certificate: the initial one and the
successor recorded after each step. -/
def certCfgs (c : Certificate) : List Cfg := c.init :: c.steps.map (fun s => s.after)

/-- The step checker: a structural fold over the certificate steps (no fuel,
no partiality, no well-founded recursion -- specification 8H).  For each step
it runs `relDecide` from the previous configuration. -/
def checkSteps (P : Protocol) (C : Cfg) : List CertStep -> Bool
  | [] => true
  | s :: rest => relDecide P C s.ev s.after && checkSteps P s.after rest

/-- **The certificate checker** (specification section 7).
`checkCertificate P c = true` iff
* `c.init` is the initial configuration of `P`;
* every step is a `Rel`-sound transition from the previous configuration
  (as decided by `relDecide`); and
* the run violates a security property: some visited configuration leaks a
  declared secret (`leakBool`), or the trace contains a `commit` with no
  matching `claim` (`authBreakBool`).

The whole check is a closed Boolean computation; it invokes no solver and
imports nothing from the SAT encoding. -/
def checkCertificate (P : Protocol) (c : Certificate) : Bool :=
  c.init == initCfg P
    && checkSteps P c.init c.steps
    && (runsLeaksBool P (certCfgs c) || authBreakBool P (certCfgs c) (certTrace c))

/-- A `checkSteps`-accepted step list is a genuine `Runs`: the visited list is
exactly the initial configuration followed by the recorded successors.  Built
by induction over the step list using `relDecide_sound`. -/
theorem checkSteps_runs (P : Protocol) : ∀ (steps : List CertStep) (C : Cfg),
    checkSteps P C steps = true ->
    Runs P C (steps.map (fun s => s.ev)) (C :: steps.map (fun s => s.after)) := by
  intro steps
  induction steps with
  | nil => intro C _; exact Runs.nil P C
  | cons st rest ih =>
      intro C h
      rw [checkSteps, Bool.and_eq_true] at h
      rcases h with ⟨h1, h2⟩
      exact Runs.cons (relDecide_sound P C st.after st.ev h1) (ih st.after h2)

/-- **Soundness of the certificate checker** (specification 8C).  An accepted
certificate yields an `Attack`: its event list is a valid trace from
`initCfg P` (by `relDecide_sound` through `checkSteps_runs`) and the run
either leaks a declared secret on some visited configuration (`leakBool_iff`,
`runsLeaksBool_iff`) or breaks non-injective agreement (`authBreakBool_iff`). -/
theorem checkCertificate_sound {P : Protocol} (c : Certificate)
    (h : checkCertificate P c = true) : Attack P (certTrace c) := by
  rw [checkCertificate, Bool.and_eq_true] at h
  rcases h with ⟨h12, h3⟩
  rw [Bool.and_eq_true] at h12
  rcases h12 with ⟨h1, h2⟩
  rw [Bool.or_eq_true] at h3
  have hi : c.init = initCfg P := beq_iff_eq.mp h1
  have hruns : Runs P (initCfg P) (certTrace c) (certCfgs c) := by
    rw [← hi]
    exact checkSteps_runs P c.steps c.init h2
  refine ⟨certCfgs c, hruns, ?_⟩
  rcases h3 with h3 | h3
  · left
    exact (runsLeaksBool_iff P (certCfgs c)).mp h3
  · right
    exact (authBreakBool_iff P (certCfgs c) (certTrace c)).mp h3

/-- **Authentication variant of the checker's soundness** (specification 8C,
second disjunct).  If the steps are valid and the trace exhibits an un-matched
commit, the trace is an attack via `AuthBreak` -- the form the Lowe attack on
Needham-Schroeder takes (specification 9.5). -/
theorem checkCertificate_authbreak {P : Protocol} (c : Certificate)
    (h1 : (c.init == initCfg P) = true)
    (h2 : checkSteps P c.init c.steps = true)
    (h3 : authBreakBool P (certCfgs c) (certTrace c) = true) :
    Attack P (certTrace c) :=
  checkCertificate_sound c (by
    rw [checkCertificate, h1, h2, Bool.true_and, Bool.true_and, Bool.or_eq_true]
    right
    exact h3)

/-- Auxiliary for `certificate_of_runs`: read a `Runs` proof off as a step
list that the step checker accepts.  Proved by induction over `Runs` using
`relDecide_complete`. -/
theorem runs_steps (P : Protocol) : ∀ {C : Cfg} {tr : List Ev} {Cs : List Cfg},
    Runs P C tr Cs ->
    ∃ (steps : List CertStep),
      (steps.map (fun s => s.ev)) = tr
      ∧ (C :: steps.map (fun s => s.after)) = Cs
      ∧ checkSteps P C steps = true := by
  intro C tr Cs h
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | @cons Cc C' e tr' rest' hrel hr ih =>
      obtain ⟨steps, h1, h2, h3⟩ := ih
      refine ⟨⟨e, C'⟩ :: steps, ?_, ?_, ?_⟩
      · simp [h1]
      · simp [h2]
      · rw [checkSteps, Bool.and_eq_true]
        exact ⟨relDecide_complete hrel, h3⟩

/-- Every `Rel`-valid run of `P` from `initCfg P` that leaks produces a
certificate the checker accepts: the step list is read off the run, every
transition passes `relDecide` (`relDecide_complete`), and the leak is found by
the checker itself.  This is the "no false rejection of honest proofs"
direction. -/
theorem certificate_of_runs {P : Protocol} {tr : List Ev} {Cs : List Cfg}
    (h : Runs P (initCfg P) tr Cs) (hl : runsLeaks P Cs) :
    ∃ (c : Certificate), checkCertificate P c = true ∧ certTrace c = tr := by
  obtain ⟨steps, h1, h2, h3⟩ := runs_steps P h
  refine ⟨⟨initCfg P, steps⟩, ?_, h1⟩
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨beq_iff_eq.mpr rfl, h3⟩, ?_⟩
  rw [Bool.or_eq_true]
  left
  rw [certCfgs, h2]
  exact (runsLeaksBool_iff P Cs).mpr hl

/-! ### Executable examples -/

namespace Examples

/-! #### A protocol whose first role leaks a long-term key through a pair -/

/-- `pClear`: role 0 (agent 0) sends the pair ⟨agent 0, K(0,1)⟩ to agent 1
in the clear; the long-term key `K(0,1)` is declared secret.  The attacker
observes the pair (published by the send) and projects the key out of it
(rule `sndE`).  Two steps suffice. -/
def pClear : Protocol :=
  { roles :=
      [ { acts := [Action.send 1 (Expr.pair (Expr.agent 0) (Expr.shrk 0 1))] },
        { acts := [Action.secret (Expr.shrk 0 1)] } ]
  , sessions := [ { role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 } ]
  , agents := [0, 1]
  , nonceDomain := []
  , compromised := []
  , secrets := [Secret.closed (Expr.shrk 0 1)]
  , auths := [] }

/-- The initial attacker knowledge of `pClear`: the two agent names and the
two public keys; nothing is compromised. -/
def K0 : List Term :=
  [Term.agent 0, Term.agent 1, Term.key (Key.pub 0), Term.key (Key.pub 1)]

/-- The initial configuration of `pClear`, written out as data. -/
def C0 : Cfg :=
  { sess := [{ pc := 0, store := [] }, { pc := 0, store := [] }], kn := K0 }

/-- After the send: session 0 has advanced and the pair is published. -/
def C1 : Cfg :=
  { sess := [{ pc := 1, store := [] }, { pc := 0, store := [] }]
  , kn := K0 ++ [Term.pair (Term.agent 0) (Term.key (Key.shrk 0 1))] }

/-- After the projection: the attacker has split the pair and holds the
secret key. -/
def C2 : Cfg :=
  { sess := C1.sess, kn := C1.kn ++ [Term.key (Key.shrk 0 1)] }

/-- The two-step attack certificate on `pClear`: a send followed by a
`sndE` deduction.  The configurations are written out literally, so the
certificate is pure data and the checker recomputes every successor. -/
def certClear : Certificate :=
  { init := initCfg pClear
  , steps :=
      [ { ev := Ev.act 0 (Term.agent 0) 0, after := C1 },
        { ev := Ev.ded (Term.key (Key.shrk 0 1)), after := C2 } ] }

/-- The checker accepts `certClear`: a closed `decide` evaluation of the whole
pipeline (initial configuration, both transitions, the leak). -/
theorem checkClear : checkCertificate pClear certClear = true := by decide

/-- Hence `pClear` is attacked: the certificate trace is a valid `Runs` from
`initCfg pClear` that leaks the declared secret. -/
theorem attackClear : Attack pClear (certTrace certClear) :=
  checkCertificate_sound (P := pClear) certClear (by decide)

/-! #### A protocol leaking a fresh nonce through symmetric decryption -/

/-- `pEnc`: role 0 generates a fresh nonce `Na` (value 0 from the nonce
domain) and sends its symmetric encryption {Na}_K(0,1) to agent 1.  Agent 1
is compromised, so the attacker holds `K(0,1)` and decrypts.  The declared
secret is the nonce `Na`.  This exercises `rFresh`, `rSend` and the symmetric
destructor `encSD`. -/
def pEnc : Protocol :=
  { roles :=
      [ { acts := [Action.fresh 0 0, Action.send 1 (Expr.encS (Expr.var 0) (Expr.shrk 0 1))] },
        { acts := [Action.secret (Expr.nonce 0)] } ]
  , sessions := [ { role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 } ]
  , agents := [0, 1]
  , nonceDomain := [0]
  , compromised := [1]
  , secrets := [Secret.closed (Expr.nonce 0)]
  , auths := [] }

/-- The initial configuration of `pEnc`: the attacker holds the public names,
the public keys, and -- because agent 1 is compromised -- `priv 1` and every
shared key involving agent 1, in particular `K(0,1)`. -/
def D0 : Cfg :=
  { sess := [{ pc := 0, store := [] }, { pc := 0, store := [] }], kn := pEnc.initKn }

/-- After the fresh step: session 0 stores `nonce 0` under variable 0. -/
def D1 : Cfg :=
  { sess := [{ pc := 1, store := [(0, Term.nonce 0)] }, { pc := 0, store := [] }]
  , kn := pEnc.initKn }

/-- After the send: the ciphertext {Na}_K(0,1) is published. -/
def D2 : Cfg :=
  { sess := [{ pc := 2, store := [(0, Term.nonce 0)] }, { pc := 0, store := [] }]
  , kn := pEnc.initKn ++ [Term.encS (Term.nonce 0) (Key.shrk 0 1)] }

/-- After the decryption step: the attacker holds the secret nonce. -/
def D3 : Cfg :=
  { sess := D2.sess, kn := D2.kn ++ [Term.nonce 0] }

/-- The three-step attack certificate on `pEnc`. -/
def certEnc : Certificate :=
  { init := initCfg pEnc
  , steps :=
      [ { ev := Ev.act 0 (Term.agent 0) 0, after := D1 },
        { ev := Ev.act 0 (Term.agent 0) 0, after := D2 },
        { ev := Ev.ded (Term.nonce 0), after := D3 } ] }

/-- The checker accepts `certEnc`. -/
theorem checkEnc : checkCertificate pEnc certEnc = true := by decide

/-- Hence `pEnc` is attacked. -/
theorem attackEnc : Attack pEnc (certTrace certEnc) :=
  checkCertificate_sound (P := pEnc) certEnc (by decide)

/-- A certificate whose deduction steps use the symmetric *constructor* and
then the symmetric *destructor* -- the `encS_then_decS` round trip of
specification 2.4, checked rule by rule: the attacker re-encrypts the
captured ciphertext under the compromised key (`encSI`), strips one layer
(`encSD`), then strips the other (`encSD`) to recover the nonce. -/
def certRound : Certificate :=
  { init := initCfg pEnc
  , steps :=
      [ { ev := Ev.act 0 (Term.agent 0) 0, after := D1 },
        { ev := Ev.act 0 (Term.agent 0) 0, after := D2 },
        { ev := Ev.ded (Term.encS (Term.encS (Term.nonce 0) (Key.shrk 0 1)) (Key.shrk 0 1))
        , after := { sess := D2.sess
                   , kn := D2.kn ++
                       [Term.encS (Term.encS (Term.nonce 0) (Key.shrk 0 1)) (Key.shrk 0 1)] } },
        { ev := Ev.ded (Term.encS (Term.nonce 0) (Key.shrk 0 1))
        , after := { sess := D2.sess
                   , kn := D2.kn ++
                       [Term.encS (Term.encS (Term.nonce 0) (Key.shrk 0 1)) (Key.shrk 0 1),
                        Term.encS (Term.nonce 0) (Key.shrk 0 1)] } },
        { ev := Ev.ded (Term.nonce 0)
        , after := { sess := D2.sess
                   , kn := D2.kn ++
                       [Term.encS (Term.encS (Term.nonce 0) (Key.shrk 0 1)) (Key.shrk 0 1),
                        Term.encS (Term.nonce 0) (Key.shrk 0 1), Term.nonce 0] } } ] }

/-- The constructor/destructor round trip is accepted by the checker. -/
theorem checkRound : checkCertificate pEnc certRound = true := by decide

/-- Hence the round-trip trace is an attack. -/
theorem attackRound : Attack pEnc (certTrace certRound) :=
  checkCertificate_sound (P := pEnc) certRound (by decide)

/-! #### A store-secret leak -/

/-- `pStore`: role 0 generates a fresh nonce and sends it in the clear; the
declared secret is the *store* secret "(session 0, variable 0)".  This
exercises the second disjunct of `Leak`/`leakBool`. -/
def pStore : Protocol :=
  { roles :=
      [ { acts := [Action.fresh 0 0, Action.send 1 (Expr.var 0)] },
        { acts := [] } ]
  , sessions := [ { role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 } ]
  , agents := [0, 1]
  , nonceDomain := [0]
  , compromised := []
  , secrets := [Secret.store 0 0]
  , auths := [] }

/-- The store-secret attack certificate: fresh, then send. -/
def certStore : Certificate :=
  { init := initCfg pStore
  , steps :=
      [ { ev := Ev.act 0 (Term.agent 0) 0
        , after := { sess := [{ pc := 1, store := [(0, Term.nonce 0)] },
                              { pc := 0, store := [] }]
                   , kn := pStore.initKn } },
        { ev := Ev.act 0 (Term.agent 0) 0
        , after := { sess := [{ pc := 2, store := [(0, Term.nonce 0)] },
                              { pc := 0, store := [] }]
                   , kn := pStore.initKn ++ [Term.nonce 0] } } ] }

/-- The checker finds the store-secret leak. -/
theorem checkStore : checkCertificate pStore certStore = true := by decide

/-- Hence `pStore` is attacked. -/
theorem attackStore : Attack pStore (certTrace certStore) :=
  checkCertificate_sound (P := pStore) certStore (by decide)

/-! #### An authentication-break certificate (no secret leak) -/

/-- `pAuth`: role 0 commits to having run the protocol with agent 1 on the
value `agent 0`, but no role ever claims.  The secrecy set is empty, so the
violation is purely an `AuthBreak` -- the checker's second disjunct. -/
def pAuth : Protocol :=
  { roles :=
      [ { acts := [Action.commit 0 (Expr.agent 1) (Expr.agent 0)] },
        { acts := [] } ]
  , sessions := [ { role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 } ]
  , agents := [0, 1]
  , nonceDomain := []
  , compromised := []
  , secrets := []
  , auths := [{ tag := 0 }] }

/-- A one-step certificate: session 0 commits; the commit has no matching
claim, so the run breaks agreement. -/
def certAuth : Certificate :=
  { init := initCfg pAuth
  , steps :=
      [ { ev := Ev.act 0 (Term.agent 0) 0
        , after := { sess := [{ pc := 1, store := [] }, { pc := 0, store := [] }]
                   , kn := pAuth.initKn } } ] }

/-- The checker accepts the authentication-break certificate (no leak is
required). -/
theorem checkAuth : checkCertificate pAuth certAuth = true := by decide

/-- Hence `pAuth` is attacked via the `AuthBreak` disjunct. -/
theorem attackAuth : Attack pAuth (certTrace certAuth) :=
  checkCertificate_sound (P := pAuth) certAuth (by decide)

/-! #### Mutated certificates the checker rejects -/

/-- A certificate claiming the send step left the configuration *unchanged*:
the recorded successor is not the successor the semantics prescribes, so
`relDecide` rejects the step. -/
def certBadSucc : Certificate :=
  { init := initCfg pClear
  , steps := [ { ev := Ev.act 0 (Term.agent 0) 0, after := C0 } ] }

/-- The checker rejects the wrong-successor certificate. -/
theorem rejectBadSucc : checkCertificate pClear certBadSucc = false := by decide

/-- A certificate whose deduction step claims the attacker can produce a
nonce it was never told about: the `ded` premise is missing, so
`oneStepBool` rejects it (this is `Attacker.nonce_not_deducible` at work). -/
def certBadDed : Certificate :=
  { init := initCfg pClear
  , steps :=
      [ { ev := Ev.act 0 (Term.agent 0) 0, after := C1 },
        { ev := Ev.ded (Term.nonce 9)
        , after := { sess := C1.sess, kn := C1.kn ++ [Term.nonce 9] } } ] }

/-- The checker rejects the deduction with a missing premise. -/
theorem rejectBadDed : checkCertificate pClear certBadDed = false := by decide

/-- A certificate of a run that never leaks: the single send step is a *valid*
transition, but the secret key only occurs inside a pair, never as a known
message, and there is no authentication event -- so the violation check fails. -/
def certNoLeak : Certificate :=
  { init := initCfg pClear
  , steps := [ { ev := Ev.act 0 (Term.agent 0) 0, after := C1 } ] }

/-- The checker rejects a valid run that violates nothing. -/
theorem rejectNoLeak : checkCertificate pClear certNoLeak = false := by decide

end Examples

end ProtSat
