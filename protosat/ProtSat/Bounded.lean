/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Operational

/-!
# ProtSat: bounded execution semantics (specification section 4)

## What "bounded" means here, precisely

Four independent bounds are made explicit and are parameters of every definition in
this module:

* Bounds.steps  - L, the number of events in an analysed execution.  Because the
  attacker's deductions are *events* (Ev.ded), L also bounds the depth of the attacker
  derivations the model can represent.  This is not a limitation hidden in an
  implementation detail: the completeness theorem (specification 8B) is stated for
  traces of at most L events, and the README says so in plain words.
* Bounds.rounds - the number of constructor-closure rounds applied to the seed set,
  which bounds the depth of messages the attacker may build (see Term.depth).
* the finite agent domain P.agents and the finite nonce domain P.nonceDomain.

The analysed execution space is then: configurations whose messages all lie in the
universe univ P B, reachable from initCfg P by at most Bounds.steps events.  The
predicate BoundedAttack spells that out, and it is the exact object the SAT encoding of
ProtSat.Encode is proved equivalent to (specification 8A/8B).

## The universe

The seed set is *derived from the protocol*, not guessed:

* every agent name, every nonce value of the domain, every key the environment
  mentions (public keys, private keys, and the symmetric keys between domain agents);
* the attacker's initial knowledge P.initKn;
* the declared closed secrets P.closedSecretTerms;
* for every session and every program counter, the value of every subexpression of the
  action there, evaluated in a *placeholder* store that gives each session variable a
  distinct reserved nonce value.  This is what puts the shapes of the messages the
  protocol can exchange (encrypted challenges, pairs, hashes) into the universe without
  knowing the run.

The seeds are then closed under subterms (so that every premise of a rule instance
whose conclusion is in the universe is also in the universe - the property the
attacker-completeness proof needs) and under Bounds.rounds constructor-closure steps.

Everything here is a List with eraseDups, so the universe is computable and its size is
what drives the size of the generated CNF.
-/

namespace ProtSat.Bounded

open ProtSat Term

/-! ### The bounds record -/

/-- The bounds of a bounded model checking run (specification section 4). -/
structure Bounds where
  /-- L: maximum number of events in an analysed execution. -/
  steps : Nat
  /-- Number of constructor-closure rounds over the seed set: bounds message depth. -/
  rounds : Nat
  deriving Repr, DecidableEq

/-! ### List-based subterms -/

/-- The inclusive subterm list of a message (the List counterpart of Term.subterms;
lists are what the executable universe is built from). -/
def subtermsL : Term -> List Term
  | Term.agent A => [Term.agent A]
  | Term.nonce N => [Term.nonce N]
  | Term.key k => [Term.key k]
  | Term.pair x y => Term.pair x y :: (subtermsL x ++ subtermsL y)
  | Term.encS m k => Term.encS m k :: (subtermsL m ++ [Term.key k])
  | Term.encA m a => Term.encA m a :: (subtermsL m ++ [Term.agent a])
  | Term.hash m => Term.hash m :: subtermsL m

/-- Subterms are transitive: a subterm of a subterm is a subterm. -/
theorem subtermsL_subtermsL : ∀ {t u : Term}, u ∈ subtermsL t -> subtermsL u ⊆ subtermsL t := by
  intro t
  induction t with
  | agent A | nonce N | key k =>
      intro u h
      simp only [subtermsL, List.mem_singleton] at h
      subst h
      exact List.Subset.refl _
  | pair x y ihx ihy =>
      intro u h
      simp only [subtermsL] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact List.Subset.refl _
      · rcases List.mem_append.mp h with h | h
        · exact List.Subset.trans (ihx h) (by
            intro z hz; simp [List.mem_append, hz])
        · exact List.Subset.trans (ihy h) (by
            intro z hz; simp [List.mem_append, List.mem_append, hz])
  | encS m k ih =>
      intro u h
      simp only [subtermsL] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact List.Subset.refl _
      · rcases List.mem_append.mp h with h | h
        · exact List.Subset.trans (ih h) (by intro z hz; simp [List.mem_append, hz])
        · obtain rfl := List.mem_singleton.mp h
          intro z hz
          simp only [subtermsL, List.mem_singleton] at hz
          subst hz
          simp [subtermsL, List.mem_append]
  | encA m a ih =>
      intro u h
      simp only [subtermsL] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact List.Subset.refl _
      · rcases List.mem_append.mp h with h | h
        · exact List.Subset.trans (ih h) (by intro z hz; simp [List.mem_append, hz])
        · obtain rfl := List.mem_singleton.mp h
          intro z hz
          simp only [subtermsL, List.mem_singleton] at hz
          subst hz
          simp [subtermsL, List.mem_append]
  | hash m ih =>
      intro u h
      simp only [subtermsL] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact List.Subset.refl _
      · exact List.Subset.trans (ih h) (by intro z hz; simp [List.mem_append, hz])

/-- Every message is one of its own subterms. -/
theorem mem_subtermsL (t : Term) : t ∈ subtermsL t := by
  cases t <;> simp [subtermsL]

/-- The subterm closure of a list of messages. -/
def subtermClosureL (S : List Term) : List Term := (S.flatMap subtermsL).eraseDups

theorem mem_subtermClosureL {S : List Term} {t : Term} (h : t ∈ S) : t ∈ subtermClosureL S :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨t, h, mem_subtermsL t⟩)

/-- **The universe is subterm-closed.**  Every premise of a rule instance whose
conclusion is in the closure is itself in the closure. -/
theorem subtermClosureL_closed {S : List Term} {t u : Term}
    (ht : t ∈ subtermClosureL S) (hu : u ∈ subtermsL t) : u ∈ subtermClosureL S := by
  have ht' : t ∈ S.flatMap subtermsL := List.mem_eraseDups.mp ht
  obtain ⟨s, hs, hts⟩ := List.mem_flatMap.mp ht'
  refine List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨s, hs, subtermsL_subtermsL hts hu⟩)

/-! ### The universe -/

/-- The keys the universe is closed under: every public key of the domain, every
private key of the domain, and every symmetric key between domain agents. -/
def domainKeys (ag : List Agent) : List Key :=
  (ag.map Key.pub) ++ (ag.map Key.priv) ++ (ag.flatMap fun a => ag.map fun b => Key.shrk a b)

/-- One constructor-closure round over a list of messages. -/
def closeOne (ag : List Agent) (ks : List Key) (U : List Term) : List Term :=
  (U ++
    (U.flatMap fun x => U.map fun y => Term.pair x y) ++
    (U.flatMap fun m => ks.map fun k => Term.encS m k) ++
    (U.flatMap fun m => ag.map fun a => Term.encA m a) ++
    (U.map fun m => Term.hash m)).eraseDups

theorem mem_closeOne {ag : List Agent} {ks : List Key} {U : List Term} {t : Term}
    (h : t ∈ U) : t ∈ closeOne ag ks U :=
  List.mem_eraseDups.mpr (by
    simp only [closeOne, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl h))))

/-- Iterating a monotone-inclusion-preserving function keeps every original element. -/
theorem iterate_mem {f : List Term -> List Term} (hf : ∀ (U : List Term) t, t ∈ U -> t ∈ f U) :
    ∀ (n : Nat) (U : List Term) t, t ∈ U -> t ∈ f^[n] U := by
  intro n
  induction n with
  | zero => intro U t h; simpa using h
  | succ n ih =>
      intro U t h
      rw [Function.iterate_succ_apply']
      exact hf _ _ (ih U t h)

/-- A placeholder store for session q: each variable the session uses is bound to a
distinct reserved nonce value, so evaluating the protocol's expressions yields the
*shapes* of the messages exchanged. -/
def placeholderStore (P : Protocol) (q : Nat) : List (Var × Term) :=
  (P.sessionVars q).zip ((P.sessionVars q).map fun x => Term.nonce (100000 + 1000 * q + x))

/-- The messages an action can mention: the values of all its subexpressions, evaluated
in the placeholder store, plus the key and name constants it writes literally. -/
def actionSeedTerms (P : Protocol) (q pc : Nat) : List Term :=
  match P.actionAt q pc with
  | none => []
  | some a =>
      let es : List Expr :=
        match a with
        | Action.fresh _ _ => []
        | Action.send _ e => Expr.subexpressions e
        | Action.recv _ _ => []
        | Action.assign _ e => Expr.subexpressions e
        | Action.check e1 e2 => Expr.subexpressions e1 ++ Expr.subexpressions e2
        | Action.secret e => Expr.subexpressions e
        | Action.claim _ peer v => Expr.subexpressions peer ++ Expr.subexpressions v
        | Action.commit _ peer v => Expr.subexpressions peer ++ Expr.subexpressions v
      (es.filterMap fun e => Expr.eval e (placeholderStore P q))
        ++ (es.filterMap fun e => match e with
            | Expr.shrk a b => some (Term.key (Key.shrk a b))
            | Expr.pubk a => some (Term.key (Key.pub a))
            | Expr.privk a => some (Term.key (Key.priv a))
            | Expr.agent A => some (Term.agent A)
            | Expr.nonce N => some (Term.nonce N)
            | _ => none)

/-- The seed set of the universe: atoms, initial knowledge, secrets, and the shapes of
all messages the protocol's actions can mention. -/
def seeds (P : Protocol) : List Term :=
  (P.agents.map Term.agent)
    ++ (P.nonceDomain.map Term.nonce)
    ++ (domainKeys P.agents |>.map Term.key)
    ++ P.initKn
    ++ P.closedSecretTerms
    ++ ((List.range P.sessions.length).flatMap fun q =>
          (List.range (P.roleLen q)).flatMap fun pc => actionSeedTerms P q pc)

/-- **The universe of a protocol under the given bounds** (specification section 4:
"explicitly define the relationship between these bounds and the analyzed execution
space").  Subterm-closed, and closed under Bounds.rounds constructor rounds. -/
def univ (P : Protocol) (B : Bounds) : List Term :=
  ((fun U => closeOne P.agents (domainKeys P.agents) U)^[B.rounds]
    (subtermClosureL (seeds P))).eraseDups

theorem mem_univ_of_mem {P : Protocol} {B : Bounds} {t : Term}
    (h : t ∈ subtermClosureL (seeds P)) : t ∈ univ P B := by
  refine List.mem_eraseDups.mpr (iterate_mem (fun U x hx => mem_closeOne hx) B.rounds _ t h)

/-- The seeds contain the initial knowledge, the secrets, the domain names and the
domain nonces.  Each is a one-line membership in the seed concatenation. -/
theorem mem_seeds_initKn {P : Protocol} {t : Term} (h : t ∈ P.initKn) : t ∈ seeds P := by
  simp only [seeds, List.mem_append]; tauto

theorem mem_secrets_seeds {P : Protocol} {t : Term} (h : t ∈ P.closedSecretTerms) :
    t ∈ seeds P := by
  simp only [seeds, List.mem_append]; tauto

theorem mem_seeds_agent {P : Protocol} {A : Agent} (h : A ∈ P.agents) :
    Term.agent A ∈ seeds P := by
  simp only [seeds, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨A, h, rfl⟩))))

theorem mem_seeds_nonce {P : Protocol} {N : NonceName} (h : N ∈ P.nonceDomain) :
    Term.nonce N ∈ seeds P := by
  simp only [seeds, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨N, h, rfl⟩))))

/-- The universe contains the attacker's initial knowledge. -/
theorem initKn_subset_univ (P : Protocol) (B : Bounds) :
    ∀ t ∈ P.initKn, t ∈ univ P B := by
  intro t ht
  exact mem_univ_of_mem (mem_subtermClosureL (mem_seeds_initKn ht))

/-- The universe contains the declared closed secrets. -/
theorem secrets_subset_univ (P : Protocol) (B : Bounds) :
    ∀ t ∈ P.closedSecretTerms, t ∈ univ P B := by
  intro t ht
  exact mem_univ_of_mem (mem_subtermClosureL (mem_secrets_seeds ht))

/-- The universe contains every agent name of the domain. -/
theorem agents_subset_univ (P : Protocol) (B : Bounds) (A : Agent) (h : A ∈ P.agents) :
    Term.agent A ∈ univ P B :=
  mem_univ_of_mem (mem_subtermClosureL (mem_seeds_agent h))

/-- The universe contains every nonce value of the domain. -/
theorem nonces_subset_univ (P : Protocol) (B : Bounds) (N : NonceName)
    (h : N ∈ P.nonceDomain) : Term.nonce N ∈ univ P B :=
  mem_univ_of_mem (mem_subtermClosureL (mem_seeds_nonce h))

/-! ### Values: the store and evaluation domain -/

/-- A value is either a message of the universe or "unset".  Session stores map
variables to values and expression evaluation returns a value, so the one-hot encoding
of ProtSat.Encode uses exactly this finite domain. -/
abbrev Val := Option Term

/-- The value domain of a universe: every message of U wrapped in some, plus none. -/
def vals (U : List Term) : List Val := none :: (U.map some)

/-! ### Configurations inside the universe -/

/-- Does every message occurring in configuration C belong to the universe U?  This is
the hypothesis under which the SAT encoding is complete. -/
def cfgInUniverse (C : Cfg) (U : List Term) : Bool :=
  (C.kn.all fun t => U.contains t)
    && (C.sess.all fun s => s.store.all fun p => U.contains p.2)

/-- A trace stays inside the universe if every visited configuration does. -/
def runsInUniverse (Cs : List Cfg) (U : List Term) : Prop :=
  ∀ C ∈ Cs, cfgInUniverse C U = true

/-! ### The bounded predicates -/

/-- BoundedTrace P B tr Cs: tr is a valid trace of at most B.steps events, and every
configuration it visits uses only messages of the universe. -/
def BoundedTrace (P : Protocol) (B : Bounds) (tr : List Ev) (Cs : List Cfg) : Prop :=
  Runs P (initCfg P) tr Cs ∧ tr.length ≤ B.steps ∧ runsInUniverse Cs (univ P B)

/-- BoundedAttack P B: there is a bounded trace that leaks a secret or breaks
agreement.  This is the predicate the SAT encoding is proved equivalent to. -/
def BoundedAttack (P : Protocol) (B : Bounds) : Prop :=
  ∃ tr Cs, BoundedTrace P B tr Cs ∧ (runsLeaks P Cs ∨ AuthBreak P Cs tr)

/-- Bounded safety: no bounded attack exists.  This is NOT the same as unbounded
security; see the README and specification section 11. -/
def BoundedSafe (P : Protocol) (B : Bounds) : Prop := ¬ BoundedAttack P B

end ProtSat.Bounded
