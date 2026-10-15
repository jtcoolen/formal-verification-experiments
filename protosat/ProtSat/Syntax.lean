/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# ProtSat: the symbolic message algebra (specification section 1)

## What this module defines

This module defines the *messages* that protocol participants and the Dolev-Yao
adversary exchange.  Messages are elements of a free algebra of cryptographic
constructors:

* atomic names: agent names and nonces,
* keys: long-term symmetric keys K(A,B), public keys pub A, private keys priv A,
* pairing ⟨x, y⟩,
* symmetric encryption {m}_k,
* asymmetric encryption {m}_A (encryption under pub A),
* hashing #m.

There are deliberately **no destructor constructors** in Term: the message algebra
is presented in *normal form*.  Destructors (projections, decryption) live in the
raw syntax of ProtSat.Theory, together with the explicit symbolic equational
theory

    fst ⟨x, y⟩     = x           snd ⟨x, y⟩     = y
    decS {m}_k k   = m           decA {m}_A (priv A) = m

closed under reflexivity, symmetry, transitivity and congruence.  Theory proves
that the rewrite system made out of these four equations is *convergent*, and
hence that r =_E r' iff norm r = norm r' for raw terms r, r': a verified decision
procedure for the symbolic equational theory.  Because every message produced by
the protocol semantics or by the attacker is a normal form, working with Term
loses nothing, and it makes the finite term universes of section 4 honest sets
rather than quotients.

## Why "symbolic" and not "computational"

Every constructor is *perfect*: {m}_k = {m'}_k implies m = m', and a hash reveals
nothing but its argument.  No computational assumption (DDH, RSA hardness,
collision resistance of a real hash function, ...) is used anywhere in this
development, and none is proved.  All guarantees in this repository are guarantees
of the *symbolic* (Dolev-Yao) model.  See README.md, section "Trust and
limitations".
-/

namespace ProtSat

/-- An agent identifier.  Agents are named by natural numbers; the *bounded* model
(ProtSat.Bounded) fixes the finite set of agent indices a run may use. -/
abbrev Agent := Nat

/-- A nonce *name*: a template.  Each session that generates it picks a concrete
value out of the bounded nonce domain. -/
abbrev NonceName := Nat

/-- A variable of a session's local store. -/
abbrev Var := Nat

/-- Tags used to match authentication events (claim / commit). -/
abbrev Tag := Nat

/-! ### Keys -/

/-- Keys form their own syntactic sort.  Keeping them separate from Term makes the
typing of encryption structural (encS : Term -> Key -> Term), which is what makes
the rewrite system of ProtSat.Theory orthogonal, and it makes the attacker's
decryption rule one clause instead of a case analysis. -/
inductive Key where
  /-- The long-term symmetric key shared by agents a and b. -/
  | shrk (a b : Agent)
  /-- The public key of agent a. -/
  | pub (a : Agent)
  /-- The private key of agent a. -/
  | priv (a : Agent)
  deriving DecidableEq, Repr

namespace Key

/-- Compact concrete syntax for keys, used in printed traces. -/
def show' : Key -> String
  | shrk a b => "K(" ++ reprStr a ++ "," ++ reprStr b ++ ")"
  | pub a => "pub(" ++ reprStr a ++ ")"
  | priv a => "priv(" ++ reprStr a ++ ")"

instance : ToString Key := ⟨show'⟩

end Key

/-! ### Messages (normal forms) -/

/-- The algebra of messages in normal form. -/
inductive Term where
  /-- The name of agent A (public information). -/
  | agent (A : Agent)
  /-- A concrete nonce value. -/
  | nonce (N : NonceName)
  /-- A key, viewed as a message. -/
  | key (k : Key)
  /-- Pairing. -/
  | pair (x y : Term)
  /-- Symmetric encryption of m under the key k. -/
  | encS (m : Term) (k : Key)
  /-- Asymmetric encryption of m for agent a, i.e. under pub a. -/
  | encA (m : Term) (a : Agent)
  /-- Hash of m. -/
  | hash (m : Term)
  deriving DecidableEq, Repr

namespace Term

/-! #### Syntactic measures -/

/-- Number of constructor nodes.  Used as the termination measure for recursions
over messages and to bound the size of the term universe. -/
def size : Term -> Nat
  | agent _ => 1
  | nonce _ => 1
  | key _ => 1
  | pair x y => x.size + y.size + 1
  | encS m _ => m.size + 1
  | encA m _ => m.size + 1
  | hash m => m.size + 1

/-- Nesting depth: atoms and keys have depth 0.  The maxDepth bound of section 4 of
the specification is a bound on this function. -/
def depth : Term -> Nat
  | agent _ => 0
  | nonce _ => 0
  | key _ => 0
  | pair x y => max x.depth y.depth + 1
  | encS m _ => m.depth + 1
  | encA m _ => m.depth + 1
  | hash m => m.depth + 1

@[simp] theorem size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp [size] <;> omega

theorem depth_lt_size (t : Term) : t.depth < t.size := by
  induction t with
  | agent _ | nonce _ | key _ => simp [depth, size]
  | pair x y ihx ihy => simp [depth, size]; omega
  | encS m _ ih | encA m _ ih | hash m ih => simp [depth, size]; omega

/-! #### No-confusion: perfect cryptography (section 1) -/

/-- Constructors are injective.  These lemmas are the formal content of the
"perfect encryption" assumption: an encryption has exactly one plaintext and one
key, a pair exactly two components, and no two different constructor applications
are equal (this is Lean's built-in no-confusion principle). -/
theorem pair_inj : ∀ {x y u v : Term}, Term.pair x y = Term.pair u v -> x = u ∧ y = v
  | _, _, _, _, rfl => ⟨rfl, rfl⟩

theorem encS_inj : ∀ {m k m' k'}, Term.encS m k = Term.encS m' k' -> m = m' ∧ k = k'
  | _, _, _, _, rfl => ⟨rfl, rfl⟩

theorem encA_inj : ∀ {m a m' a'}, Term.encA m a = Term.encA m' a' -> m = m' ∧ a = a'
  | _, _, _, _, rfl => ⟨rfl, rfl⟩

theorem hash_inj : ∀ {m m'}, Term.hash m = Term.hash m' -> m = m'
  | _, _, rfl => rfl

/-- Distinct keys give distinct encryptions (used by the decryption rule). -/
theorem encS_ne_of_key_ne {m m' : Term} {k k' : Key} (h : k ≠ k') :
    Term.encS m k ≠ Term.encS m' k' := by
  intro e; exact h (Term.encS_inj e).2

/-- Different head constructors denote different messages.  These "no confusion"
facts say the attacker's destructor rules are *local*: a message tells you which
destructor can fire on it, and a destructor never applies by accident. -/
theorem ne_pair_encS {m : Term} {k : Key} {u v : Term} : ¬ (Term.pair u v = Term.encS m k) := fun e => by cases e
theorem ne_hash_encS {m : Term} {k : Key} {u : Term} : ¬ (Term.hash u = Term.encS m k) := fun e => by cases e
theorem ne_pair_hash {u v w : Term} : ¬ (Term.pair u v = Term.hash w) := fun e => by cases e
/-! #### Keys as messages -/

/-- Recognise a message that is syntactically a key. -/
def asKey : Term -> Option Key
  | key k => some k
  | _ => none

@[simp] theorem asKey_key (k : Key) : asKey (key k) = some k := rfl

theorem not_asKey {t : Term} (h : ∀ k, t ≠ key k) : asKey t = none := by
  cases t <;> simp_all [asKey]

/-- The keys that occur anywhere inside a message: used to report which long-term
keys a session must know in order to evaluate one of its expressions. -/
def keys : Term -> List Key
  | agent _ => []
  | nonce _ => []
  | key k => [k]
  | pair x y => x.keys ++ y.keys
  | encS m k => k :: m.keys
  | encA m _ => m.keys
  | hash m => m.keys

/-! #### Subterms -/

/-- The (inclusive) subterm set of a message.

This is the operation that makes the finite universe of section 4 a
*subterm-closed* set, which is what the completeness proof for executable attacker
deduction (section 2.2) needs: every premise of every deduction-rule instance is
a subterm of its conclusion. -/
def subterms : Term -> Finset Term
  | agent A => {agent A}
  | nonce N => {nonce N}
  | key k => {key k}
  | pair x y => insert (pair x y) (x.subterms ∪ y.subterms)
  | encS m k => insert (encS m k) (m.subterms ∪ {key k})
  | encA m a => insert (encA m a) (m.subterms ∪ {agent a})
  | hash m => insert (hash m) m.subterms

/-- The characterisation of membership in a subterm set, one lemma per
constructor.  These are the only facts about subterms the rest of the
development uses, which keeps every proof below independent of how Finset
membership is encoded. -/
@[simp] theorem mem_subterms_agent {A : Agent} {u : Term} : u ∈ (Term.agent A).subterms ↔ u = Term.agent A := by
  simp [subterms]
@[simp] theorem mem_subterms_nonce {N : NonceName} {u : Term} : u ∈ (Term.nonce N).subterms ↔ u = Term.nonce N := by
  simp [subterms]
@[simp] theorem mem_subterms_key {k : Key} {u : Term} : u ∈ (Term.key k).subterms ↔ u = Term.key k := by
  simp [subterms]
@[simp] theorem mem_subterms_pair {x y u : Term} :
    u ∈ (Term.pair x y).subterms ↔ u = Term.pair x y ∨ u ∈ x.subterms ∨ u ∈ y.subterms := by
  simp only [subterms, Finset.mem_insert, Finset.mem_union] <;> tauto
@[simp] theorem mem_subterms_encS {m u : Term} {k : Key} :
    u ∈ (Term.encS m k).subterms ↔ u = Term.encS m k ∨ u ∈ m.subterms ∨ u = Term.key k := by
  simp only [subterms, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] <;> tauto
@[simp] theorem mem_subterms_encA {m u : Term} {a : Agent} :
    u ∈ (Term.encA m a).subterms ↔ u = Term.encA m a ∨ u ∈ m.subterms ∨ u = Term.agent a := by
  simp only [subterms, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] <;> tauto
@[simp] theorem mem_subterms_hash {m u : Term} :
    u ∈ (Term.hash m).subterms ↔ u = Term.hash m ∨ u ∈ m.subterms := by
  simp only [subterms, Finset.mem_insert] <;> tauto

@[simp] theorem subterms_self (t : Term) : t ∈ t.subterms := by
  cases t <;> simp [subterms]

/-- Subterms are transitive: a subterm of a subterm is a subterm.  The proof is an
induction on the outer message, case-splitting on the membership characterisations
above; it is the workhorse behind subterm-closure of the universe. -/
theorem subterms_trans : ∀ {t s : Term}, s ∈ t.subterms -> ∀ u ∈ s.subterms, u ∈ t.subterms := by
  intro t
  induction t with
  | agent A | nonce N | key k =>
      intro s h u hu
      simp_all
  | pair x y ihx ihy =>
      intro s h u hu
      rcases mem_subterms_pair.mp h with rfl | h | h
      · exact hu
      · exact mem_subterms_pair.mpr (Or.inr (Or.inl (ihx h u hu)))
      · exact mem_subterms_pair.mpr (Or.inr (Or.inr (ihy h u hu)))
  | encS m k ih =>
      intro s h u hu
      rcases mem_subterms_encS.mp h with rfl | h | h
      · exact hu
      · exact mem_subterms_encS.mpr (Or.inr (Or.inl (ih h u hu)))
      · have hu' : u ∈ (Term.key k).subterms := h ▸ hu
        exact mem_subterms_encS.mpr (Or.inr (Or.inr (mem_subterms_key.mp hu')))
  | encA m a ih =>
      intro s h u hu
      rcases mem_subterms_encA.mp h with rfl | h | h
      · exact hu
      · exact mem_subterms_encA.mpr (Or.inr (Or.inl (ih h u hu)))
      · have hu' : u ∈ (Term.agent a).subterms := h ▸ hu
        exact mem_subterms_encA.mpr (Or.inr (Or.inr (mem_subterms_agent.mp hu')))
  | hash m ih =>
      intro s h u hu
      rcases mem_subterms_hash.mp h with rfl | h
      · exact hu
      · exact mem_subterms_hash.mpr (Or.inr (ih h u hu))

/-! #### Size and depth of subterms

The arithmetic facts about the two syntactic measures are isolated in small named
lemmas so that the structural proofs below stay readable. -/

theorem size_pair_gt_left (x y : Term) : x.size < (Term.pair x y).size := by
  simp [size]; omega
theorem size_pair_gt_right (x y : Term) : y.size < (Term.pair x y).size := by
  simp [size]; omega
theorem size_encS_gt (m : Term) (k : Key) : m.size < (Term.encS m k).size := by
  simp [size]
theorem size_encA_gt (m : Term) (a : Agent) : m.size < (Term.encA m a).size := by
  simp [size]
theorem size_hash_gt (m : Term) : m.size < (Term.hash m).size := by
  simp [size]
theorem size_key_lt_encS (m : Term) (k : Key) : (Term.key k).size < (Term.encS m k).size := by
  simp [size]
theorem size_agent_lt_encA (m : Term) (a : Agent) :
    (Term.agent a).size < (Term.encA m a).size := by
  simp [size]

theorem depth_pair_le_left (x y : Term) : x.depth ≤ (Term.pair x y).depth := by
  simp [depth]; omega
theorem depth_pair_le_right (x y : Term) : y.depth ≤ (Term.pair x y).depth := by
  simp [depth]; omega
theorem depth_encS_le (m : Term) (k : Key) : m.depth ≤ (Term.encS m k).depth := by
  simp [depth]
theorem depth_encA_le (m : Term) (a : Agent) : m.depth ≤ (Term.encA m a).depth := by
  simp [depth]
theorem depth_hash_le (m : Term) : m.depth ≤ (Term.hash m).depth := by
  simp [depth]
theorem depth_key_lt_encS (m : Term) (k : Key) : (Term.key k).depth < (Term.encS m k).depth := by
  simp [depth]
theorem depth_agent_lt_encA (m : Term) (a : Agent) :
    (Term.agent a).depth < (Term.encA m a).depth := by
  simp [depth]

/-- A subterm is never larger. -/
theorem size_le_of_subterms {t u : Term} (h : u ∈ t.subterms) : u.size ≤ t.size := by
  induction t with
  | agent A | nonce N | key k => simp_all
  | pair x y ihx ihy =>
      rcases mem_subterms_pair.mp h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihx h) (Nat.le_of_lt (size_pair_gt_left x y))
      · exact Nat.le_trans (ihy h) (Nat.le_of_lt (size_pair_gt_right x y))
  | encS m k ih =>
      rcases mem_subterms_encS.mp h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (Nat.le_of_lt (size_encS_gt m k))
      · subst h; exact Nat.le_of_lt (size_key_lt_encS m k)
  | encA m a ih =>
      rcases mem_subterms_encA.mp h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (Nat.le_of_lt (size_encA_gt m a))
      · subst h; exact Nat.le_of_lt (size_agent_lt_encA m a)
  | hash m ih =>
      rcases mem_subterms_hash.mp h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (Nat.le_of_lt (size_hash_gt m))

/-- A *proper* subterm is strictly smaller: the measure that makes recursions over
the universe well founded and that bounds the attacker's constructions. -/
theorem size_lt_of_subterms {t u : Term} (h : u ∈ t.subterms) (hne : u ≠ t) : u.size < t.size := by
  induction t with
  | agent A | nonce N | key k => simp_all
  | pair x y ihx ihy =>
      rcases mem_subterms_pair.mp h with rfl | h | h
      · exact absurd rfl hne
      · by_cases e : u = x
        · rw [e]; exact size_pair_gt_left x y
        · exact Nat.lt_of_lt_of_le (ihx h e) (Nat.le_of_lt (size_pair_gt_left x y))
      · by_cases e : u = y
        · rw [e]; exact size_pair_gt_right x y
        · exact Nat.lt_of_lt_of_le (ihy h e) (Nat.le_of_lt (size_pair_gt_right x y))
  | encS m k ih =>
      rcases mem_subterms_encS.mp h with rfl | h | h
      · exact absurd rfl hne
      · by_cases e : u = m
        · rw [e]; exact size_encS_gt m k
        · exact Nat.lt_of_lt_of_le (ih h e) (Nat.le_of_lt (size_encS_gt m k))
      · subst h; exact size_key_lt_encS m k
  | encA m a ih =>
      rcases mem_subterms_encA.mp h with rfl | h | h
      · exact absurd rfl hne
      · by_cases e : u = m
        · rw [e]; exact size_encA_gt m a
        · exact Nat.lt_of_lt_of_le (ih h e) (Nat.le_of_lt (size_encA_gt m a))
      · subst h; exact size_agent_lt_encA m a
  | hash m ih =>
      rcases mem_subterms_hash.mp h with rfl | h
      · exact absurd rfl hne
      · by_cases e : u = m
        · rw [e]; exact size_hash_gt m
        · exact Nat.lt_of_lt_of_le (ih h e) (Nat.le_of_lt (size_hash_gt m))

/-- A subterm of the same size is the whole term.  Together with the previous lemma
this says that the size measure *separates* a message from its proper subterms. -/
theorem eq_of_subterms_of_size_le {t u : Term} (h : u ∈ t.subterms) (hl : t.size ≤ u.size) :
    u = t := by
  by_contra hne
  exact Nat.not_le.mpr (size_lt_of_subterms h hne) hl

/-- A subterm is never deeper. -/
theorem depth_le_of_subterms {t u : Term} (h : u ∈ t.subterms) : u.depth ≤ t.depth := by
  induction t with
  | agent A | nonce N | key k => simp_all
  | pair x y ihx ihy =>
      rcases mem_subterms_pair.mp h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihx h) (depth_pair_le_left x y)
      · exact Nat.le_trans (ihy h) (depth_pair_le_right x y)
  | encS m k ih =>
      rcases mem_subterms_encS.mp h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (depth_encS_le m k)
      · subst h; exact Nat.le_of_lt (depth_key_lt_encS m k)
  | encA m a ih =>
      rcases mem_subterms_encA.mp h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (depth_encA_le m a)
      · subst h; exact Nat.le_of_lt (depth_agent_lt_encA m a)
  | hash m ih =>
      rcases mem_subterms_hash.mp h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (depth_hash_le m)

/-! #### Nonces -/

/-- The set of nonce names occurring in a message.  Used by the freshness theorem
of ProtSat.Attacker (the attacker can never produce a nonce it was not told). -/
def nonces : Term -> Finset NonceName
  | Term.agent _ => ∅
  | Term.nonce N => {N}
  | Term.key _ => ∅
  | Term.pair x y => x.nonces ∪ y.nonces
  | Term.encS m _ => m.nonces
  | Term.encA m _ => m.nonces
  | Term.hash m => m.nonces

@[simp] theorem nonces_pair (x y : Term) : (Term.pair x y).nonces = x.nonces ∪ y.nonces := rfl
@[simp] theorem nonces_encS (m : Term) (k : Key) : (Term.encS m k).nonces = m.nonces := rfl
@[simp] theorem nonces_encA (m : Term) (a : Agent) : (Term.encA m a).nonces = m.nonces := rfl
@[simp] theorem nonces_hash (m : Term) : (Term.hash m).nonces = m.nonces := rfl
@[simp] theorem nonces_agent (a : Agent) : (Term.agent a).nonces = (∅ : Finset NonceName) := rfl
@[simp] theorem nonces_key (k : Key) : (Term.key k).nonces = (∅ : Finset NonceName) := rfl

/-! #### The finite term universe (section 4) -/

/-- One step of closing a set of messages under the cryptographic constructors,
using keys from ks and agent names from as.

This is the mechanism behind the "maximum term depth" and "finite principal and
nonce domains" parameters of section 4: the analysed execution space is the set of
messages reachable from the seeds by iterating this step a bounded number of
times.  The step is monotone and the result is finite, so iterating it reaches a
fixpoint; the function pool below simply burns a fixed number of rounds, which is
cheaper to reason about. -/
def poolStep (ks : Finset Key) (as : Finset Agent) (U : Finset Term) : Finset Term :=
  U ∪
  (U.biUnion fun x => U.biUnion fun y => {pair x y}) ∪
  (U.biUnion fun m => ks.biUnion fun k => {encS m k}) ∪
  (U.biUnion fun m => as.biUnion fun a => {encA m a}) ∪
  (U.biUnion fun m => {hash m})

@[simp] lemma poolStep_subset (ks : Finset Key) (as : Finset Agent) (U : Finset Term) :
    U ⊆ poolStep ks as U := by
  intro x hx
  show x ∈ ((((U ∪ _) ∪ _) ∪ _) ∪ _)
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))))))

/- The four membership lemmas below spell out the disjunction structure of the
five-way union in poolStep:  U ∪ pairs ∪ encS ∪ encA ∪ hash, which Lean parses
left-associatively as ((((U ∪ pairs) ∪ encS) ∪ encA) ∪ hash).  Keeping them as
four named lemmas means the rest of the development never has to look inside a
union. -/

theorem mem_poolStep_pair (ks : Finset Key) (as : Finset Agent) (U : Finset Term)
    (x y : Term) (hx : x ∈ U) (hy : y ∈ U) : Term.pair x y ∈ poolStep ks as U :=
  have hA : Term.pair x y ∈ (U.biUnion fun a => U.biUnion fun c => {Term.pair a c}) :=
    Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_singleton.mpr rfl⟩⟩
  Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hA)))))))

theorem mem_poolStep_encS (ks : Finset Key) (as : Finset Agent) (U : Finset Term)
    (m : Term) (k : Key) (hm : m ∈ U) (hk : k ∈ ks) : Term.encS m k ∈ poolStep ks as U :=
  have hB : Term.encS m k ∈ (U.biUnion fun a => ks.biUnion fun k => {Term.encS a k}) :=
    Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_singleton.mpr rfl⟩⟩
  Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inr hB)))))

theorem mem_poolStep_encA (ks : Finset Key) (as : Finset Agent) (U : Finset Term)
    (m : Term) (a : Agent) (hm : m ∈ U) (ha : a ∈ as) : Term.encA m a ∈ poolStep ks as U :=
  have hC : Term.encA m a ∈ (U.biUnion fun b => as.biUnion fun c => {Term.encA b c}) :=
    Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_singleton.mpr rfl⟩⟩
  Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hC)))

theorem mem_poolStep_hash (ks : Finset Key) (as : Finset Agent) (U : Finset Term)
    (m : Term) (hm : m ∈ U) : Term.hash m ∈ poolStep ks as U :=
  have hD : Term.hash m ∈ (U.biUnion fun a => {Term.hash a}) :=
    Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_singleton.mpr rfl⟩
  Finset.mem_union.mpr (Or.inr hD)

/-- pool seeds ks as rounds is a term universe: rounds closure steps over the seed
set.  The seeds are normally the subterm closure of everything the protocol
mentions (section 4: "explicitly define the relationship between these bounds and
the analyzed execution space"). -/
def pool (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (rounds : Nat) : Finset Term :=
  (fun U => poolStep ks as U)^[rounds] seeds

theorem pool_zero (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) :
    pool seeds ks as 0 = seeds := rfl

theorem pool_succ (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (n : Nat) :
    pool seeds ks as (n + 1) = poolStep ks as (pool seeds ks as n) := by
  simp only [pool]
  exact Function.iterate_succ_apply' _ _ _

theorem pool_mono (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (n : Nat) :
    pool seeds ks as n ⊆ pool seeds ks as (n + 1) := by
  rw [pool_succ]; exact poolStep_subset _ _ _

/-- **The pool is closed under the constructors.**  These four lemmas are exactly
what the completeness proof of the SAT encoding (section 8B) needs from the
universe: whenever a run of length at most L uses a message the attacker built,
that message is still in the universe at the next round, so the encoding never has
to talk about a message outside U. -/
theorem pool_closed_pair (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (n : Nat) :
    ∀ x y, x ∈ pool seeds ks as n -> y ∈ pool seeds ks as n ->
      Term.pair x y ∈ pool seeds ks as (n + 1) := by
  intro x y hx hy
  rw [pool_succ]
  exact mem_poolStep_pair _ _ _ x y hx hy

theorem pool_closed_encS (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (n : Nat) :
    ∀ m k, m ∈ pool seeds ks as n -> k ∈ ks -> Term.encS m k ∈ pool seeds ks as (n + 1) := by
  intro m k hm hk
  rw [pool_succ]
  exact mem_poolStep_encS _ _ _ m k hm hk

theorem pool_closed_encA (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (n : Nat) :
    ∀ m a, m ∈ pool seeds ks as n -> a ∈ as -> Term.encA m a ∈ pool seeds ks as (n + 1) := by
  intro m a hm ha
  rw [pool_succ]
  exact mem_poolStep_encA _ _ _ m a hm ha

theorem pool_closed_hash (seeds : Finset Term) (ks : Finset Key) (as : Finset Agent) (n : Nat) :
    ∀ m, m ∈ pool seeds ks as n -> Term.hash m ∈ pool seeds ks as (n + 1) := by
  intro m hm
  rw [pool_succ]
  exact mem_poolStep_hash _ _ _ m hm

/-- The subterm closure of a set of messages.  Unlike pool this operation only
*removes* structure, so it never blows up: it is the right way to build seeds. -/
def subtermClosure (S : Finset Term) : Finset Term := S.biUnion subterms

theorem mem_subtermClosure (S : Finset Term) {t : Term} (h : t ∈ S) : t ∈ subtermClosure S :=
  Finset.mem_biUnion.mpr ⟨t, h, subterms_self t⟩

/-- **The universe is subterm-closed.**  This single lemma is what section 2.2
(completeness of executable deduction relative to the finite universe) and
section 8A (encoding soundness) are built on: whenever the conclusion of a
deduction rule instance is in the universe, so are all of its premises. -/
theorem subtermClosure_subterms (S : Finset Term) {t u : Term}
    (h : t ∈ subtermClosure S) (hu : u ∈ t.subterms) : u ∈ subtermClosure S := by
  obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨s, hs, subterms_trans hts u hu⟩

/-! #### Pretty printing (used by the executable analyser) -/

/-- Compact concrete syntax for messages, for human-readable traces. -/
def show' : Term -> String
  | agent A => "agent " ++ reprStr A
  | nonce N => "n" ++ reprStr N
  | key k => Key.show' k
  | pair x y => "⟨" ++ x.show' ++ "," ++ y.show' ++ "⟩"
  | encS m k => "{" ++ m.show' ++ "}_" ++ Key.show' k
  | encA m a => "{" ++ m.show' ++ "}_pub(" ++ reprStr a ++ ")"
  | hash m => "#" ++ m.show'

instance : ToString Term := ⟨show'⟩

end Term

end ProtSat
