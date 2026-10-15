/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Syntax

/-!
# ProtSat: the Dolev-Yao attacker (specification section 2)

## Three deduction relations, and why there are three

1. Ded K m - the inductive, unbounded Dolev-Yao relation.  This is the *reference*
   semantics of the attacker: attack certificates are checked against it
   (ProtSat.Certificate), and it places no bound at all on the size of the
   intermediate messages the attacker builds.

2. OneStep K t - "t is the conclusion of one instance of one of the deduction
   rules, all of whose premises lie in K" - stated as an inductive predicate (one
   constructor per rule, so the SAT encoding gets one clause group per rule) and
   computed as a Boolean function oneStepBool.  oneStepBool_iff proves the two
   agree; that theorem is the "correctness of cryptographic constructor and
   destructor rules" of specification section 2.4.

3. deduce U K n - the executable saturation procedure: start from K and, for n
   rounds, add every message of the *finite universe* U that is one step derivable.
   deduce_sound proves soundness w.r.t. Ded (section 2.1) and dedIn_deduce proves
   completeness relative to U (section 2.2).  ded_dedIn then shows the
   finite-universe restriction costs nothing in principle: every Ded derivation
   lives inside *some* finite universe, so the executable procedure is complete in
   the limit.

Knowledge bases are *lists* of messages: membership is List.Mem, the executable
procedures use List.filter / List.any, and no finiteness assumption beyond the
universe U is hidden in the representation.

## The rules

The attacker may: replay what it knows (known); use agent names and public keys
(agent, pub); pair two known messages (pairI); project a known pair (fstE, sndE);
encrypt a known message under a known key (encSI, encAI); decrypt a known
ciphertext with a known key (encSD, encAD); hash a known message (hashI); and
inject any deduced message into the network (modelled in ProtSat.Operational).

No rule undoes an encryption whose key is unknown, invents a nonce, or splits a
hash.  Section 2 of the specification forbids approximating deduction by declaring
everything public; no_fresh_nonces and the negative examples at the end of this
file are the formal evidence that the model really is restrictive.
-/

namespace ProtSat.Attacker

open ProtSat

/-! ### The reference relation -/

/-- Ded K m: the message m can be deduced from the attacker's knowledge base K.

The relation is inductive in the conclusion, so a proof of Ded K m carries a finite
derivation tree, which is what an attack certificate later exhibits. -/
inductive Ded : List Term -> Term -> Prop
  /-- Replay: anything already known is deducible. -/
  | known : ∀ {K m}, m ∈ K -> Ded K m
  /-- Agent names are public information. -/
  | agent : ∀ {K A}, Ded K (Term.agent A)
  /-- Public keys are public information. -/
  | pub : ∀ {K A}, Ded K (Term.key (Key.pub A))
  /-- Pairing constructor. -/
  | pairI : ∀ {K a b}, Ded K a -> Ded K b -> Ded K (Term.pair a b)
  /-- First projection. -/
  | fstE : ∀ {K a b}, Ded K (Term.pair a b) -> Ded K a
  /-- Second projection. -/
  | sndE : ∀ {K a b}, Ded K (Term.pair a b) -> Ded K b
  /-- Symmetric encryption constructor. -/
  | encSI : ∀ {K m k}, Ded K m -> Ded K (Term.key k) -> Ded K (Term.encS m k)
  /-- Symmetric decryption: needs the ciphertext and the key. -/
  | encSD : ∀ {K m k}, Ded K (Term.encS m k) -> Ded K (Term.key k) -> Ded K m
  /-- Asymmetric encryption constructor (encryption for agent a). -/
  | encAI : ∀ {K m a}, Ded K m -> Ded K (Term.encA m a)
  /-- Asymmetric decryption: needs the ciphertext and the private key of a. -/
  | encAD : ∀ {K m a}, Ded K (Term.encA m a) -> Ded K (Term.key (Key.priv a)) -> Ded K m
  /-- Hashing constructor. -/
  | hashI : ∀ {K m}, Ded K m -> Ded K (Term.hash m)

/-! ### Section 2.3: monotonicity -/

/-- **Monotonicity of attacker knowledge** (specification section 2.3).  Growing
the knowledge base never destroys a deduction. -/
theorem ded_mono {K K' : List Term} {m : Term} (h : Ded K m)
    (sub : ∀ x, x ∈ K -> x ∈ K') : Ded K' m := by
  induction h with
  | known hx => exact Ded.known (sub _ hx)
  | agent => exact Ded.agent
  | pub => exact Ded.pub
  | pairI _ _ ih1 ih2 => exact Ded.pairI ih1 ih2
  | fstE _ ih => exact Ded.fstE ih
  | sndE _ ih => exact Ded.sndE ih
  | encSI _ _ ih1 ih2 => exact Ded.encSI ih1 ih2
  | encSD _ _ ih1 ih2 => exact Ded.encSD ih1 ih2
  | encAI _ ih => exact Ded.encAI ih
  | encAD _ _ ih1 ih2 => exact Ded.encAD ih1 ih2
  | hashI _ ih => exact Ded.hashI ih

/-- Appending a message to the knowledge base preserves everything deducible. -/
theorem ded_append {K K' : List Term} {m : Term} (h : Ded K m) : Ded (K' ++ K) m :=
  ded_mono h (by intro x hx; exact List.mem_append_right K' hx)

/-- **Monotonicity, corollary used by the bounded model:** knowledge only grows
along a run. -/
theorem ded_grow {K : List Term} {t : Term} (h : Ded K t) (x : Term) : Ded (x :: K) t :=
  ded_mono h (by intro y hy; exact List.Mem.tail _ hy)

/-! ### Section 2.4: correctness of the constructor / destructor pairs -/

/-- Encrypting and then decrypting returns the plaintext: the destructor is a left
inverse of the constructor (symmetric case). -/
theorem encS_then_decS {K : List Term} {m : Term} {k : Key}
    (hm : Ded K m) (hk : Ded K (Term.key k)) : Ded K m :=
  Ded.encSD (Ded.encSI hm hk) hk

/-- The asymmetric analogue: decryption with priv a inverts encryption for a. -/
theorem encA_then_decA {K : List Term} {m : Term} {a : Agent}
    (hm : Ded K m) (hk : Ded K (Term.key (Key.priv a))) : Ded K m :=
  Ded.encAD (Ded.encAI hm) hk

/-- Pairing then projecting returns both components. -/
theorem pair_then_proj {K : List Term} {a b : Term} (ha : Ded K a) (hb : Ded K b) :
    Ded K a ∧ Ded K b := ⟨Ded.fstE (Ded.pairI ha hb), Ded.sndE (Ded.pairI ha hb)⟩

/-! ### Freshness: the attacker cannot invent nonces -/

/-- The nonces occurring anywhere in a knowledge base. -/
def noncesOf : List Term -> Finset NonceName
  | [] => ∅
  | t :: K => t.nonces ∪ noncesOf K

theorem noncesOf_nil : noncesOf ([] : List Term) = ∅ := rfl

theorem noncesOf_cons (t : Term) (K : List Term) :
    noncesOf (t :: K) = t.nonces ∪ noncesOf K := rfl

/-- **The attacker cannot create fresh nonces.**  This is the formal content of the
freshness assumption every protocol in section 9 relies on, and it is what makes
the freshness constraints of the SAT encoding (section 5) meaningful: every nonce
occurring in a deducible message already occurs in the knowledge base. -/
theorem no_fresh_nonces {K : List Term} {m : Term} (h : Ded K m) :
    m.nonces ⊆ noncesOf K := by
  induction h with
  | known hk =>
      induction K with
      | nil => simp_all [noncesOf]
      | cons t rest ih =>
          rw [List.mem_cons] at hk
          rcases hk with rfl | hk
          · exact Finset.subset_union_left
          · exact Finset.Subset.trans (ih hk) Finset.subset_union_right
  | agent => simp [Term.nonces_agent]
  | pub => simp [Term.nonces_key]
  | pairI _ _ ih1 ih2 => exact Finset.union_subset ih1 ih2
  | fstE _ ih => exact Finset.Subset.trans (by simp [Term.nonces_pair]) ih
  | sndE _ ih => exact Finset.Subset.trans (by simp [Term.nonces_pair]) ih
  | encSI _ _ ih1 _ => exact ih1
  | encSD _ _ ih1 _ => exact ih1
  | encAI _ ih => exact ih
  | encAD _ _ ih1 _ => exact ih1
  | hashI _ ih => exact ih

/-- A nonce the attacker was never told about cannot be produced. -/
theorem nonce_not_deducible (N : NonceName) : ¬ Ded ([] : List Term) (Term.nonce N) := by
  intro h
  have h1 := no_fresh_nonces h
  have hN : N ∈ (Term.nonce N).nonces := by simp [Term.nonces]
  have h2 : N ∈ (∅ : Finset NonceName) := h1 hN
  exact absurd h2 (by simp)

/-- With an empty knowledge base the attacker cannot even build the encryption of
a nonce it does not know: the formal counterpart of "do not approximate deduction
by treating every term as publicly known". -/
theorem encS_nonce_not_deducible (N : NonceName) (k : Key) :
    ¬ Ded ([] : List Term) (Term.encS (Term.nonce N) k) := by
  intro h
  have h1 := no_fresh_nonces h
  have hN : N ∈ (Term.encS (Term.nonce N) k).nonces := by simp [Term.nonces]
  have h2 : N ∈ (∅ : Finset NonceName) := h1 hN
  exact absurd h2 (by simp)

/-! ### One deduction step -/

/-- OneStep K t: t is the conclusion of one instance of one of the deduction rules,
all of whose premises lie in K.  One constructor per rule, which is what lets the
SAT encoding emit one clause group per rule (ProtSat.Encode.onestepClauses). -/
inductive OneStep : List Term -> Term -> Prop
  | known : ∀ {K t}, t ∈ K -> OneStep K t
  | agent : ∀ {K A}, OneStep K (Term.agent A)
  | pub : ∀ {K A}, OneStep K (Term.key (Key.pub A))
  | pairI : ∀ {K x y}, x ∈ K -> y ∈ K -> OneStep K (Term.pair x y)
  | fstE : ∀ {K x y}, Term.pair x y ∈ K -> OneStep K x
  | sndE : ∀ {K x y}, Term.pair x y ∈ K -> OneStep K y
  | encSI : ∀ {K m k}, m ∈ K -> Term.key k ∈ K -> OneStep K (Term.encS m k)
  | encSD : ∀ {K m k}, Term.encS m k ∈ K -> Term.key k ∈ K -> OneStep K m
  | encAI : ∀ {K m a}, m ∈ K -> OneStep K (Term.encA m a)
  | encAD : ∀ {K m a}, Term.encA m a ∈ K -> Term.key (Key.priv a) ∈ K -> OneStep K m
  | hashI : ∀ {K m}, m ∈ K -> OneStep K (Term.hash m)

/-- Every one-step conclusion is genuinely deducible. -/
theorem oneStep_ded {K : List Term} {t : Term} (h : OneStep K t) : Ded K t := by
  induction h with
  | known ht => exact Ded.known ht
  | agent => exact Ded.agent
  | pub => exact Ded.pub
  | pairI hx hy => exact Ded.pairI (Ded.known hx) (Ded.known hy)
  | fstE hp => exact Ded.fstE (Ded.known hp)
  | sndE hp => exact Ded.sndE (Ded.known hp)
  | encSI hm hk => exact Ded.encSI (Ded.known hm) (Ded.known hk)
  | encSD he hk => exact Ded.encSD (Ded.known he) (Ded.known hk)
  | encAI hm => exact Ded.encAI (Ded.known hm)
  | encAD he hk => exact Ded.encAD (Ded.known he) (Ded.known hk)
  | hashI hm => exact Ded.hashI (Ded.known hm)

/-- One-step deduction is monotone in the knowledge base: the property that makes
the saturation loop monotone and that the encoding's "knowledge only grows"
clauses express. -/
theorem oneStep_mono {K K' : List Term} (sub : ∀ x, x ∈ K -> x ∈ K') {t : Term}
    (h : OneStep K t) : OneStep K' t := by
  induction h with
  | known ht => exact OneStep.known (sub _ ht)
  | agent => exact OneStep.agent
  | pub => exact OneStep.pub
  | pairI hx hy => exact OneStep.pairI (sub _ hx) (sub _ hy)
  | fstE hp => exact OneStep.fstE (sub _ hp)
  | sndE hp => exact OneStep.sndE (sub _ hp)
  | encSI hm hk => exact OneStep.encSI (sub _ hm) (sub _ hk)
  | encSD he hk => exact OneStep.encSD (sub _ he) (sub _ hk)
  | encAI hm => exact OneStep.encAI (sub _ hm)
  | encAD he hk => exact OneStep.encAD (sub _ he) (sub _ hk)
  | hashI hm => exact OneStep.hashI (sub _ hm)


/-! ### Where the executable procedure lives

The executable saturation over a finite universe (specification sections 2.1 and
2.2) is developed in its own module, ProtSat.Deduce, which imports this one and
proves deduce_sound, dedIn_deduce and ded_dedIn.  Keeping it separate makes the
trust structure explicit: the declarative rules above are the reference model, and
the executable procedure is a *client* of them. -/

end ProtSat.Attacker
