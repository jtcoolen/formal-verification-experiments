/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Attacker

/-!
# ProtSat: executable Dolev-Yao deduction over a finite term universe
(specification section 2)

## What this module adds

'ProtSat.Attacker' contains the *declarative* attacker: the inductive relation
'Ded K m' (eleven rules) and the one-step relation 'OneStep K t' (one constructor per
rule).  Neither is executable: 'Ded' is a 'Prop'-valued inductive, and 'OneStep'
quantifies over *all* agent names, so neither can be evaluated by the kernel.

This module supplies the *executable* deduction procedure of specification section 2
together with the four theorems section 2 demands:

| specification | theorem |
|---|---|
| 2.1 soundness of executable deduction | 'deduce_sound' |
| 2.2 completeness relative to the finite universe | 'oneStep_mem', 'dedIn_deduce' |
| 2.3 monotonicity of attacker knowledge | 'deduce_subset_deduce_succ', 'deduce_mono' |
| 2.4 correctness of the constructor / destructor rules | 'encS_decS_step', 'encA_decA_step', 'pair_proj_step' — executable restatements of 'Attacker.encS_then_decS', 'Attacker.encA_then_decA', 'Attacker.pair_then_proj', which are *not* reproved here |

## The algorithm

```text
oneStepList ag K     =  (oneStepChunks ag K).flatten
closeStep   U ag K   =  K ++ U.filter (fun t => decide (t ∈ oneStepList ag K))
deduce      U ag K n =  (closeStep U ag)^[n] K
```

Every definition is a plain list comprehension or an iteration of one: there is no recursion
and no unbounded search anywhere in the procedure, so all three are kernel-reducible and can
be run by 'decide' on concrete inputs (see the examples at the end of the file).

'oneStepList' enumerates *every* instance of every deduction rule whose premises are
currently held: the pair chunk is 'K × K', the projection chunks scan 'K', the symmetric
encryption chunk pairs 'K' with the keys held in 'K', the decryption chunks scan the
ciphertexts in 'K', and so on.  A rule instance is built only out of messages already in
'K', so the enumeration is finite and quadratic in '|K|' — no exponential search.

'closeStep' keeps from that enumeration only the messages that lie in the *finite
universe* 'U' (the filter) and appends them to the current knowledge.  The filter is what
makes the procedure bounded: 'deduce_subset_union' proves the invariant that the knowledge
never leaves 'K ∪ U'.  'deduce' iterates 'closeStep' a bounded number of rounds; the round
bound is an explicit parameter, exactly as section 4 requires of every bound.

## Why the universe has to be *supported*

'Ded' and 'OneStep' may introduce the name of *any* agent, the public key of *any* agent,
and may encrypt *for* any agent: three rules with an unbounded witness.  An executable
enumeration can only produce the witnesses of a bounded domain, so 'oneStepList ag K'
injects the public material of the agents '0, …, ag - 1' and encrypts only for those
agents: 'ag' is the size of the bounded agent domain (the "finite principal domain" of
specification section 4).

'supported ag U' says that the universe only mentions agent indices below 'ag'.  With that
hypothesis the enumeration is *complete*: 'oneStep_mem' proves that every 'OneStep K t'
with 't ∈ U' appears in 'oneStepList ag K'.  Without it the theorem is false (the message
'Term.agent 1' is derivable but not enumerated when 'ag = 1'), so 'supported' is not
decoration: it is the exact price of executability.  'ded_dedIn' at the end of the file
shows that nothing else is lost — every derivation lives in *some* supported finite
universe.

## Completeness, precisely

'deduce_sound' holds unconditionally.  The converse cannot hold for an arbitrary universe:
a 'Ded' derivation of a message of 'U' may pass through intermediate messages outside 'U'
(the attacker may build a pair outside the universe and project it), and no finite
universe is closed under every possible detour.  The honest statement — the one
specification section 2.2 asks for — is completeness for derivations that stay inside the
universe, formalised by the auxiliary inductive 'DedIn U K t' ("'t' is deducible by a
derivation all of whose conclusions lie in 'U'").  'dedIn_deduce' proves that 'U.length'
rounds of the executable saturation derive every message of 'DedIn U K t'.  The proof
needs a genuine fixpoint theorem, 'deduce_closed' (the saturation stops growing after '|U|'
rounds, by a counting argument on 'knownCount'), not merely an induction on the
derivation.
-/

namespace ProtSat.Deduce

open ProtSat Term Attacker

/-! ### The bounded agent domain -/

/-- The agent indices a message *mentions*: 'A' occurs in the list of 'Term.agent A', of
'Term.key (Key.pub A)' and of 'Term.encA m A'.  These are exactly the three places where a
deduction rule has an agent witness that an executable enumeration has to guess, so this
is what the 'supported' hypothesis below bounds. -/
def agentsOf : Term → List Agent
  | Term.agent A => [A]
  | Term.key (Key.pub A) => [A]
  | Term.encA _ a => [a]
  | _ => []

/-- A universe 'U' is *supported* by the agent domain 'Fin ag' when every agent index
mentioned by a message of 'U' is below 'ag'.

This is the "explicitly bounded finite term universe" of specification section 2 read
together with section 4: the executable procedure may only use the agents '0, …, ag-1', and
'supported' is the hypothesis that lets it produce *everything* the declarative attacker
can produce inside 'U' (see 'oneStep_mem'). -/
def supported (ag : Agent) (U : List Term) : Prop :=
  ∀ t ∈ U, ∀ A ∈ agentsOf t, A < ag

/-- The keys the attacker holds, read off its knowledge base as messages. -/
def keysOf (K : List Term) : List Key := K.filterMap Term.asKey

/-- 'k ∈ keysOf K' iff the message 'Term.key k' is in 'K'. -/
theorem mem_keysOf {k : Key} {K : List Term} : k ∈ keysOf K ↔ Term.key k ∈ K := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp h
    cases x with
    | key k' =>
        have : k' = k := by simpa [Term.asKey] using he
        subst this
        exact hx
    | agent _ | nonce _ | pair _ _ | encS _ _ | encA _ _ | hash _ => cases he
  · intro h
    exact List.mem_filterMap.mpr ⟨Term.key k, h, rfl⟩

/-- The public initial material of the bounded model: every agent name and every public key
of the agent domain 'Fin ag'.  These are the conclusions of the two rules 'Ded.agent' and
'Ded.pub', which need no premise at all. -/
def pubMaterial (ag : Agent) : List Term :=
  (List.range ag).map Term.agent ++ (List.range ag).map fun a => Term.key (Key.pub a)


/-! ### The executable one-step enumeration -/

/-- The ten chunks of the executable one-step enumeration, one per rule of
'Attacker.OneStep', in the order in which the constructors of 'OneStep' are declared: replay,
agent name + public key, pairing, first projection, second projection, symmetric encryption,
symmetric decryption, asymmetric encryption, asymmetric decryption, hashing.

Keeping them as an explicit list of chunks is what lets 'oneStepList_sound' and
'oneStep_mem' be proved by a single case split, one case per rule. -/
def oneStepChunks (ag : Agent) (K : List Term) : List (List Term) :=
  [ -- 'known': replay everything already observed
    K
    -- 'agent' + 'pub': the public initial material of the bounded domain
  , pubMaterial ag
    -- 'pairI': every pair of known messages
  , K.flatMap fun x => K.map fun y => Term.pair x y
    -- 'fstE': first components of known pairs
  , K.filterMap fun t => match t with | Term.pair x _ => some x | _ => none
    -- 'sndE': second components of known pairs
  , K.filterMap fun t => match t with | Term.pair _ y => some y | _ => none
    -- 'encSI': encrypt every known message under every known key
  , K.flatMap fun m => (keysOf K).map fun k => Term.encS m k
    -- 'encSD': decrypt every known ciphertext whose key is known
  , K.filterMap fun t => match t with
      | Term.encS m k => if Term.key k ∈ K then some m else none
      | _ => none
    -- 'encAI': encrypt every known message for every agent of the domain
  , K.flatMap fun m => (List.range ag).map fun a => Term.encA m a
    -- 'encAD': decrypt every known asymmetric ciphertext whose private key is known
  , K.filterMap fun t => match t with
      | Term.encA m a => if Term.key (Key.priv a) ∈ K then some m else none
      | _ => none
    -- 'hashI': hash every known message
  , K.map Term.hash ]

/-- 'oneStepList ag K': the executable one-step closure of 'K'.  Every element is the
conclusion of one instance of one of the eleven deduction rules whose premises all lie in 'K'
('oneStepList_sound'), and — provided the conclusion lies in a universe supported by 'ag' —
*every* such instance appears here ('oneStep_mem').

The function is a chain of 'flatMap' / 'map' / 'filterMap' over 'K': no recursion, so
termination is immediate and the cost is quadratic in '|K|'. -/
def oneStepList (ag : Agent) (K : List Term) : List Term :=
  (oneStepChunks ag K).flatten

/-- **Soundness of the enumeration** (the engine of specification section 2.1).  Every message
the executable one-step procedure produces is the conclusion of a real instance of one of the
deduction rules: membership in 'oneStepList ag K' implies 'OneStep K t'.

The proof is a case split over the ten chunks; each case reads the premises off the chunk that
produced the message and replays them through the matching constructor of
'Attacker.OneStep'. -/
theorem oneStepList_sound (ag : Agent) (K : List Term) :
    ∀ t ∈ oneStepList ag K, OneStep K t := by
  intro t h
  rw [oneStepList, List.mem_flatten] at h
  obtain ⟨c, hc, hm⟩ := h
  simp only [oneStepChunks, List.mem_cons, List.not_mem_nil, or_false] at hc
  revert hm
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 'known'
    intro hx; exact OneStep.known hx
  · -- 'agent' + 'pub'
    intro hx
    rw [pubMaterial, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact OneStep.agent
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact OneStep.pub
  · -- 'pairI'
    intro hx
    obtain ⟨x, hxK, hy⟩ := List.mem_flatMap.mp hx
    obtain ⟨y, hyK, rfl⟩ := List.mem_map.mp hy
    exact OneStep.pairI hxK hyK
  · -- 'fstE'
    intro hx
    obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hx
    cases p with
    | pair x y =>
        have h2 : some x = some t := he
        cases h2
        exact OneStep.fstE hp
    | _ => cases he
  · -- 'sndE'
    intro hx
    obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hx
    cases p with
    | pair x y =>
        have h2 : some y = some t := he
        cases h2
        exact OneStep.sndE hp
    | _ => cases he
  · -- 'encSI'
    intro hx
    obtain ⟨m, hmK, hrest⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, hkK, rfl⟩ := List.mem_map.mp hrest
    exact OneStep.encSI hmK (mem_keysOf.mp hkK)
  · -- 'encSD'
    intro hx
    obtain ⟨c', hc', he⟩ := List.mem_filterMap.mp hx
    cases c' with
    | encS m k =>
        by_cases hk : Term.key k ∈ K
        · have h2 : some m = some t := by simpa [hk] using he
          cases h2
          exact OneStep.encSD hc' hk
        · simp [hk] at he
    | _ => cases he
  · -- 'encAI'
    intro hx
    obtain ⟨m, hmK, hrest⟩ := List.mem_flatMap.mp hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hrest
    exact OneStep.encAI hmK
  · -- 'encAD'
    intro hx
    obtain ⟨c', hc', he⟩ := List.mem_filterMap.mp hx
    cases c' with
    | encA m a =>
        by_cases hk : Term.key (Key.priv a) ∈ K
        · have h2 : some m = some t := by simpa [hk] using he
          cases h2
          exact OneStep.encAD hc' hk
        · simp [hk] at he
    | _ => cases he
  · -- 'hashI'
    intro hx
    obtain ⟨m, hmK, rfl⟩ := List.mem_map.mp hx
    exact OneStep.hashI hmK

/-- **Completeness of the enumeration inside the universe** (the engine of specification
section 2.2).  If 't' is the conclusion of a real deduction-rule instance and 't' lies in a
universe supported by the agent domain 'ag', then the executable enumeration finds it:
't ∈ oneStepList ag K'.

This is where the bounded agent domain is used: the rules 'agent', 'pub' and 'encAI' have an
unconstrained agent witness in the declarative model, and the enumeration can only guess the
witnesses '0, …, ag-1'.  For a conclusion inside a supported universe those witnesses
coincide, and the enumeration is exhaustive.

Together with 'oneStepList_sound' this says that, inside a supported universe, the executable
one-step enumeration and the declarative one-step relation coincide. -/
theorem oneStep_mem {ag : Agent} {K U : List Term} (hsup : supported ag U) {t : Term}
    (hU : t ∈ U) (h : OneStep K t) : t ∈ oneStepList ag K := by
  have inList : ∀ c ∈ oneStepChunks ag K, t ∈ c → t ∈ oneStepList ag K := fun c hc ht =>
    List.mem_flatten.mpr ⟨c, hc, ht⟩
  induction h with
  | known hx => exact inList K (by simp [oneStepChunks]) hx
  | agent =>
      rename_i A
      have hA : A < ag := hsup _ hU A (by simp [agentsOf])
      exact inList (pubMaterial ag) (by simp [oneStepChunks])
        (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨A, List.mem_range.mpr hA, rfl⟩)))
  | pub =>
      rename_i A
      have hA : A < ag := hsup _ hU A (by simp [agentsOf])
      exact inList (pubMaterial ag) (by simp [oneStepChunks])
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨A, List.mem_range.mpr hA, rfl⟩)))
  | pairI hx hy =>
      exact inList (K.flatMap fun x => K.map fun y => Term.pair x y) (by simp [oneStepChunks])
        (List.mem_flatMap.mpr ⟨_, hx, List.mem_map.mpr ⟨_, hy, rfl⟩⟩)
  | fstE hp =>
      exact inList (K.filterMap fun t => match t with
          | Term.pair x _ => some x | _ => none) (by simp [oneStepChunks])
        (List.mem_filterMap.mpr ⟨Term.pair _ _, hp, rfl⟩)
  | sndE hp =>
      exact inList (K.filterMap fun t => match t with
          | Term.pair _ y => some y | _ => none) (by simp [oneStepChunks])
        (List.mem_filterMap.mpr ⟨Term.pair _ _, hp, rfl⟩)
  | encSI hm hk =>
      exact inList (K.flatMap fun m => (keysOf K).map fun k => Term.encS m k)
        (by simp [oneStepChunks])
        (List.mem_flatMap.mpr ⟨_, hm, List.mem_map.mpr ⟨_, mem_keysOf.mpr hk, rfl⟩⟩)
  | encSD he hk =>
      exact inList (K.filterMap fun t => match t with
          | Term.encS m k => if Term.key k ∈ K then some m else none
          | _ => none) (by simp [oneStepChunks])
        (List.mem_filterMap.mpr ⟨Term.encS _ _, he, by simp [hk]⟩)
  | encAI hm =>
      rename_i a
      exact inList (K.flatMap fun m => (List.range ag).map fun a => Term.encA m a)
        (by simp [oneStepChunks])
        (List.mem_flatMap.mpr ⟨_, hm, List.mem_map.mpr ⟨a,
          List.mem_range.mpr (hsup _ hU a (by simp [agentsOf])), rfl⟩⟩)
  | encAD he hk =>
      exact inList (K.filterMap fun t => match t with
          | Term.encA m a => if Term.key (Key.priv a) ∈ K then some m else none
          | _ => none) (by simp [oneStepChunks])
        (List.mem_filterMap.mpr ⟨Term.encA _ _, he, by simp [hk]⟩)
  | hashI hm =>
      exact inList (K.map Term.hash) (by simp [oneStepChunks])
        (List.mem_map.mpr ⟨_, hm, rfl⟩)


/-! ### The saturation step and the iteration -/

/-- The new messages of the universe produced by one enumeration pass.  Split out of
'closeStep' so that 'oneStepList ag K' is computed once per round instead of once per
universe element. -/
def closeStepCore (U : List Term) (new : List Term) : List Term :=
  U.filter (fun t => decide (t ∈ new))

/-- 'closeStep U ag K': one round of the executable saturation.  The attacker keeps
everything it has and adds every message *of the universe* 'U' that is the conclusion of a
deduction-rule instance over 'K'.

The 'U.filter' is the finite-universe restriction of specification sections 2 and 4: it is
what keeps the knowledge set bounded. -/
def closeStep (U : List Term) (ag : Agent) (K : List Term) : List Term :=
  K ++ closeStepCore U (oneStepList ag K)

/-- Characterisation of 'closeStep': a message is known after one round iff it was known
before, or it is in the universe and the enumeration produced it. -/
theorem mem_closeStep {U : List Term} {ag : Agent} {K : List Term} {x : Term} :
    x ∈ closeStep U ag K ↔ x ∈ K ∨ (x ∈ U ∧ x ∈ oneStepList ag K) := by
  unfold closeStep closeStepCore
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]

/-- 'deduce U ag K rounds': the executable Dolev-Yao saturation.  Start from 'K' and apply
'closeStep' exactly 'rounds' times.

The procedure is terminating for two independent reasons: 'rounds' is a 'Nat' supplied from
outside (no fixpoint search), and each round is a finite list operation.  The number of
rounds is a *bound on the depth of attacker derivations the model represents* — the
counterpart, on the deduction side, of the step bound 'L' of specification section 4. -/
def deduce (U : List Term) (ag : Agent) (K : List Term) (rounds : Nat) : List Term :=
  (fun L => closeStep U ag L)^[rounds] K

/-- Zero rounds does nothing. -/
@[simp] theorem deduce_zero (U : List Term) (ag : Agent) (K : List Term) :
    deduce U ag K 0 = K := rfl

/-- One more round is one more 'closeStep'. -/
theorem deduce_succ (U : List Term) (ag : Agent) (K : List Term) (n : Nat) :
    deduce U ag K (n + 1) = closeStep U ag (deduce U ag K n) := by
  simp only [deduce]
  rw [Function.iterate_succ_apply']

/-- Everything initially known stays known. -/
theorem mem_deduce_of_mem {U : List Term} {ag : Agent} {K : List Term} {t : Term}
    (n : Nat) (h : t ∈ K) : t ∈ deduce U ag K n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [deduce_succ, mem_closeStep]
      exact Or.inl ih

/-- **Monotonicity of attacker knowledge in the number of rounds** (specification section
2.3): 'deduce U ag K n ⊆ deduce U ag K (n+1)'. -/
theorem deduce_subset_deduce_succ {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {t : Term} (h : t ∈ deduce U ag K n) : t ∈ deduce U ag K (n + 1) := by
  rw [deduce_succ, mem_closeStep]
  exact Or.inl h

/-- More rounds give more knowledge (iteration of the previous lemma). -/
theorem deduce_subset_deduce {U : List Term} {ag : Agent} {K : List Term} {t : Term}
    {m n : Nat} (hmn : m ≤ n) (h : t ∈ deduce U ag K m) : t ∈ deduce U ag K n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Nat.add_succ]
      exact deduce_subset_deduce_succ ih

/-- The knowledge never leaves 'K ∪ U': the invariant that makes the finite universe a bound
on the analysis. -/
theorem deduce_subset_union {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {t : Term} (h : t ∈ deduce U ag K n) : t ∈ K ∨ t ∈ U := by
  induction n with
  | zero => exact Or.inl h
  | succ n ih =>
      rw [deduce_succ, mem_closeStep] at h
      rcases h with h | ⟨hU, _⟩
      · exact ih h
      · exact Or.inr hU

/-- If the initial knowledge is inside the universe, so is everything the saturation derives:
the finite universe is a *closed* search space, which is what section 4 of the specification
means by an explicitly bounded term universe. -/
theorem deduce_subset_of_subset {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    (hK : ∀ x, x ∈ K → x ∈ U) {t : Term} (h : t ∈ deduce U ag K n) : t ∈ U := by
  have h2 := deduce_subset_union h
  exact h2.elim (fun hk => hK _ hk) (fun hu => hu)

/-- **The one-step round lemma.**  Inside a supported universe, one round of the executable
saturation derives every one-step consequence of the current knowledge. -/
theorem deduce_round {U : List Term} {ag : Agent} {K : List Term} {n : Nat} {t : Term}
    (hsup : supported ag U) (hU : t ∈ U) (h : OneStep (deduce U ag K n) t) :
    t ∈ deduce U ag K (n + 1) := by
  rw [deduce_succ, mem_closeStep]
  exact Or.inr ⟨hU, oneStep_mem hsup hU h⟩

/-! ### Specification 2.1: soundness -/

/-- **Cut / transitivity of deduction.**  If 't' is deducible from 'K'' and every message of
'K'' is deducible from 'K', then 't' is deducible from 'K'.  This is the transitivity of the
consequence relation, and it is what lets the soundness proof below compose the derivations
produced round by round into a single derivation from the initial knowledge. -/
theorem ded_cut {K K' : List Term} {t : Term} (h : Ded K' t)
    (sub : ∀ x, x ∈ K' → Ded K x) : Ded K t := by
  induction h with
  | known hx => exact sub _ hx
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

/-- **Soundness of executable deduction** (specification section 2.1).  Whatever the
executable saturation derives is genuinely deducible in the reference model:

'∀ t ∈ deduce U ag K rounds, Ded K t'.

Note what is *not* assumed: no hypothesis on 'U' (not even 'supported'), no hypothesis on the
number of rounds.  The finite universe only restricts which messages the procedure is
*allowed* to add; everything it does add is justified by an instance of one of the eleven
rules of 'Attacker.OneStep', hence by a 'Ded' derivation.

The proof is an induction on the number of rounds: in round 'n+1' a message is either already
known in round 'n' (induction hypothesis) or it is the conclusion of a rule instance over the
round-'n' knowledge; 'Attacker.oneStep_ded' turns that into a derivation from the round-'n'
knowledge and 'ded_cut' composes it with the round-'n' derivations of all its premises. -/
theorem deduce_sound {U : List Term} {ag : Agent} {K : List Term} {rounds : Nat} :
    ∀ t ∈ deduce U ag K rounds, Ded K t := by
  induction rounds with
  | zero => intro t h; exact Ded.known h
  | succ n ih =>
      intro t h
      rw [deduce_succ, mem_closeStep] at h
      rcases h with h | ⟨_, h⟩
      · exact ih t h
      · exact ded_cut (oneStep_ded (oneStepList_sound ag (deduce U ag K n) t h))
          (fun x hx => ih x hx)

/-! ### Specification 2.3: monotonicity -/

/-- **Monotonicity of attacker knowledge, initial-knowledge direction** (specification
section 2.3).  A larger initial knowledge base yields at least as much derived knowledge, in
the same universe and the same number of rounds.  This is the executable counterpart of
'Attacker.ded_mono'.

The 'supported' hypothesis is only needed to *recognise* a one-step consequence of the larger
base inside the enumeration ('oneStep_mem'); the statement itself is about the executable
procedure, not about the declarative one. -/
theorem deduce_mono {U : List Term} {ag : Agent} {K K' : List Term}
    (sub : ∀ x, x ∈ K → x ∈ K') (hsup : supported ag U) :
    ∀ (n : Nat) {t : Term}, t ∈ deduce U ag K n → t ∈ deduce U ag K' n := by
  intro n
  induction n with
  | zero => intro t h; exact sub _ h
  | succ n ih =>
      intro t h
      rw [deduce_succ, mem_closeStep] at h
      rcases h with h | ⟨hU, hl⟩
      · exact deduce_subset_deduce_succ (ih h)
      · have hos : OneStep (deduce U ag K n) t := oneStepList_sound ag (deduce U ag K n) t hl
        have hos' : OneStep (deduce U ag K' n) t := oneStep_mono (fun _ hx => ih hx) hos
        exact deduce_round hsup hU hos'

/-- Monotonicity of the knowledge base under appending: 'deduce U ag K n ⊆
deduce U ag (x :: K) n'.  The direct analogue of 'Attacker.ded_grow'. -/
theorem deduce_cons {U : List Term} {ag : Agent} {K : List Term} (hsup : supported ag U)
    (x : Term) {n : Nat} {t : Term} (h : t ∈ deduce U ag K n) :
    t ∈ deduce U ag (x :: K) n :=
  deduce_mono (fun _ hx => List.Mem.tail _ hx) hsup n h

/-! ### Specification 2.4: the constructor / destructor pairs, executably -/

/-- **Symmetric round trip, executable form** (specification section 2.4).  If the
saturation knows the ciphertext '{m}_k' and the key 'k' after 'n' rounds, it knows 'm' after
'n+1' rounds.  This is the executable counterpart of 'Attacker.encS_then_decS' (whose proof
is 'Ded.encSD (Ded.encSI hm hk) hk'); the destructor rule of the enumeration is the 'encSD'
chunk of 'oneStepChunks'. -/
theorem encS_decS_step {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {m : Term} {k : Key} (hsup : supported ag U) (hm : m ∈ U)
    (h1 : Term.encS m k ∈ deduce U ag K n) (h2 : Term.key k ∈ deduce U ag K n) :
    m ∈ deduce U ag K (n + 1) :=
  deduce_round hsup hm (OneStep.encSD h1 h2)

/-- **Asymmetric round trip, executable form**: the counterpart of
'Attacker.encA_then_decA'. -/
theorem encA_decA_step {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {m : Term} {a : Agent} (hsup : supported ag U) (hm : m ∈ U)
    (h1 : Term.encA m a ∈ deduce U ag K n) (h2 : Term.key (Key.priv a) ∈ deduce U ag K n) :
    m ∈ deduce U ag K (n + 1) :=
  deduce_round hsup hm (OneStep.encAD h1 h2)

/-- **Pair round trip, executable form**: the counterpart of 'Attacker.pair_then_proj'. -/
theorem pair_proj_step {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {a b : Term} (hsup : supported ag U) (ha : a ∈ U) (hb : b ∈ U)
    (h : Term.pair a b ∈ deduce U ag K n) :
    a ∈ deduce U ag K (n + 1) ∧ b ∈ deduce U ag K (n + 1) :=
  ⟨deduce_round hsup ha (OneStep.fstE h), deduce_round hsup hb (OneStep.sndE h)⟩

/-- The constructor direction of the round trip: one round after the attacker knows a message
and a key it knows the encryption.  Together with 'encS_decS_step' this is the executable
statement that the destructor really inverts the constructor. -/
theorem encS_intro_step {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {m : Term} {k : Key} (hsup : supported ag U) (hm : Term.encS m k ∈ U)
    (h1 : m ∈ deduce U ag K n) (h2 : Term.key k ∈ deduce U ag K n) :
    Term.encS m k ∈ deduce U ag K (n + 1) :=
  deduce_round hsup hm (OneStep.encSI h1 h2)

/-- The pairing constructor, executably. -/
theorem pair_intro_step {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {a b : Term} (hsup : supported ag U) (hp : Term.pair a b ∈ U)
    (h1 : a ∈ deduce U ag K n) (h2 : b ∈ deduce U ag K n) :
    Term.pair a b ∈ deduce U ag K (n + 1) :=
  deduce_round hsup hp (OneStep.pairI h1 h2)

/-- The hashing constructor, executably.  There is no destructor for hashes, which is why no
'hash_*_step' counterpart appears here: '#m' reveals nothing but 'm', and the model has no
rule to recover 'm' from '#m'. -/
theorem hash_intro_step {U : List Term} {ag : Agent} {K : List Term} {n : Nat}
    {m : Term} (hsup : supported ag U) (hm : Term.hash m ∈ U)
    (h : m ∈ deduce U ag K n) : Term.hash m ∈ deduce U ag K (n + 1) :=
  deduce_round hsup hm (OneStep.hashI h)

/-! ### The executable decision procedure -/

/-- 'attackerKnows U ag K t rounds': the executable answer to "can the attacker produce 't'
from 'K' within the universe 'U' in 'rounds' rounds?".  It is a 'Bool', computed by running
the saturation and testing membership, so it can be evaluated by the kernel and discharged by
'decide'.

Its correctness is 'attackerKnows_true' (a 'true' answer is a genuine attack step,
specification 2.1) and 'attackerKnows_false' (a 'false' answer refutes every universe-bounded
derivation, specification 2.2). -/
def attackerKnows (U : List Term) (ag : Agent) (K : List Term) (t : Term)
    (rounds : Nat) : Bool :=
  decide (t ∈ deduce U ag K rounds)

/-- A positive answer of the decision procedure is sound: 'attackerKnows … = true' implies
'Ded K t'. -/
theorem attackerKnows_true {U : List Term} {ag : Agent} {K : List Term} {t : Term}
    {rounds : Nat} (h : attackerKnows U ag K t rounds = true) : Ded K t :=
  deduce_sound t (decide_eq_true_eq.mp h)

/-- The decision procedure is a *test*, not a search: 'attackerKnows U ag K t rounds = true'
and 't ∈ deduce U ag K rounds' are the same proposition. -/
theorem attackerKnows_eq {U : List Term} {ag : Agent} {K : List Term} {t : Term}
    {rounds : Nat} : attackerKnows U ag K t rounds = true ↔ t ∈ deduce U ag K rounds :=
  ⟨fun h => decide_eq_true_eq.mp h, fun h => decide_eq_true_eq.mpr h⟩


/-! ### Specification 2.2: the saturation reaches a fixpoint -/

/-- 'knownCount U K': the number of messages of the universe 'U' the attacker already holds.

This is the *variant* of the saturation loop. It is used only in the fixpoint argument
below, and it is the reason the round bound 'U.length' is the right one: every round that is
not already a fixpoint raises 'knownCount' by at least one, and 'knownCount' can never
exceed 'U.length'. -/
def knownCount : List Term → List Term → Nat
  | [], _ => 0
  | u :: rest, K => if u ∈ K then knownCount rest K + 1 else knownCount rest K

theorem knownCount_le (U K : List Term) : knownCount U K ≤ U.length := by
  induction U with
  | nil => simp [knownCount]
  | cons u rest ih =>
      by_cases hu : u ∈ K
      · simp [knownCount, hu]
        omega
      · simp [knownCount, hu]
        omega

theorem knownCount_cons_mem (u : Term) (rest K : List Term) (hu : u ∈ K) :
    knownCount (u :: rest) K = knownCount rest K + 1 := by
  simp [knownCount, hu]

theorem knownCount_cons_not (u : Term) (rest K : List Term) (hu : ¬ u ∈ K) :
    knownCount (u :: rest) K = knownCount rest K := by
  simp [knownCount, hu]

/-- Growing the knowledge base never decreases the number of known universe messages. -/
theorem knownCount_mono {K K' : List Term} (sub : ∀ x, x ∈ K → x ∈ K') :
    ∀ U : List Term, knownCount U K ≤ knownCount U K' := by
  intro U
  induction U with
  | nil => simp [knownCount]
  | cons u rest ih =>
      by_cases hu : u ∈ K
      · have hu' : u ∈ K' := sub _ hu
        rw [knownCount_cons_mem u rest K hu, knownCount_cons_mem u rest K' hu']
        exact Nat.succ_le_succ ih
      · by_cases hu' : u ∈ K'
        · rw [knownCount_cons_not u rest K hu, knownCount_cons_mem u rest K' hu']
          omega
        · rw [knownCount_cons_not u rest K hu, knownCount_cons_not u rest K' hu']
          exact ih

/-- Learning one new message of the universe raises the count strictly. -/
theorem knownCount_strict (t : Term) :
    ∀ (U : List Term) {K : List Term}, t ∈ U → t ∉ K →
      knownCount U K < knownCount U (t :: K) := by
  intro U
  induction U with
  | nil => intro K hU _; cases hU
  | cons u rest ih =>
      intro K hut htn
      by_cases hu : u ∈ K
      · have hne : t ≠ u := fun e => htn (by rw [e]; exact hu)
        have hrest : t ∈ rest := (List.mem_cons.mp hut).resolve_left hne
        rw [knownCount_cons_mem u rest K hu,
            knownCount_cons_mem u rest (t :: K) (List.mem_cons_of_mem t hu)]
        exact Nat.succ_lt_succ (ih hrest htn)
      · by_cases hut' : t = u
        · rw [knownCount_cons_not u rest K hu]
          subst hut'
          rw [knownCount_cons_mem _ _ _ (by simp)]
          have hmono : knownCount rest K ≤ knownCount rest (t :: K) :=
            knownCount_mono (fun x hx => List.Mem.tail t hx) rest
          omega
        · have hrest : t ∈ rest := (List.mem_cons.mp hut).resolve_left hut'
          have hlt := ih hrest htn
          by_cases hu' : u ∈ t :: K
          · rw [knownCount_cons_not u rest K hu, knownCount_cons_mem u rest (t :: K) hu']
            omega
          · rw [knownCount_cons_not u rest K hu, knownCount_cons_not u rest (t :: K) hu']
            exact hlt

/-- Any growth of the knowledge base that brings in a new universe message raises the count
strictly. -/
theorem knownCount_lt {K K' : List Term} (sub : ∀ x, x ∈ K → x ∈ K') {U : List Term}
    {t : Term} (hU : t ∈ U) (ht : t ∈ K') (htn : t ∉ K) :
    knownCount U K < knownCount U K' := by
  have h1 : knownCount U K < knownCount U (t :: K) := knownCount_strict t U hU htn
  have h2 : knownCount U (t :: K) ≤ knownCount U K' :=
    knownCount_mono (fun x hx => by
      rw [List.mem_cons] at hx
      exact hx.elim (fun e => by rw [e]; exact ht) (fun h => sub x h)) U
  exact Nat.lt_of_lt_of_le h1 h2

/-- 'closedFor U K': the enumeration of one-step consequences adds nothing new to 'K' inside
the universe 'U'. This is the fixpoint property of the saturation. -/
def closedFor (U K : List Term) : Prop :=
  ∀ t ∈ U, OneStep K t → t ∈ K

/-- Once the knowledge is closed, one more round does not change it (as a set of universe
messages), so closedness propagates along the iteration. -/
theorem closedFor_closeStep {ag : Agent} {U K : List Term}
    (h : closedFor U K) : closedFor U (closeStep U ag K) := by
  have sub : ∀ x, x ∈ closeStep U ag K → x ∈ K := by
    intro x hx
    rw [mem_closeStep] at hx
    rcases hx with hx | ⟨hxU, hl⟩
    · exact hx
    · exact h x hxU (oneStepList_sound ag K x hl)
  intro t htU hos
  exact mem_closeStep.mpr (Or.inl (h t htU (oneStep_mono sub hos)))

/-- A round that is not a fixpoint raises the count of known universe messages. -/
theorem not_closedFor_growth {ag : Agent} {U K : List Term} (hsup : supported ag U)
    (h : ¬ closedFor U K) : knownCount U K < knownCount U (closeStep U ag K) := by
  rw [closedFor] at h
  push Not at h
  obtain ⟨t, htU, hos, htn⟩ := h
  have sub : ∀ x, x ∈ K → x ∈ closeStep U ag K := fun x hx => mem_closeStep.mpr (Or.inl hx)
  have ht : t ∈ closeStep U ag K :=
    mem_closeStep.mpr (Or.inr ⟨htU, oneStep_mem hsup htU hos⟩)
  exact knownCount_lt sub htU ht htn

/-- **The saturation reaches a fixpoint within '|U| rounds.** For every universe and every
initial knowledge base there is a round 'm ≤ U.length' at which the knowledge is closed under
the deduction rules inside 'U'.

The proof is the classical counting argument: a round that is not a fixpoint adds a new
message of 'U' (by completeness of the enumeration, 'oneStep_mem'), so the number of known
universe messages grows by at least one; that number is bounded by 'U.length'; hence after
'U.length' rounds the growth must have stopped. -/
theorem exists_closedFor {ag : Agent} {U K : List Term} (hsup : supported ag U) :
    ∃ m, m ≤ U.length ∧ closedFor U (deduce U ag K m) := by
  by_contra hc
  push Not at hc
  have grow : ∀ m, m ≤ U.length →
      knownCount U (deduce U ag K m) < knownCount U (deduce U ag K (m + 1)) := by
    intro m hm
    rw [deduce_succ]
    exact not_closedFor_growth hsup (hc m hm)
  have key : ∀ m, m ≤ U.length + 1 →
      knownCount U (deduce U ag K 0) + m ≤ knownCount U (deduce U ag K m) := by
    intro m
    induction m with
    | zero => intro _; omega
    | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := grow m (by omega)
        omega
  have h0 := key (U.length + 1) (by omega)
  have h1 := knownCount_le U (deduce U ag K (U.length + 1))
  have h2 : 0 ≤ knownCount U (deduce U ag K 0) := Nat.zero_le _
  omega

/-- **Fixpoint theorem for the executable saturation** (specification section 2.2). After
'U.length' rounds — and hence after any larger number of rounds — the knowledge base is
closed under the deduction rules inside the universe: every one-step consequence of what the
attacker knows that lies in the universe is already known.

This is the statement that turns "the enumeration is complete for one step" ('oneStep_mem')
into "the saturation is complete for arbitrarily nested derivations" ('dedIn_deduce'). -/
theorem deduce_closed {ag : Agent} {U K : List Term} {n : Nat} (hsup : supported ag U)
    (hn : U.length ≤ n) : closedFor U (deduce U ag K n) := by
  obtain ⟨m, hm, hclosed⟩ := exists_closedFor hsup
  have step : ∀ k : Nat, closedFor U (deduce U ag K (m + k)) := by
    intro k
    induction k with
    | zero => simpa using hclosed
    | succ k ih =>
        rw [Nat.add_succ, Nat.succ_eq_add_one, deduce_succ]
        exact closedFor_closeStep ih
  have hmn : m ≤ n := Nat.le_trans hm hn
  have := step (n - m)
  rwa [Nat.add_sub_of_le hmn] at this


/-! ### Specification 2.2: completeness relative to the finite universe -/

/-- 'DedIn U K t': the message 't' is deducible from 'K' by a derivation in which **every
message the attacker produces lies in 'U'**.

'DedIn' mirrors 'Attacker.Ded' rule for rule; the only difference is the side condition
't ∈ U' on every conclusion (for the destructor rules, on the message recovered). Those side
conditions are what makes a completeness statement for the executable saturation true: the
saturation only ever adds messages of 'U' ('deduce_subset_union'), so a derivation that
leaves 'U' — the attacker builds a pair that is not in the universe and then projects it —
cannot be simulated by it, and no finite universe is closed under every such detour.

Section 2.2 of the specification asks for completeness "relative to the supported finite
universe", and this is the precise form of that requirement: 'dedIn_deduce' proves that
'U.length' rounds of the executable procedure derive everything 'DedIn' derives, and
'ded_dedIn' proves that every 'Ded' derivation can be relocated into a suitable universe, so
the restriction costs nothing in principle. -/
inductive DedIn : List Term → List Term → Term → Prop
  | known : ∀ {U K t}, t ∈ K → t ∈ U → DedIn U K t
  | agent : ∀ {U K A}, Term.agent A ∈ U → DedIn U K (Term.agent A)
  | pub : ∀ {U K A}, Term.key (Key.pub A) ∈ U → DedIn U K (Term.key (Key.pub A))
  | pairI : ∀ {U K a b}, DedIn U K a → DedIn U K b → Term.pair a b ∈ U →
      DedIn U K (Term.pair a b)
  | fstE : ∀ {U K a b}, DedIn U K (Term.pair a b) → a ∈ U → DedIn U K a
  | sndE : ∀ {U K a b}, DedIn U K (Term.pair a b) → b ∈ U → DedIn U K b
  | encSI : ∀ {U K m k}, DedIn U K m → DedIn U K (Term.key k) → Term.encS m k ∈ U →
      DedIn U K (Term.encS m k)
  | encSD : ∀ {U K m k}, DedIn U K (Term.encS m k) → DedIn U K (Term.key k) → m ∈ U →
      DedIn U K m
  | encAI : ∀ {U K m a}, DedIn U K m → Term.encA m a ∈ U → DedIn U K (Term.encA m a)
  | encAD : ∀ {U K m a}, DedIn U K (Term.encA m a) → DedIn U K (Term.key (Key.priv a)) →
      m ∈ U → DedIn U K m
  | hashI : ∀ {U K m}, DedIn U K m → Term.hash m ∈ U → DedIn U K (Term.hash m)

/-- Every universe-bounded derivation is a real derivation: 'DedIn U K t → Ded K t'.  The
universe conditions are simply dropped, so this is the "soundness of the restricted model"
direction of the correspondence between 'Ded' and 'DedIn'. -/
theorem dedIn_ded {U K t} (h : DedIn U K t) : Ded K t := by
  induction h with
  | known hx _ => exact Ded.known hx
  | agent _ => exact Ded.agent
  | pub _ => exact Ded.pub
  | pairI _ _ _ ih1 ih2 => exact Ded.pairI ih1 ih2
  | fstE _ _ ih => exact Ded.fstE ih
  | sndE _ _ ih => exact Ded.sndE ih
  | encSI _ _ _ ih1 ih2 => exact Ded.encSI ih1 ih2
  | encSD _ _ _ ih1 ih2 => exact Ded.encSD ih1 ih2
  | encAI _ _ ih => exact Ded.encAI ih
  | encAD _ _ _ ih1 ih2 => exact Ded.encAD ih1 ih2
  | hashI _ _ ih => exact Ded.hashI ih

/-- Every message derived by a 'DedIn' derivation lies in the universe: this is exactly what
the side conditions of the inductive predicate enforce, and it is the reason the completeness
proof below can use the fixpoint theorem. -/
theorem dedIn_concl_mem {U K t} (h : DedIn U K t) : t ∈ U := by
  induction h with
  | known _ hu => exact hu
  | agent hu => exact hu
  | pub hu => exact hu
  | pairI _ _ hu _ _ => exact hu
  | fstE _ hu _ => exact hu
  | sndE _ hu _ => exact hu
  | encSI _ _ hu _ _ => exact hu
  | encSD _ _ hu _ _ => exact hu
  | encAI _ hu _ => exact hu
  | encAD _ _ hu _ _ => exact hu
  | hashI _ hu _ => exact hu

/-- 'DedIn' is monotone in the universe: a derivation that lives in 'U' also lives in any
larger universe.  Used to relocate derivations into a bigger universe when several derivations
are combined. -/
theorem dedIn_mono {U K t} (h : DedIn U K t) :
    ∀ {U' : List Term}, (∀ x, x ∈ U → x ∈ U') → DedIn U' K t := by
  intro U' sub
  induction h with
  | known hx hu => exact DedIn.known hx (sub _ hu)
  | agent hu => exact DedIn.agent (sub _ hu)
  | pub hu => exact DedIn.pub (sub _ hu)
  | pairI _ _ hu ih1 ih2 => exact DedIn.pairI ih1 ih2 (sub _ hu)
  | fstE _ hu ih => exact DedIn.fstE ih (sub _ hu)
  | sndE _ hu ih => exact DedIn.sndE ih (sub _ hu)
  | encSI _ _ hu ih1 ih2 => exact DedIn.encSI ih1 ih2 (sub _ hu)
  | encSD _ _ hu ih1 ih2 => exact DedIn.encSD ih1 ih2 (sub _ hu)
  | encAI _ hu ih => exact DedIn.encAI ih (sub _ hu)
  | encAD _ _ hu ih1 ih2 => exact DedIn.encAD ih1 ih2 (sub _ hu)
  | hashI _ hu ih => exact DedIn.hashI ih (sub _ hu)

/-- **Completeness of the executable saturation relative to the finite universe**
(specification section 2.2).  If 't' has a derivation that stays inside 'U', the universe 'U'
is supported by the agent domain 'ag', and the number of rounds is at least '|U|', then the
executable saturation derives 't'.

Contrapositively: whatever the saturation misses after '|U|' rounds is not deducible from 'K'
by any derivation that stays inside 'U'.

The proof is an induction on the 'DedIn' derivation.  Each rule instance is discharged by the
fixpoint theorem 'deduce_closed': because 'U.length' rounds are enough to reach a fixpoint,
the round-'n' knowledge is closed under one step, so a rule whose premises are already known
(and whose conclusion is in 'U') has its conclusion known as well.  Without the fixpoint
theorem the induction would need the derivation depth as an extra parameter. -/
theorem dedIn_deduce {U K t} (h : DedIn U K t) :
    ∀ {ag : Agent}, supported ag U → ∀ {n : Nat}, U.length ≤ n → t ∈ deduce U ag K n := by
  induction h with
  | known hx _ =>
      intro ag hsup n hn
      exact mem_deduce_of_mem n hx
  | agent htU =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU OneStep.agent
  | pub htU =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU OneStep.pub
  | pairI _ _ htU ih1 ih2 =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.pairI (ih1 hsup hn) (ih2 hsup hn))
  | fstE _ htU ih =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.fstE (ih hsup hn))
  | sndE _ htU ih =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.sndE (ih hsup hn))
  | encSI _ _ htU ih1 ih2 =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.encSI (ih1 hsup hn) (ih2 hsup hn))
  | encSD _ _ htU ih1 ih2 =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.encSD (ih1 hsup hn) (ih2 hsup hn))
  | encAI _ htU ih =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.encAI (ih hsup hn))
  | encAD _ _ htU ih1 ih2 =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.encAD (ih1 hsup hn) (ih2 hsup hn))
  | hashI _ htU ih =>
      intro ag hsup n hn
      exact (deduce_closed hsup hn) _ htU (OneStep.hashI (ih hsup hn))

/-- A negative answer of the executable test refutes every universe-bounded derivation: if
'attackerKnows' says 'false', the universe is supported and the round bound is at least '|U|',
then 't' is *not* derivable inside the universe.  Together with 'attackerKnows_true' this is
the correctness of the decision procedure. -/
theorem attackerKnows_false {U : List Term} {ag : Agent} {K : List Term} {t : Term}
    {rounds : Nat} (h : attackerKnows U ag K t rounds = false) (hsup : supported ag U)
    (hn : U.length ≤ rounds) : ¬ DedIn U K t := by
  intro hd
  have hmem : t ∈ deduce U ag K rounds := dedIn_deduce hd hsup hn
  have htrue : attackerKnows U ag K t rounds = true := decide_eq_true_eq.mpr hmem
  rw [htrue] at h
  exact Bool.false_ne_true h.symm



/-! ### The finite-universe restriction costs nothing in principle -/

/-- The least agent-domain bound that supports a single message: one more than the largest
agent index the message mentions. -/
def agentBound : Term → Agent
  | Term.agent A => A + 1
  | Term.key (Key.pub A) => A + 1
  | Term.encA _ a => a + 1
  | _ => 0

/-- The least agent-domain bound that supports a list of messages. -/
def agentBoundL (U : List Term) : Agent := (U.map agentBound).foldr max 0

theorem lt_agentBound {t : Term} {A : Agent} (h : A ∈ agentsOf t) : A < agentBound t := by
  cases t with
  | agent A' => simp_all [agentsOf, agentBound]
  | nonce _ => simp [agentsOf] at h
  | key k' =>
      cases k' with
      | pub A' => simp_all [agentsOf, agentBound]
      | shrk _ _ => simp [agentsOf] at h
      | priv _ => simp [agentsOf] at h
  | pair _ _ => simp [agentsOf] at h
  | encS _ _ => simp [agentsOf] at h
  | encA _ a' => simp_all [agentsOf, agentBound]
  | hash _ => simp [agentsOf] at h

theorem le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons x rest ih =>
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Every list of messages is supported by a large enough agent domain: 'supported' is a
condition on the *universe*, not a restriction on what can be expressed. -/
theorem supported_agentBoundL (U : List Term) : supported (agentBoundL U) U := by
  intro t ht A hA
  have h1 : A < agentBound t := lt_agentBound hA
  have h2 : agentBound t ≤ agentBoundL U := le_foldr_max (List.mem_map.mpr ⟨t, ht, rfl⟩)
  exact Nat.lt_of_lt_of_le h1 h2

/-- Every 'Ded' derivation can be *relocated* into a finite universe: there is a list 'U' such
that the same derivation is a 'DedIn U' derivation.  The construction walks the derivation and
collects, for each rule instance, the messages it needs; the universe is finite because the
derivation is.

Together with 'dedIn_deduce' this is the sense in which the finite-universe restriction of
specification section 2.2 costs nothing in principle: the bound is not an approximation of the
attacker's power, it is a bound on *which* derivations the analysis represents. -/
theorem ded_dedIn_univ {K t} (h : Ded K t) : ∃ U : List Term, DedIn U K t := by
  induction h with
  | known hx =>
      rename_i m
      exact ⟨[m], DedIn.known hx (by simp)⟩
  | agent =>
      rename_i A
      exact ⟨[Term.agent A], DedIn.agent (by simp)⟩
  | pub =>
      rename_i A
      exact ⟨[Term.key (Key.pub A)], DedIn.pub (by simp)⟩
  | pairI hp1 hp2 ih1 ih2 =>
      rename_i a b
      obtain ⟨U1, d1⟩ := ih1
      obtain ⟨U2, d2⟩ := ih2
      refine ⟨U1 ++ U2 ++ [Term.pair a b],
        DedIn.pairI (dedIn_mono d1 (by intro z hz; simp [hz]))
          (dedIn_mono d2 (by intro z hz; simp [hz])) (by simp)⟩
  | fstE hp ih =>
      rename_i a b
      obtain ⟨U, d⟩ := ih
      exact ⟨U ++ [a], DedIn.fstE (dedIn_mono d (by intro z hz; simp [hz])) (by simp)⟩
  | sndE hp ih =>
      rename_i a b
      obtain ⟨U, d⟩ := ih
      exact ⟨U ++ [b], DedIn.sndE (dedIn_mono d (by intro z hz; simp [hz])) (by simp)⟩
  | encSI hp1 hp2 ih1 ih2 =>
      rename_i m k
      obtain ⟨U1, d1⟩ := ih1
      obtain ⟨U2, d2⟩ := ih2
      refine ⟨U1 ++ U2 ++ [Term.encS m k],
        DedIn.encSI (dedIn_mono d1 (by intro z hz; simp [hz]))
          (dedIn_mono d2 (by intro z hz; simp [hz])) (by simp)⟩
  | encSD hp1 hp2 ih1 ih2 =>
      rename_i m k
      obtain ⟨U1, d1⟩ := ih1
      obtain ⟨U2, d2⟩ := ih2
      refine ⟨U1 ++ U2 ++ [m],
        DedIn.encSD (dedIn_mono d1 (by intro z hz; simp [hz]))
          (dedIn_mono d2 (by intro z hz; simp [hz])) (by simp)⟩
  | encAI hp ih =>
      rename_i m a
      obtain ⟨U, d⟩ := ih
      exact ⟨U ++ [Term.encA m a],
        DedIn.encAI (dedIn_mono d (by intro z hz; simp [hz])) (by simp)⟩
  | encAD hp1 hp2 ih1 ih2 =>
      rename_i m a
      obtain ⟨U1, d1⟩ := ih1
      obtain ⟨U2, d2⟩ := ih2
      refine ⟨U1 ++ U2 ++ [m],
        DedIn.encAD (dedIn_mono d1 (by intro z hz; simp [hz]))
          (dedIn_mono d2 (by intro z hz; simp [hz])) (by simp)⟩
  | hashI hp ih =>
      rename_i m
      obtain ⟨U, d⟩ := ih
      exact ⟨U ++ [Term.hash m],
        DedIn.hashI (dedIn_mono d (by intro z hz; simp [hz])) (by simp)⟩

/-- **No loss of generality.**  Every declarative derivation 'Ded K t' takes place inside some
supported finite universe: 'ded_dedIn' produces the universe and the agent-domain bound. -/
theorem ded_dedIn {K t} (h : Ded K t) :
    ∃ (U : List Term) (ag : Agent), supported ag U ∧ DedIn U K t := by
  obtain ⟨U, hd⟩ := ded_dedIn_univ h
  exact ⟨U, agentBoundL U, supported_agentBoundL U, hd⟩

/-- **Completeness in the limit** (specification section 2.2, final form).  Every message the
declarative attacker can deduce is found by the executable saturation in a suitable finite
universe with a suitable number of rounds: the executable procedure is not an
under-approximation of the attacker's power, only of the *messages the analysis admits*. -/
theorem ded_deduce {K t} (h : Ded K t) :
    ∃ (U : List Term) (ag : Agent) (n : Nat), t ∈ deduce U ag K n := by
  obtain ⟨U, ag, hsup, hd⟩ := ded_dedIn h
  exact ⟨U, ag, U.length, dedIn_deduce hd hsup (Nat.le_refl _)⟩


/-! ### Deciding the support hypothesis -/

/-- The executable test for 'supported'.  The hypothesis quantifies over the finitely many
messages of the universe, so it is decidable; 'supported_of_supportedBool' lets a concrete
universe be discharged with 'decide'. -/
def supportedBool (ag : Agent) (U : List Term) : Bool :=
  U.all fun t => (agentsOf t).all fun A => decide (A < ag)

/-- If the executable test says 'true' then the universe really is supported. -/
theorem supported_of_supportedBool {ag : Agent} {U : List Term}
    (h : supportedBool ag U = true) : supported ag U := by
  intro t ht A hA
  have h1 : ∀ t' ∈ U, (agentsOf t').all (fun A => decide (A < ag)) = true :=
    List.all_eq_true.mp h
  have h2 : (agentsOf t).all (fun A' => decide (A' < ag)) = true := h1 t ht
  have h3 : ∀ A' ∈ agentsOf t, decide (A' < ag) = true := List.all_eq_true.mp h2
  exact decide_eq_true_eq.mp (h3 A hA)

/-- The test is complete: a supported universe passes it. -/
theorem supportedBool_of_supported {ag : Agent} {U : List Term} (h : supported ag U) :
    supportedBool ag U = true := by
  rw [supportedBool, List.all_eq_true]
  intro t ht
  rw [List.all_eq_true]
  intro A hA
  exact decide_eq_true_eq.mpr (h t ht A hA)

/-! ### Executable examples -/

/-- The universe of the symmetric-key example: a nonce, a long-term key, and the ciphertext of
the nonce under that key. -/
def U_sym : List Term :=
  [Term.nonce 7, Term.key (Key.shrk 0 1), Term.encS (Term.nonce 7) (Key.shrk 0 1)]

/-- The attacker holds the key *and* the ciphertext: the "long-term key compromised" scenario. -/
def K_sym : List Term := [Term.key (Key.shrk 0 1), Term.encS (Term.nonce 7) (Key.shrk 0 1)]

/-- The universe mentions only agent index 0, so it is supported by the one-agent domain. -/
theorem supported_sym : supported 1 U_sym :=
  supported_of_supportedBool (by decide)

/-- **Example 1 — the symmetric destructor, executable.**  A known symmetric key lets the
attacker decrypt a ciphertext built from known parts: one round of the saturation finds the
plaintext. -/
example : Term.nonce 7 ∈ deduce U_sym 1 K_sym 1 := by decide

/-- The same fact through the Boolean decision procedure. -/
example : attackerKnows U_sym 1 K_sym (Term.nonce 7) 1 = true := by decide

/-- ... and its soundness consequence: the executable answer really is a 'Ded' derivation in the
reference model (specification 2.1). -/
example : Ded K_sym (Term.nonce 7) :=
  deduce_sound (Term.nonce 7) (by decide : Term.nonce 7 ∈ deduce U_sym 1 K_sym 1)

/-- The destructor law of specification 2.4 applied to the saturation rather than checked by
'decide': the ciphertext and the key are known at round 0 (they are initial knowledge), so the
plaintext is known at round 1. -/
example : Term.nonce 7 ∈ deduce U_sym 1 K_sym 1 :=
  encS_decS_step (n := 0) (k := Key.shrk 0 1) supported_sym (by decide)
    (mem_deduce_of_mem 0 (by decide :
      Term.encS (Term.nonce 7) (Key.shrk 0 1) ∈ K_sym))
    (mem_deduce_of_mem 0 (by decide : Term.key (Key.shrk 0 1) ∈ K_sym))

/-- **Example 2 — pair projections and pairing.**  Both components of a known pair are
deducible, and the pair of two known messages is deducible. -/
def U_pair : List Term :=
  [Term.nonce 3, Term.agent 0, Term.pair (Term.nonce 3) (Term.agent 0)]

/-- The attacker overheard one pair. -/
def K_pair : List Term := [Term.pair (Term.nonce 3) (Term.agent 0)]

theorem supported_pair : supported 1 U_pair :=
  supported_of_supportedBool (by decide)

example : Term.nonce 3 ∈ deduce U_pair 1 K_pair 1 := by decide
example : Term.agent 0 ∈ deduce U_pair 1 K_pair 1 := by decide
example : Ded K_pair (Term.nonce 3) :=
  deduce_sound (Term.nonce 3) (by decide : Term.nonce 3 ∈ deduce U_pair 1 K_pair 1)

/-- The constructor direction: from two known messages the pair is known in one round. -/
example : Term.pair (Term.nonce 3) (Term.agent 0) ∈
    deduce U_pair 1 [Term.nonce 3, Term.agent 0] 1 := by decide

/-- **Example 3 — the asymmetric destructor.**  A private key decrypts a message encrypted for
that agent. -/
def U_asym : List Term := [Term.nonce 5, Term.key (Key.priv 0), Term.encA (Term.nonce 5) 0]

/-- The attacker holds the private key of agent 0 and the ciphertext addressed to it. -/
def K_asym : List Term := [Term.encA (Term.nonce 5) 0, Term.key (Key.priv 0)]

theorem supported_asym : supported 1 U_asym :=
  supported_of_supportedBool (by decide)

example : Term.nonce 5 ∈ deduce U_asym 1 K_asym 1 := by decide
example : Ded K_asym (Term.nonce 5) :=
  deduce_sound (Term.nonce 5) (by decide : Term.nonce 5 ∈ deduce U_asym 1 K_asym 1)

/-- **Example 4 — a two-round attack.**  The attacker first decrypts with the key it has, then
re-encrypts the plaintext under a second key it also has.  The re-encryption is *not* reachable
in one round: the enumeration of a round only uses the knowledge of the previous round. -/
def U_two : List Term :=
  [Term.nonce 7, Term.key (Key.shrk 0 1), Term.key (Key.shrk 0 2),
    Term.encS (Term.nonce 7) (Key.shrk 0 1), Term.encS (Term.nonce 7) (Key.shrk 0 2)]

/-- The attacker knows both keys and the first ciphertext, but not the plaintext. -/
def K_two : List Term :=
  [Term.key (Key.shrk 0 1), Term.key (Key.shrk 0 2), Term.encS (Term.nonce 7) (Key.shrk 0 1)]

theorem supported_two : supported 1 U_two :=
  supported_of_supportedBool (by decide)

example : ¬ (Term.encS (Term.nonce 7) (Key.shrk 0 2) ∈ deduce U_two 1 K_two 1) := by decide
example : Term.encS (Term.nonce 7) (Key.shrk 0 2) ∈ deduce U_two 1 K_two 2 := by decide
example : Ded K_two (Term.encS (Term.nonce 7) (Key.shrk 0 2)) :=
  deduce_sound (Term.encS (Term.nonce 7) (Key.shrk 0 2))
    (by decide : Term.encS (Term.nonce 7) (Key.shrk 0 2) ∈ deduce U_two 1 K_two 2)

/-- **Example 5 — a nonce that is never sent is not deducible.**  The nonce '9' is *in* the
universe (so the negative answer is not an artefact of the bound), the round bound is above the
fixpoint bound '|U|', and the executable test says 'false'. -/
def U_neg : List Term :=
  [Term.nonce 9, Term.key (Key.shrk 0 1), Term.encS (Term.nonce 7) (Key.shrk 0 1)]

/-- The attacker knows the key and the ciphertext of nonce 7 — but never saw nonce 9. -/
def K_neg : List Term := [Term.key (Key.shrk 0 1), Term.encS (Term.nonce 7) (Key.shrk 0 1)]

theorem supported_neg : supported 1 U_neg :=
  supported_of_supportedBool (by decide)

example : ¬ (Term.nonce 9 ∈ deduce U_neg 1 K_neg 3) := by decide
example : attackerKnows U_neg 1 K_neg (Term.nonce 9) 3 = false := by decide

/-- The negative answer is a *certificate*: no universe-bounded derivation of the message exists
(specification 2.2, the direction 'attackerKnows_false'). -/
example : ¬ DedIn U_neg K_neg (Term.nonce 9) :=
  attackerKnows_false (ag := 1) (rounds := 3) (by decide) supported_neg (by decide)

/-- and the reference model agrees, by the freshness theorem of 'ProtSat.Attacker': every nonce
of a deducible message already occurs in the knowledge base. -/
example : ¬ Ded K_neg (Term.nonce 9) := by
  intro hd
  have h1 := Attacker.no_fresh_nonces hd
  have h2 : (9 : NonceName) ∈ (Term.nonce 9).nonces := by simp [Term.nonces]
  have h3 : (9 : NonceName) ∈ Attacker.noncesOf K_neg := h1 h2
  have h4 : (9 : NonceName) ∉ Attacker.noncesOf K_neg := by decide
  exact h4 h3

/-- **Example 6 — hashing.**  The attacker can hash what it knows; a hash reveals nothing, so
there is no rule going the other way. -/
def U_hash : List Term := [Term.nonce 4, Term.hash (Term.nonce 4)]

/-- The attacker knows the nonce. -/
def K_hash : List Term := [Term.nonce 4]

theorem supported_hash : supported 1 U_hash :=
  supported_of_supportedBool (by decide)

example : Term.hash (Term.nonce 4) ∈ deduce U_hash 1 K_hash 1 := by decide
example : Ded K_hash (Term.hash (Term.nonce 4)) :=
  deduce_sound (Term.hash (Term.nonce 4))
    (by decide : Term.hash (Term.nonce 4) ∈ deduce U_hash 1 K_hash 1)

/-- **Example 7 — the public initial material.**  Agent names and public keys of the bounded
domain are deducible even with an empty knowledge base. -/
example : Term.key (Key.pub 0) ∈ deduce [Term.key (Key.pub 0)] 1 [] 1 := by decide
example : Term.agent 0 ∈ deduce [Term.agent 0] 1 [] 1 := by decide

/-- **Example 8 — the finite universe really is a restriction.**  'Term.nonce 7' is deducible
from 'K_sym' in the reference model (Example 1), but if the universe does not contain it the
executable saturation never adds it: the analysis answers 'false' for a message outside its
declared universe.  This is the honest content of "completeness relative to the supported finite
universe". -/
example : ¬ (Term.nonce 7 ∈ deduce [Term.key (Key.shrk 0 1)] 1 K_sym 3) := by decide

end ProtSat.Deduce
