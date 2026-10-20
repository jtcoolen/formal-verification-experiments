/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Complete
import ProtSat.Represent

/-!
# ProtSat: the universe is subterm-closed by construction

## Why this module exists

`Complete.univSub` asks that every subterm of every universe message is itself a universe message:

    univSub sh : Prop := ∀ t ∈ sh.U, ∀ u ∈ subtermsL t, u ∈ sh.U

It is carried as a hypothesis by `Complete.encoding_complete` and by every bridge that consumes it -
`Correspondence`, `CheckedSafe`, `Sound`, `Refute`, `AuthGap` - and each of those sites currently
discharges it by `decide` on a concrete protocol, which proves the fact about an example and says
nothing about the construction.

But the construction is the reason it is true. `Bounded.univ` is built as

    (closeOne P.agents (domainKeys P.agents))^[B.rounds] (subtermClosureL (seeds P)) |>.eraseDups

whose base is subterm-closed by `Bounded.subtermClosureL_closed`, whose seeds already contain every
agent and every domain key, and whose one round only ever builds `pair x y`, `encS m k`, `encA m a`
and `hash m` out of messages the round already has - so the subterms of anything it adds were
already present. Subterm-closure is therefore a theorem of the universe, not a condition the user
must arrange. This module proves it:

    univSub_shapeOf : univSub (shapeOf P B)

## Why this is stated separately rather than by deleting the hypothesis

Deleting `hsub` from fifteen signatures is a mechanical but wide change, and a wide change is easier
to review when the lemma it relies on already exists and is checked. This file is that lemma. The
deletion is the next step, and it becomes a one-line substitution of `Closure.univSub_shapeOf` for
a discharged hypothesis at each site.

## What this does not do

It says nothing about the other two shape conditions. `Encode.univClosed` is a genuine bound-
adequacy property - a too-small universe is exactly what it rules out, and the analyser reports it
as `boundsTooSmall` rather than proving it. And `Complete.SecretsOK` is half bound-adequacy (a
declared secret the CNF cannot name makes the violation clause empty, which is what
`AuthGap.violationLits_nonempty` is about) and half provable; splitting it is separate work.
-/

namespace ProtSat.Closure

open ProtSat Term Bounded Complete Encode

/-- A list of messages is **subterm-closed** when it contains the subterms of each of its members.
`univSub` is this predicate read at a shape's universe. -/
def SubtermClosed (L : List Term) : Prop := ∀ t ∈ L, ∀ u ∈ subtermsL t, u ∈ L

/-- The subterm closure of any seed list is subterm-closed: that is what `subtermClosureL` is for. -/
theorem subtermClosureL_SubtermClosed (S : List Term) : SubtermClosed (subtermClosureL S) := by
  intro t ht u hu
  exact subtermClosureL_closed ht hu

/-- A message of the base list survives every closure round: `closeOne` never removes anything. -/
theorem mem_iterate_closeOne {ag : List Agent} {ks : List Key} {U : List Term} (t : Term)
    (ht : t ∈ U) : ∀ n, t ∈ ((fun W => closeOne ag ks W)^[n] U) := by
  intro n
  induction n with
  | zero => exact ht
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact mem_closeOne ih

theorem mem_closeOne_pair {ag : List Agent} {ks : List Key} {U : List Term} {x y : Term}
    (hx : x ∈ U) (hy : y ∈ U) : Term.pair x y ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, y, hy, rfl⟩)))

theorem mem_closeOne_encS {ag : List Agent} {ks : List Key} {U : List Term} {m : Term} {k : Key}
    (hm : m ∈ U) (hk : k ∈ ks) : Term.encS m k ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨m, hm, k, hk, rfl⟩))

theorem mem_closeOne_encA {ag : List Agent} {ks : List Key} {U : List Term} {m : Term} {a : Agent}
    (hm : m ∈ U) (ha : a ∈ ag) : Term.encA m a ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨m, hm, a, ha, rfl⟩)

theorem mem_closeOne_hash {ag : List Agent} {ks : List Key} {U : List Term} {m : Term}
    (hm : m ∈ U) : Term.hash m ∈ closeOne ag ks U := by
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inr ⟨m, hm, rfl⟩
/-- **One closure round adds nothing whose subterms were not already present.** Each generated
message is built from a base message, so its parts are base messages or their subterms; the agents
and keys it may mention are in the base by hypothesis. -/
theorem subtermsL_subset_closeOne {ag : List Agent} {ks : List Key} {U : List Term}
    (hU : SubtermClosed U) (hag : ∀ a ∈ ag, Term.agent a ∈ U)
    (hks : ∀ k ∈ ks, Term.key k ∈ U) {t : Term} (ht : t ∈ closeOne ag ks U) :
    subtermsL t ⊆ closeOne ag ks U := by
  have hUin : ∀ s, s ∈ U -> s ∈ closeOne ag ks U := fun s hs => mem_closeOne hs
  have hsubU : ∀ s, s ∈ U -> subtermsL s ⊆ closeOne ag ks U := fun s hs u hu =>
    mem_closeOne (hU s hs u hu)
  simp only [closeOne, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map] at ht
  intro u hu
  rcases ht with (((hU' | ⟨x, hx, y, hy, rfl⟩) | ⟨m, hm, k, hk, rfl⟩) | ⟨m, hm, a, ha, rfl⟩)
    | ⟨m, hm, rfl⟩
  · exact hsubU t hU' hu
  · have hmem : u ∈ Term.pair x y :: subtermsL x ++ subtermsL y := hu
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with (rfl | hz) | hz
    · exact mem_closeOne_pair hx hy
    · exact hsubU x hx hz
    · exact hsubU y hy hz
  · have hmem : u ∈ Term.encS m k :: subtermsL m ++ [Term.key k] := hu
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with (rfl | hz) | (rfl | hnil)
    · exact mem_closeOne_encS hm hk
    · exact hsubU m hm hz
    · exact hUin _ (hks k hk)
    · cases hnil
  · have hmem : u ∈ Term.encA m a :: subtermsL m ++ [Term.agent a] := hu
    simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with (rfl | hz) | (rfl | hnil)
    · exact mem_closeOne_encA hm ha
    · exact hsubU m hm hz
    · exact hUin _ (hag a ha)
    · cases hnil
  · have hmem : u ∈ Term.hash m :: subtermsL m := hu
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hz
    · exact mem_closeOne_hash hm
    · exact hsubU m hm hz
/-- **One closure round preserves subterm-closure**, provided the agents and keys it closes under
are already present - which they are, because the seeds put them in the base. -/
theorem SubtermClosed.mono_closeOne {ag : List Agent} {ks : List Key} {U : List Term}
    (hU : SubtermClosed U) (hag : ∀ a ∈ ag, Term.agent a ∈ U)
    (hks : ∀ k ∈ ks, Term.key k ∈ U) : SubtermClosed (closeOne ag ks U) := fun t ht u hu =>
  subtermsL_subset_closeOne hU hag hks ht hu

/-- Subterm-closure survives every number of closure rounds. -/
theorem SubtermClosed.iterate {ag : List Agent} {ks : List Key} {U : List Term}
    (hU : SubtermClosed U) (hag : ∀ a ∈ ag, Term.agent a ∈ U)
    (hks : ∀ k ∈ ks, Term.key k ∈ U) :
    ∀ n, SubtermClosed ((fun W => closeOne ag ks W)^[n] U) := by
  intro n
  induction n with
  | zero => exact hU
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ih.mono_closeOne ?_ ?_
      · intro a ha
        exact mem_iterate_closeOne _ (hag a ha) n
      · intro k hk
        exact mem_iterate_closeOne _ (hks k hk) n

/-- Removing duplicates preserves subterm-closure. -/
theorem SubtermClosed.eraseDups {U : List Term} (h : SubtermClosed U) :
    SubtermClosed U.eraseDups := by
  intro t ht u hu
  apply List.mem_eraseDups.mpr
  exact h t (List.mem_eraseDups.mp ht) u hu

/-- **The universe of a protocol under any bounds is subterm-closed.** The base is the subterm
closure of the seeds, the seeds already contain every agent and every domain key, and each round
only builds messages out of parts it already had. -/
theorem univ_SubtermClosed (P : Protocol) (B : Bounds) : SubtermClosed (univ P B) := by
  have hbase : SubtermClosed (subtermClosureL (seeds P)) := subtermClosureL_SubtermClosed _
  have hag : ∀ a ∈ P.agents, Term.agent a ∈ subtermClosureL (seeds P) := by
    intro a ha
    exact mem_subtermClosureL (mem_seeds_agent ha)
  have hks : ∀ k ∈ domainKeys P.agents, Term.key k ∈ subtermClosureL (seeds P) := by
    intro k hk
    refine mem_subtermClosureL ?_
    show Term.key k ∈ seeds P
    simp only [seeds, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩)))
  have hI := hbase.iterate hag hks
  have huniv : univ P B =
      ((fun W => closeOne P.agents (domainKeys P.agents) W)^[B.rounds]
        (subtermClosureL (seeds P))).eraseDups := rfl
  rw [huniv]
  exact (hI B.rounds).eraseDups

/-- **`univSub` is a theorem of the construction, not a hypothesis about the query.** Every subterm
of every universe message is itself a universe message, for every protocol and every bounds. -/
theorem univSub_shapeOf (P : Protocol) (B : Bounds) : univSub (shapeOf P B) := by
  intro t ht u hu
  exact univ_SubtermClosed P B t ht u hu

/-! ### Instances: the generic theorem, applied -/

/-- The guarded-style protocol of `Represent`: the generic theorem discharges what an instance
proof would otherwise reach by `decide`. -/
example : univSub (shapeOf Represent.plainP { steps := 2, rounds := 1 }) :=
  univSub_shapeOf _ _

/-- And on a protocol with a nonce domain and a pairing expression, so the universe is not just a
handful of atoms: the condition is doing work here, and the theorem still discharges it. -/
example : univSub (shapeOf ExprDomain.boundsP ExprDomain.boundsB) := univSub_shapeOf _ _

end ProtSat.Closure
