/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import ProtSat.BoundedExec
import ProtSat.Query
import ProtSat.Differential

/-!
# ProtSat: the soundness direction, completed

## Why this module exists

`Encoding.encoding_sound` proves that a satisfying assignment of the generated CNF decodes to an
attack: a real run of `ProtSat.Rel` from `initCfg P` in which a declared secret reaches the
attacker. The public predicate the correspondence is measured against asks for one thing more, and
the whole "the verdict means what it says" story turns on it. `Bounded.BoundedAttack` is a
*bounded* attack: `BoundedTrace P B tr Cs` conjoins three facts, and the third of them -
`Bounded.runsInUniverse Cs (univ P B)`, every configuration the run visits uses only messages of
the universe - is the one `encoding_sound` never claimed. `Correspondence.lean` closes by naming
exactly this hole:

> the direction `Satisfiable (encode P B) -> boundedAttackGoals q` needs `encoding_sound` to
> return the complete bounded predicate, i.e. that the *decoded* run stays inside the universe.
> The leak half of its conclusion is proved; the `runsInUniverse` half is not.

This module proves the missing half, and then the two directions meet: `encoding_correct` is the
full equivalence between satisfiability of the generated formula and the public bounded attack
predicate, for the goal the encoding can express. `Differential.leak_sat` exhibits a satisfying
assignment of a real generated CNF, so the equivalence is instantiated with no hypotheses at all
(`leaky_query_boundedAttack`) - and, unlike the instance proof that was there before, the witness
is the run *decoded from the assignment*, not a hand-built one.

## How the proof goes

The decoded configuration at step `i` is `decRun P B a i`, and `Encoding.agrees_decRun` says it
agrees with the assignment: its knowledge list *is* `decKnSeq`, and every store slot that reads
back *is* `decSt`. So it is enough to show that the two decoders have the universe as their range:

* `decVal sh o a` is `valAt sh u` for the index the one-hot group selects, and `valAt sh u` is
  `rget sh.U u` - a read of the universe list, so whatever it returns is a universe message
  (`decVal_range`). No hypothesis at all: this is a property of the decoders, not of the run.
* `decLearn` returns either such a `decVal` (a session's send value, read off the Tseitin group)
  or `valAt sh inst.concl` (the conclusion of a deduction instance, an index into the universe),
  so it too is universe-valued (`decLearn_range`), and by induction so is every `decKnSeq` once
  the initial knowledge is (`decKnSeq_range`; `Bounded.initKn_subset_univ` supplies that).
* A store is well formed - `StoreWF`, a field of `Agrees` - so each of its variables is one of the
  slots the store clauses pin, and each pinned slot is a `decSt`, hence a `decVal`, hence a
  universe message (`decRun_storeU`).

The one hypothesis the argument genuinely uses is `univClosed (shapeOf P B) P`, and it is used only
to obtain `Agrees` at all: `Encoding.rel_agrees` needs it, so `agrees_decRun` needs it. It is the
same hypothesis `encoding_sound` already assumes, so nothing is added to the soundness theorem.

## What this does not do

* It does **not** need `Represent.domainGap P B = false`, and it is worth saying why, because the
  completeness side does. `domainGap` is a statement about *forward* closure: that evaluating a
  protocol expression in a universe-valued store cannot produce a message the value domain does
  not name (`RunOK.exprB`). Soundness reads the other way: the decoded values are obtained by
  *indexing into* the universe list, so they are universe messages by construction, whatever the
  protocol's expressions do. The under-approximation lives in the completeness direction; the
  soundness direction is unconditional in this respect. `domainGap` appears in this module only in
  the capstone equivalence, on the half that came from `Complete.lean`.
* It does not say the decoded run is the *only* run the assignment describes, nor that the decoded
  knowledge is minimal: `decKnSeq` lists what the clauses justify, and `Rel`'s deduction steps
  accept exactly that.
* It does not extend the violation clause. `Encode.violationLits` names leaks only, so the goal
  obtained is `Goal.secrecy`; an `AuthBreak` conclusion does not follow from a satisfying
  assignment and is not claimed here.
* It does not discharge `univClosed`, `univSub` or `SecretsOK`; they remain hypotheses (decidable
  ones, which the analyser computes - see `ProtSat.Analyzer`).
-/

namespace ProtSat.Sound

open ProtSat Term Protocol Bounded Encode Encoding OneHot Query Complete BoundedExec
  Represent

/-! ### Reading a list at an index -/

/-- Reading a list at an index returns an element of the list. -/
theorem rget_some_mem {alpha : Type} {l : List alpha} {i : Nat} {a : alpha}
    (h : rget l i = some a) : a ∈ l := by
  induction l generalizing i with
  | nil => exact absurd h (by simp [rget])
  | cons x xs ih =>
      cases i with
      | zero =>
          rw [rget] at h
          cases h
          exact List.Mem.head _
      | succ i =>
          rw [rget] at h
          exact List.Mem.tail _ (ih h)

/-- An index at which a list has a value is inside the list. -/
theorem lt_length_of_rget_some {alpha : Type} {l : List alpha} {i : Nat} {a : alpha}
    (h : rget l i = some a) : i < l.length := by
  induction l generalizing i with
  | nil => exact absurd h (by simp [rget])
  | cons x xs ih =>
      cases i with
      | zero => exact Nat.succ_pos _
      | succ i =>
          rw [show rget (x :: xs) (i + 1) = rget xs i from rfl] at h
          exact Nat.succ_lt_succ (ih h)

/-- Every member of a list sits at some index. -/
theorem exists_rget_of_mem {alpha : Type} {l : List alpha} {a : alpha} (h : a ∈ l) :
    ∃ i, rget l i = some a := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      cases h with
      | head _ => exact ⟨0, rfl⟩
      | tail _ h =>
          obtain ⟨i, hi⟩ := ih h
          exact ⟨i + 1, by rw [show rget (x :: xs) (i + 1) = rget xs i from rfl]; exact hi⟩

/-- Membership in a list makes `contains` decide it. -/
theorem mem_contains {U : List Term} {t : Term} (h : t ∈ U) : U.contains t = true := by
  simpa

/-! ### The range of the value decoders -/

/-- **The range of the value decoder.** Whatever a one-hot group over the value indices decodes
to, that value is a message of the shape's universe. `decVal` reads the selected index through
`valAt`, and `valAt` is a read of the universe list, so this needs no hypothesis about the
assignment, the protocol or the bounds: it is a property of the decoder. -/
theorem decVal_range {sh : Shape} {o : Oh Nat} {a : Assignment} {t : Term}
    (h : decVal sh o a = some t) : t ∈ sh.U := by
  cases h1 : o.decode a with
  | none => rw [decVal, h1] at h; exact absurd h (by simp)
  | some u =>
      rw [decVal, h1] at h
      exact rget_some_mem h

/-- The value a store slot is pinned to is a universe message. -/
theorem decSt_range {sh : Shape} {a : Assignment} {i q x : Nat} {t : Term}
    (h : decSt sh a i q x = some t) : t ∈ sh.U := decVal_range h

/-- The value a Tseitin expression group is pinned to is a universe message. -/
theorem decXe_range {sh : Shape} {P : Protocol} {a : Assignment} {i q : Nat} {e : Expr}
    {t : Term} (h : decXe sh P a i q e = some t) : t ∈ sh.U := decVal_range h

/-- **The range of the learn decoder.** The message step `i` teaches the attacker - the value a
session sent, or the conclusion of the deduction instance that fired - is a universe message.
Both alternatives are reads of the universe list: `decXe` through a Tseitin group, the instance
conclusion through `valAt sh inst.concl`, whose index is a position in `sh.U`. -/
theorem decLearn_range {sh : Shape} {P : Protocol} {a : Assignment} {i : Nat} {t : Term}
    (h : decLearn sh P a i = some t) : t ∈ sh.U := by
  cases h1 : (evOh sh i).decode a with
  | none => exact absurd h (by simp [decLearn, h1])
  | some k =>
      by_cases hk : k = 0
      · exact absurd h (by simp [decLearn, h1, hk])
      · by_cases hk' : k < 1 + shS sh
        · -- the step is an action: only a send teaches the attacker anything
          cases h2 : P.actionAt (k - 1) (decodePc sh a i (k - 1)) with
          | none => exact absurd h (by simp [decLearn, h1, hk, hk', h2])
          | some act =>
              cases act with
              | send _ e =>
                  have h3 : decLearn sh P a i = decXe sh P a i (k - 1) e := by
                    simp [decLearn, h1, hk, hk', h2]
                  rw [h3] at h
                  exact decXe_range h
              | _ => exact absurd h (by simp [decLearn, h1, hk, hk', h2])
        · -- the step is a deduction event: its conclusion is a universe position
          cases h2 : instAt sh (k - 1 - shS sh) with
          | none => exact absurd h (by simp [decLearn, h1, hk, hk', h2])
          | some inst =>
              have h3 : decLearn sh P a i = valAt sh inst.concl := by
                simp [decLearn, h1, hk, hk', h2]
              rw [h3] at h
              exact rget_some_mem h

/-- **The decoded knowledge is universe-valued.** Every message the attacker is recorded as
knowing after `i` steps is a universe message, provided the initial knowledge is. The list is the
initial knowledge extended by the `decLearn` of each earlier step, and both are universe-valued. -/
theorem decKnSeq_range {sh : Shape} {P : Protocol} {a : Assignment}
    (hinit : ∀ t ∈ P.initKn, t ∈ sh.U) :
    ∀ (i : Nat) {t : Term}, t ∈ decKnSeq sh P a i → t ∈ sh.U := by
  intro i
  induction i with
  | zero => intro t ht; exact hinit t ht
  | succ j ih =>
      intro t ht
      rw [decKnSeq] at ht
      rw [List.mem_append] at ht
      rcases ht with ht | ht
      · exact ih ht
      · cases hL : decLearn sh P a j with
        | none => rw [hL] at ht; exact absurd ht (by simp)
        | some u =>
            rw [hL] at ht
            obtain rfl := List.mem_singleton.mp ht
            exact decLearn_range hL

/-- The initial knowledge is inside the universe of the shape: `shapeOf` puts `Bounded.univ P B`
in the universe field, and the universe contains the initial knowledge by construction. -/
theorem initKn_U (P : Protocol) (B : Bounds) : ∀ t ∈ P.initKn, t ∈ (shapeOf P B).U :=
  initKn_subset_univ P B

/-! ### The decoded configuration is inside the universe -/

/-- **The decoded stores are universe-valued.** Every message held by the store of an instantiated
session of a decoded configuration is a universe message. The store is well formed, so each of its
variables is one of the slots the store clauses pin, and each pinned slot reads back through
`decSt`, hence through `valAt`. -/
theorem decRun_storeU (hag : Agrees P B a (decRun P B a i) i) {q : Nat}
    (hq : q < (shapeOf P B).nS1) {p : Var × Term}
    (hp : p ∈ storeOf (decRun P B a i) q) : p.2 ∈ (shapeOf P B).U := by
  have hwf := hag.2.2.2.1 q hq
  have hx : p.1 < (shapeOf P B).nV1 + 1 := hwf.2 p hp
  have hr : readVar p.1 (storeOf (decRun P B a i) q) = some p.2 := readVar_of_mem hp hwf.1
  have h1 : readVar p.1 (storeOf (decRun P B a i) q) = decSt (shapeOf P B) a i q p.1 :=
    hag.2.1 q p.1 hq hx
  rw [h1] at hr
  exact decSt_range hr

/-- **The decoded knowledge is universe-valued.** -/
theorem decRun_knU (hag : Agrees P B a (decRun P B a i) i) :
    ∀ t ∈ (decRun P B a i).kn, t ∈ (shapeOf P B).U := by
  intro t ht
  rw [hag.2.2.1] at ht
  exact decKnSeq_range (initKn_U P B) _ ht

/-- If every store of every session of `C` is universe-valued, the store half of
`cfgInUniverse` holds. -/
theorem cfgInUniverse_store_of {C : Cfg} {sh : Shape}
    (h : ∀ q, q < C.sess.length → ∀ p ∈ storeOf C q, p.2 ∈ sh.U) :
    C.sess.all (fun s => s.store.all (fun p => sh.U.contains p.2)) = true := by
  rw [List.all_eq_true]
  intro s hs
  obtain ⟨q, hq⟩ := exists_rget_of_mem hs
  have hlen : q < C.sess.length := lt_length_of_rget_some hq
  have hst : storeOf C q = s.store := by
    unfold storeOf sessAt
    rw [hq]
    simp
  rw [← hst, List.all_eq_true]
  intro p hp
  exact mem_contains (h q hlen p hp)

/-- **A decoded configuration is inside the universe.** Both halves of `cfgInUniverse` hold for
`decRun P B a i`: the knowledge list is `decKnSeq`, which is universe-valued, and the stores read
back through the pinned slots, which are universe-valued. -/
theorem decRun_cfgInUniverse (hag : Agrees P B a (decRun P B a i) i) :
    cfgInUniverse (decRun P B a i) (shapeOf P B).U = true := by
  unfold cfgInUniverse
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro t ht
    exact mem_contains (decRun_knU hag t ht)
  · refine cfgInUniverse_store_of (C := decRun P B a i) ?_
    intro q hq
    have hq' : q < (shapeOf P B).nS1 := by rw [← hag.2.2.2.2]; exact hq
    exact fun p hp => decRun_storeU hag hq' hp

/-! ### The main result: the decoded run stays inside the universe -/

/-- **The decoded run stays inside the universe**, up to any step count. Every configuration
`decCfgsFrom P B a n` visits is `decRun P B a i` for some `i ≤ B.steps`, and each of those is
inside `univ P B` by `decRun_cfgInUniverse`. This is the `runsInUniverse` half of
`BoundedTrace`, the half `encoding_sound` did not claim. -/
theorem runsInUniverse_decCfgsFrom (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    ∀ (n : Nat), n ≤ B.steps → runsInUniverse (decCfgsFrom P B a n) (univ P B) := by
  intro n
  induction n with
  | zero =>
      intro _
      unfold runsInUniverse
      intro C hC
      rw [decCfgsFrom, List.mem_singleton] at hC
      subst hC
      exact decRun_cfgInUniverse (agrees_decRun h hU B.steps (Nat.le_refl _))
  | succ n ih =>
      intro hn
      unfold runsInUniverse
      intro C hC
      rw [decCfgsFrom, List.mem_cons] at hC
      rcases hC with rfl | hC
      · exact decRun_cfgInUniverse
          (agrees_decRun h hU (B.steps - (n + 1)) (by omega : B.steps - (n + 1) ≤ B.steps))
      · exact ih (by omega) C hC

/-- **The missing half.** A satisfying assignment of the generated CNF decodes to a run that
stays inside the universe: every configuration it visits uses only messages of `univ P B`. The
hypotheses are exactly the ones `encoding_sound` already takes - the universe hypothesis and
satisfiability - so no new assumption is introduced. -/
theorem decoding_runsInUniverse (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    runsInUniverse (decCfgsFrom P B a B.steps) (univ P B) :=
  runsInUniverse_decCfgsFrom hU h B.steps (Nat.le_refl _)

/-- The decoded trace has at most the step bound of events. -/
theorem decEvsFrom_length_le (P : Protocol) (B : Bounds) (a : Assignment) :
    (decEvsFrom P B a B.steps).length ≤ B.steps := by
  rw [decEvsFrom_length]

/-- **The decoded run is a bounded trace** in the public sense: a run of `Rel` from the initial
configuration, at most `B.steps` events, and every visited configuration inside `univ P B`. -/
theorem boundedTrace_decRun (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    BoundedTrace P B (decEvsFrom P B a B.steps) (decCfgsFrom P B a B.steps) :=
  ⟨decRun_trace h hU, decEvsFrom_length_le P B a, decoding_runsInUniverse hU h⟩

/-- The decoded run leaks a declared secret: the violation clause names a configuration of it. -/
theorem decCfgsFrom_runsLeaks (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    runsLeaks P (decCfgsFrom P B a B.steps) := by
  obtain ⟨i, hi, hleak⟩ := violation_leak hU h
  refine ⟨decRun P B a i, ?_, hleak⟩
  have hmem : decRun P B a (B.steps - (B.steps - i)) ∈ decCfgsFrom P B a B.steps :=
    decCfgsFrom_mem P B a B.steps (B.steps - i) (by omega)
  rwa [Nat.sub_sub_self hi] at hmem

/-! ### The public bounded attack -/

/-- **Soundness, in the public bounded sense** (specification 8A, complete). A satisfying
assignment of the generated CNF yields a `BoundedAttack`: not merely an attack whose trace happens
to have the right length, but a trace all of whose configurations lie inside the universe the
bounds define. This is `encoding_sound` with the conjunct `Correspondence.lean` recorded as
missing. -/
theorem encoding_sound_bounded' (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    BoundedAttack P B :=
  ⟨decEvsFrom P B a B.steps, decCfgsFrom P B a B.steps, boundedTrace_decRun hU h,
    Or.inl (decCfgsFrom_runsLeaks hU h)⟩

/-- The same conclusion in the goal-indexed form of the verification contract: a satisfying
assignment is an attack on the secrecy goal of the query. -/
theorem boundedAttackGoals_of_sat (hU : univClosed (shapeOf P B) P) (h : Sat a (encode P B)) :
    boundedAttackGoals (Query.mk P B [Goal.secrecy]) :=
  ⟨Goal.secrecy, List.Mem.head _, decEvsFrom P B a B.steps, decCfgsFrom P B a B.steps,
    boundedTrace_decRun hU h, (violation_secrecy P _ _).mpr (decCfgsFrom_runsLeaks hU h)⟩

/-- **Soundness for the existential.** If the generated formula is satisfiable at all, the query
has a bounded attack on its secrecy goal. This is the direction the correspondence was missing. -/
theorem encoding_correct_sound (hU : univClosed (shapeOf P B) P) :
    Satisfiable (encode P B) → boundedAttackGoals (Query.mk P B [Goal.secrecy]) := by
  rintro ⟨a, ha⟩
  exact boundedAttackGoals_of_sat hU ha

/-- And the same for the older public predicate. -/
theorem boundedAttack_of_satisfiable (hU : univClosed (shapeOf P B) P) :
    Satisfiable (encode P B) → BoundedAttack P B := by
  rintro ⟨a, ha⟩
  exact encoding_sound_bounded' hU ha

/-- **The correspondence, both ways.** For a gap-free query, the generated CNF is satisfiable
exactly when the query has a bounded attack on its secrecy goal. The forward direction is this
module's `encoding_correct_sound`; the backward direction is `Complete.encoding_complete`, with
`WithinBounds` derived from the public bound and the query's gap check. -/
theorem encoding_correct {P : Protocol} {B : Bounds}
    (hgap : domainGap P B = false) (hU : univClosed (shapeOf P B) P)
    (hsub : univSub (shapeOf P B)) (hsec : SecretsOK (shapeOf P B) P) :
    Satisfiable (encode P B) ↔ boundedAttackGoals (Query.mk P B [Goal.secrecy]) :=
  ⟨fun hs => encoding_correct_sound hU hs, fun ⟨g, hg, tr, Cs, hbt, hv⟩ => by
      have hgeq : g = Goal.secrecy := by simpa using hg
      subst hgeq
      rw [violation_secrecy] at hv
      exact encoding_complete (P := P) (B := B) (tr := tr) (Cs := Cs) hU hsub hsec
        hbt.1 hbt.2.1 hv (withinBounds_of_bounded hbt hgap)⟩

/-! ### The general theorem, instantiated -/

/-- **No hypotheses left.** The leaky protocol of `EndToEnd` has a satisfiable generated CNF
(`Differential.leak_sat`) and a universe the protocol's expressions stay inside
(`Differential.leak_hU`), so the soundness direction applies with nothing further to discharge:
the query has a bounded attack, witnessed by the run decoded from the assignment. -/
theorem leaky_query_boundedAttack : boundedAttackGoals EndToEnd.ql :=
  encoding_correct_sound Differential.leak_hU Differential.leak_sat

/-- The same instance in the older vocabulary: a genuine `BoundedAttack`, every configuration of
which lies in `univ EndToEnd.Leak EndToEnd.GB`. -/
theorem leaky_BoundedAttack : BoundedAttack EndToEnd.Leak EndToEnd.GB :=
  boundedAttack_of_satisfiable Differential.leak_hU Differential.leak_sat

end ProtSat.Sound