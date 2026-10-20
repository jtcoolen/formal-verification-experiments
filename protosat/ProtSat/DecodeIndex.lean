/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encoding
import ProtSat.Complete

/-!
# ProtSat/DecodeIndex.lean - the decoded trace read by position

## What this file is, in plain English

`ProtSat/AuthClauses.lean` explains in its module header ("What is NOT proved") why
agreement cannot yet be proved SOUND through the CNF route: every decoding lemma of
`ProtSat.Encoding` takes its hypothesis as `Sat a (encode P B)` - the whole formula, secrecy
violation clause included - so a model of an *agreement-only* formula cannot feed them.  It
lists the missing pieces that are "not deep", and this file supplies them:

* the two trace-index lemmas, `decEvsFrom_rget` and `decCfgsFrom_rget`;
* the same two facts in the vocabulary the downstream proofs consume, `evAt_decEvsFrom` and
  `cfgAt_decCfgsFrom` (that is `ProtSat.Complete.evAt` / `ProtSat.Complete.cfgAt`);
* the lemma recovering `decCode P B a i = 1 + q` from the decoded event being `Ev.act q m d`,
  here `decCode_of_decEv_act`.

**The point of the file is that none of those needs `Sat`.**  They are statements about the
shape of the decoding functions, and they hold for *every* assignment, satisfying or not.
That is what makes them the first domino: when the secrecy violation clause is replaced by
the agreement one, the lemmas above survive untouched.

So whoever proves SOUND for the agreement encoding can now say, for a model `a` of an
agreement-only formula, that the decoded trace `tr := decEvsFrom P B a B.steps` and the
visit list `Cs := decCfgsFrom P B a B.steps` satisfy, pointwise,

    evAt tr i  = decEv (shapeOf P B) P a i   (evAt_decEvsFrom_steps,      i < B.steps)
    cfgAt Cs i = decRun P B a i              (cfgAt_decCfgsFrom_steps,    i <= B.steps)

and that a claim or commit the decoded run makes at step i forces
`decCode P B a i = 1 + q` (`decCode_of_decEv_act`), which is the event literal the
agreement clauses talk about.  The converse also holds without `Sat`:
`decEv_act_of_decCode` is the twin of `ProtSat.Encoding.decEv_act_of_code` with the
`Sat a (encode P B)` hypothesis dropped, and `decode_some_of_decEv_ded` does the same job
for a deduction step.

## What is still missing for SOUND

1. The `Encoding` decoding lemmas that genuinely read the clauses.  `agrees_decRun`,
   `rel_agrees`, `decodePc_of_true`, `kn_sound` and friends need `Sat a (encode P B)`
   because they use the one-hot clauses (`sat_evOh` and friends), and `encode P B` is where
   those clauses live.  Re-stating them over `Sat a (baseEncode P B)` plus the goal clauses
   actually used - or group by group - is the remaining work.  Nothing here does that:
   `relAt_decSegment` and `decSegment_rel` are the *only* lemmas in this file that consume
   `Sat a (encode P B)`, and they are `decRunFrom_runs` (already in the repository) read
   pointwise through `runs_rel` and re-indexed with the lemmas above.
2. The `authNameable` step: turning "the decoded run has a claim of triple t" into "all four
   literals of that claim occurrence are true".
3. The reference-semantics bridge (item 3 of the AuthClauses integration list).
4. One honest gap found while writing this file.  The natural companion of
   `decCode_of_decEv_act`, namely "the decoded event is idle only if the selected code is 0",
   does *not* follow from the definitions alone: `decEv` also returns `Ev.idle` from the
   deduction branch when `instAt` names no instance or `valAt` names no value.  Both are
   impossible for a real `shapeOf P B` - every deduction instance conclusion is a universe
   message, and `decode` only ever returns an index below `shEv` - but proving that needs
   the invariant of `ProtSat.Encode.dedInstsOf`, which is outside this file.  What is proved
   instead is `decEv_idle_cases`: an idle decoded event either has code 0 or has the code of a
   deduction instance, which is as far as the definition of `decEv` alone allows one to go.

## Conventions used here

* The lemmas live in the `ProtSat.Encoding` namespace, so a file that already does
  `open ProtSat.Encoding` picks them up without qualification.  Nothing outside this file
  changed.
* `ProtSat.Encoding.decEvsFrom_length` already exists (ProtSat/Encoding.lean:3606) and is
  used rather than reproved; the missing twin is `decCfgsFrom_length`.
* `B.steps - n` is truncated subtraction, so the re-indexing statements need
  `n <= B.steps`; without it `B.steps - n + i` and `B.steps - (n - i)` disagree.  Where a
  fact holds without that hypothesis it is stated without it: `decCfgsFrom_rget_last` needs
  no bound at all, because the segment always ends with `decRun B.steps`.
* `evAt` is `drop`/`headD`-based and `cfgAt` is `cfgGo`-based, not `rget`-based, so the
  index lemmas are transported by the two bridges `evAt_eq_rget_getD` and `cfgAt_of_rget`,
  not by definition.
* The one place where the arithmetic of the encoding is delicate is noted at
  `decEv_act_of_decCode`: the code must be written `q + 1`, not `1 + q`, for the "is the code
  zero" test in `decEv` to reduce, because `Nat.add` recurses on its second argument.
-/

namespace ProtSat.Encoding

open ProtSat Term OneHot Bounded Attacker Encode
open Protocol

variable {P : Protocol} {B : Bounds} {a : Assignment}

/-! ### Reading a list by position: rget, the standard index, evAt, cfgAt -/

/-- The repository's total index rget and the standard library's total index are the same
function: both are none past the end and both walk the list one constructor at a time. -/
theorem rget_eq_get? : ∀ {α : Type} (l : List α) (i : Nat), rget l i = l[i]? := by
  intro α l
  induction l with
  | nil => intro i; rfl
  | cons x xs ih => intro i; cases i <;> simp [rget, ih]

/-- ProtSat.Complete.evAt is rget with Ev.idle as the out-of-range default: inside the
trace the two agree, and past the end evAt idles exactly where rget says none. -/
theorem evAt_eq_rget_getD (tr : List Ev) (i : Nat) :
    Complete.evAt tr i = (rget tr i).getD Ev.idle := by
  induction tr generalizing i with
  | nil => simp [Complete.evAt, rget, List.headD]
  | cons e rest ih =>
      cases i with
      | zero => simp [Complete.evAt, rget, List.headD]
      | succ j => show Complete.evAt rest j = (rget rest j).getD Ev.idle; exact ih j

/-- Where rget finds a configuration, ProtSat.Complete.cfgAt finds the same one: the
"repeat the last configuration past the end" behaviour of cfgAt only matters out of range. -/
theorem cfgAt_of_rget {Cs : List Cfg} {i : Nat} {D : Cfg}
    (h : rget Cs i = some D) : Complete.cfgAt Cs i = D := by
  induction Cs generalizing i with
  | nil => exact absurd h (by simp [rget])
  | cons C rest ih =>
      cases i with
      | zero =>
          have hCD : C = D := by simpa [rget] using h
          subst hCD
          exact Complete.cfgAt_head
      | succ j =>
          have h2 : rget rest j = some D := h
          cases rest with
          | nil => exact absurd h2 (by simp [rget])
          | cons y ys => exact ih h2

/-! ### Lengths -/

/-- The list of configurations visited over the last n steps has n + 1 elements: one per
step, plus the one the segment starts in. -/
theorem decCfgsFrom_length (P : Protocol) (B : Bounds) (a : Assignment) :
    ∀ (n : Nat), (decCfgsFrom P B a n).length = n + 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [decCfgsFrom, ih]

/-- The event segment is nonempty as soon as it has a step. -/
theorem decEvsFrom_ne {n : Nat} (hn : 0 < n) : decEvsFrom P B a n ≠ [] := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n => simp [decEvsFrom]

/-- The configuration segment is never empty: it always contains at least the final
configuration. -/
theorem decCfgsFrom_ne (n : Nat) : decCfgsFrom P B a n ≠ [] := by
  cases n with
  | zero => simp [decCfgsFrom]
  | succ n => simp [decCfgsFrom]

/-! ### The index equations -/

/-- Trace-index lemma for events. Inside the last n steps, position i of the decoded event
segment is the event the assignment selects at step B.steps - n + i: the segment starts n
steps before the end and runs forward, so position i is step steps - n + i. -/
theorem decEvsFrom_rget : ∀ (n : Nat), n ≤ B.steps →
    ∀ (i : Nat), i < n ->
      rget (decEvsFrom P B a n) i =
        some (decEv (shapeOf P B) P a (B.steps - n + i)) := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (by omega)
  | succ n ih =>
      intro hn i hi
      cases i with
      | zero =>
          rw [show B.steps - (n + 1) + 0 = B.steps - (n + 1) by omega]
          rfl
      | succ j =>
          have hj : j < n := by omega
          have h1 : rget (decEvsFrom P B a (n + 1)) (j + 1) = rget (decEvsFrom P B a n) j := rfl
          rw [h1, ih (by omega) j hj]
          rw [show B.steps - (n + 1) + (j + 1) = B.steps - n + j by omega]

/-- Trace-index lemma for configurations. Position i of the decoded configuration segment is
the configuration the decoded run visits at step B.steps - n + i; the segment has n + 1
elements, so i runs up to n. -/
theorem decCfgsFrom_rget : ∀ (n : Nat), n ≤ B.steps →
    ∀ (i : Nat), i ≤ n ->
      rget (decCfgsFrom P B a n) i =
        some (decRun P B a (B.steps - n + i)) := by
  intro n
  induction n with
  | zero =>
      intro _ i hi
      rw [show i = 0 by omega, show B.steps - 0 + 0 = B.steps by omega]
      rfl
  | succ n ih =>
      intro hn i hi
      cases i with
      | zero =>
          rw [show B.steps - (n + 1) + 0 = B.steps - (n + 1) by omega]
          rfl
      | succ j =>
          have h1 : rget (decCfgsFrom P B a (n + 1)) (j + 1) = rget (decCfgsFrom P B a n) j := rfl
          rw [h1, ih (by omega) j (by omega)]
          rw [show B.steps - (n + 1) + (j + 1) = B.steps - n + j by omega]

/-- The last element of the configuration segment is the final configuration of the run,
whatever the bounds: no hypothesis on n is needed because the segment is built by consing at
the front and always ends with decRun B.steps. -/
theorem decCfgsFrom_rget_last (n : Nat) :
    rget (decCfgsFrom P B a n) n = some (decRun P B a B.steps) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show rget (decCfgsFrom P B a (n + 1)) (n + 1) = _
      rw [show rget (decCfgsFrom P B a (n + 1)) (n + 1) = rget (decCfgsFrom P B a n) n from rfl]
      exact ih

/-- Out of range the event segment reads none: position i >= n is past the end of a list of
n events. -/
theorem decEvsFrom_rget_oob {n i : Nat} (hi : n ≤ i) : rget (decEvsFrom P B a n) i = none :=
  rget_oob_ge (decEvsFrom P B a n) i (by rw [decEvsFrom_length P B a n]; exact hi)

/-- Out of range the configuration segment reads none: position i > n is past the end of a
list of n + 1 configurations. -/
theorem decCfgsFrom_rget_oob {n i : Nat} (hi : n + 1 ≤ i) :
    rget (decCfgsFrom P B a n) i = none :=
  rget_oob_ge (decCfgsFrom P B a n) i (by rw [decCfgsFrom_length P B a n]; exact hi)

/-- The event segment read with the standard library's total index. -/
theorem decEvsFrom_get? {n i : Nat} (h : n ≤ B.steps) (hi : i < n) :
    (decEvsFrom P B a n)[i]? = some (decEv (shapeOf P B) P a (B.steps - n + i)) := by
  rw [← rget_eq_get?, decEvsFrom_rget n h i hi]

/-- The configuration segment read with the standard library's total index. -/
theorem decCfgsFrom_get? {n i : Nat} (h : n ≤ B.steps) (hi : i ≤ n) :
    (decCfgsFrom P B a n)[i]? = some (decRun P B a (B.steps - n + i)) := by
  rw [← rget_eq_get?, decCfgsFrom_rget n h i hi]

/-- The last event of the segment is the event of the last step: position n - 1 of the last
n steps is step B.steps - 1. -/
theorem decEvsFrom_get?_last {n : Nat} (hn : 0 < n) (h : n ≤ B.steps) :
    (decEvsFrom P B a n)[n - 1]? =
      some (decEv (shapeOf P B) P a (B.steps - 1)) := by
  rw [decEvsFrom_get? h (by omega)]
  rw [show B.steps - n + (n - 1) = B.steps - 1 by omega]

/-- The last configuration of the segment is the configuration the run ends in. -/
theorem decCfgsFrom_get?_last (n : Nat) :
    (decCfgsFrom P B a n)[n]? = some (decRun P B a B.steps) := by
  rw [← rget_eq_get?, decCfgsFrom_rget_last]

/-! ### The same facts in the vocabulary downstream consumes -/

/-- evAt on the decoded event segment. The downstream proofs state a run as Runs P C0 tr Cs
and read it with ProtSat.Complete.evAt; this is the instance of the trace index lemma in that
vocabulary: the event at position i of the segment is the event the assignment selects at step
B.steps - n + i. evAt is drop/headD-based rather than rget-based, so the bridge is
evAt_eq_rget_getD. -/
theorem evAt_decEvsFrom {n i : Nat} (h : n ≤ B.steps) (hi : i < n) :
    Complete.evAt (decEvsFrom P B a n) i =
      decEv (shapeOf P B) P a (B.steps - n + i) := by
  rw [evAt_eq_rget_getD, decEvsFrom_rget n h i hi]
  rfl

/-- cfgAt on the decoded configuration segment. The configuration at position i of the
segment is the configuration the decoded run visits at step B.steps - n + i. cfgAt walks the
list with cfgGo, so the bridge is cfgAt_of_rget. -/
theorem cfgAt_decCfgsFrom {n i : Nat} (h : n ≤ B.steps) (hi : i ≤ n) :
    Complete.cfgAt (decCfgsFrom P B a n) i = decRun P B a (B.steps - n + i) :=
  cfgAt_of_rget (decCfgsFrom_rget n h i hi)

/-- The segment starts at the configuration the run visits at step B.steps - n. -/
theorem cfgAt_decCfgsFrom_zero {n : Nat} (h : n ≤ B.steps) :
    Complete.cfgAt (decCfgsFrom P B a n) 0 = decRun P B a (B.steps - n) :=
  cfgAt_decCfgsFrom h (by omega)

/-- The segment ends at the configuration the run visits at step B.steps. -/
theorem cfgAt_decCfgsFrom_last {n : Nat} (h : n ≤ B.steps) :
    Complete.cfgAt (decCfgsFrom P B a n) n = decRun P B a B.steps := by
  have h1 : Complete.cfgAt (decCfgsFrom P B a n) n = decRun P B a (B.steps - n + n) :=
    cfgAt_decCfgsFrom h (Nat.le_refl _)
  rw [show B.steps - n + n = B.steps by omega] at h1
  exact h1

/-- Past the end of the event segment evAt idles, which is what the encoding's idle steps
expect of a finished run. -/
theorem evAt_decEvsFrom_past {n i : Nat} (hi : n ≤ i) :
    Complete.evAt (decEvsFrom P B a n) i = Ev.idle := by
  rw [evAt_eq_rget_getD, decEvsFrom_rget_oob hi]
  rfl

/-! ### Recovering the event code from the decoded event -/

/-- The event group selected code 1 + q when the decoded event is the action of session q.
This is the raw form of the bridge, before decCode folds the none case to 0. -/
theorem decode_some_of_decEv_act {q : Nat} {m : Term} {d : NonceName}
    (h : decEv (shapeOf P B) P a i = Ev.act q m d) :
    (evOh (shapeOf P B) i).decode a = some (1 + q) ∧ q < shS (shapeOf P B) := by
  unfold decEv at h
  cases hd : (evOh (shapeOf P B) i).decode a with
  | none =>
      rw [hd] at h
      have h2 : Ev.idle = Ev.act q m d := h
      exact absurd h2 (by simp)
  | some k =>
      rw [hd] at h
      have hred : (if k = 0 then Ev.idle else
            if h : k < 1 + shS (shapeOf P B) then
              Ev.act (k - 1) (decDeliver (shapeOf P B) a i (k - 1)) (decNonce (shapeOf P B) a i (k - 1))
            else
              match instAt (shapeOf P B) (k - 1 - shS (shapeOf P B)) with
              | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
              | none => Ev.idle) = Ev.act q m d := h
      cases k with
      | zero =>
          have h2 : Ev.idle = Ev.act q m d := hred
          exact absurd h2 (by simp)
      | succ k' =>
          have h3 : (if h : k'.succ < 1 + shS (shapeOf P B) then
              Ev.act k' (decDeliver (shapeOf P B) a i k') (decNonce (shapeOf P B) a i k')
            else
              match instAt (shapeOf P B) (k' - shS (shapeOf P B)) with
              | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
              | none => Ev.idle) = Ev.act q m d := hred
          by_cases hlt : k'.succ < 1 + shS (shapeOf P B)
          · rw [dite_eq_left hlt] at h3
            obtain ⟨h1, _, _⟩ := Ev.act.inj h3
            have h5 : k'.succ = 1 + q := by omega
            exact ⟨congrArg some h5, by omega⟩
          · rw [dite_eq_right hlt] at h3
            cases hins : instAt (shapeOf P B) (k' - shS (shapeOf P B)) with
            | none =>
                rw [hins] at h3
                have h4 : Ev.idle = Ev.act q m d := h3
                exact absurd h4 (by simp)
            | some ins =>
                rw [hins] at h3
                have h4 : (match valAt (shapeOf P B) ins.concl with
                    | some t => Ev.ded t
                    | none => Ev.idle) = Ev.act q m d := h3
                cases hv : valAt (shapeOf P B) ins.concl with
                | none =>
                    rw [hv] at h4
                    have h5 : Ev.idle = Ev.act q m d := h4
                    exact absurd h5 (by simp)
                | some t' =>
                    rw [hv] at h4
                    have h5 : Ev.ded t' = Ev.act q m d := h4
                    exact absurd h5 (by simp)

/-- The acting session number is a session of the shape: a decoded action event cannot name a
session the bounds do not contain. -/
theorem lt_shS_of_decEv_act {q : Nat} {m : Term} {d : NonceName}
    (h : decEv (shapeOf P B) P a i = Ev.act q m d) : q < shS (shapeOf P B) :=
  (decode_some_of_decEv_act h).2

/-- Recovering the event code from the decoded event. If the decoded event at step i is the
action of session q, the event code the assignment selected is 1 + q. No Sat hypothesis is
needed: the one-hot group is what the clauses constrain, but decCode is defined by reading off
the same decode call that decEv pattern-matches on, so the two can never disagree. -/
theorem decCode_of_decEv_act {q : Nat} {m : Term} {d : NonceName}
    (h : decEv (shapeOf P B) P a i = Ev.act q m d) : decCode P B a i = 1 + q := by
  obtain ⟨hd, _⟩ := decode_some_of_decEv_act h
  unfold decCode
  rw [hd]
  rfl

/-- The companion for a deduction step: the code names a deduction instance of the shape, and
that instance's conclusion is the message the event teaches. -/
theorem decode_some_of_decEv_ded {t : Term}
    (h : decEv (shapeOf P B) P a i = Ev.ded t) :
    ∃ (n : Nat), n < nInst (shapeOf P B)
      ∧ (evOh (shapeOf P B) i).decode a = some (1 + shS (shapeOf P B) + n)
      ∧ ∃ ins, instAt (shapeOf P B) n = some ins ∧ valAt (shapeOf P B) ins.concl = some t := by
  unfold decEv at h
  cases hd : (evOh (shapeOf P B) i).decode a with
  | none =>
      rw [hd] at h
      have h2 : Ev.idle = Ev.ded t := h
      exact absurd h2 (by simp)
  | some k =>
      rw [hd] at h
      have hred : (if k = 0 then Ev.idle else
            if h : k < 1 + shS (shapeOf P B) then
              Ev.act (k - 1) (decDeliver (shapeOf P B) a i (k - 1)) (decNonce (shapeOf P B) a i (k - 1))
            else
              match instAt (shapeOf P B) (k - 1 - shS (shapeOf P B)) with
              | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
              | none => Ev.idle) = Ev.ded t := h
      cases k with
      | zero =>
          have h2 : Ev.idle = Ev.ded t := hred
          exact absurd h2 (by simp)
      | succ k' =>
          have h3 : (if h : k'.succ < 1 + shS (shapeOf P B) then
              Ev.act k' (decDeliver (shapeOf P B) a i k') (decNonce (shapeOf P B) a i k')
            else
              match instAt (shapeOf P B) (k' - shS (shapeOf P B)) with
              | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
              | none => Ev.idle) = Ev.ded t := hred
          by_cases hlt : k'.succ < 1 + shS (shapeOf P B)
          · rw [dite_eq_left hlt] at h3
            exact absurd h3 (by simp)
          · rw [dite_eq_right hlt] at h3
            cases hins : instAt (shapeOf P B) (k' - shS (shapeOf P B)) with
            | none =>
                rw [hins] at h3
                have h4 : Ev.idle = Ev.ded t := h3
                exact absurd h4 (by simp)
            | some ins =>
                rw [hins] at h3
                have h4 : (match valAt (shapeOf P B) ins.concl with
                    | some t => Ev.ded t
                    | none => Ev.idle) = Ev.ded t := h3
                cases hv : valAt (shapeOf P B) ins.concl with
                | none =>
                    rw [hv] at h4
                    have h5 : Ev.idle = Ev.ded t := h4
                    exact absurd h5 (by simp)
                | some t' =>
                    rw [hv] at h4
                    have h5 : Ev.ded t' = Ev.ded t := h4
                    have ht : t' = t := Ev.ded.inj h5
                    refine ⟨k' - shS (shapeOf P B), ?_, congrArg some (by omega), ins, hins, ?_⟩
                    · rw [instAt] at hins
                      by_contra e
                      have h6 := rget_oob_ge (dedInsts (shapeOf P B)) (k' - shS (shapeOf P B))
                        (by simpa [nInst] using e)
                      rw [h6] at hins
                      exact absurd hins (by simp)
                    · rw [hv, ht]

/-- The code of a deduction step is the offset of the instance that fired. -/
theorem decCode_of_decEv_ded {t : Term}
    (h : decEv (shapeOf P B) P a i = Ev.ded t) :
    ∃ (n : Nat), n < nInst (shapeOf P B) ∧
      decCode P B a i = 1 + shS (shapeOf P B) + n := by
  obtain ⟨n, hn, hd, _, _⟩ := decode_some_of_decEv_ded h
  refine ⟨n, hn, ?_⟩
  unfold decCode
  rw [hd]
  rfl

/-- If the selected event code is not 0, the event group really did select it: decCode
only differs from decode by folding the none case to 0. -/
theorem decode_eq_some_decCode {i : Nat} (h : decCode P B a i ≠ 0) :
    (evOh (shapeOf P B) i).decode a = some (decCode P B a i) := by
  cases hd : (evOh (shapeOf P B) i).decode a with
  | none =>
      have h0 : decCode P B a i = 0 := by unfold decCode; rw [hd]; rfl
      exact absurd h0 h
  | some k =>
      have h1 : decCode P B a i = k := by unfold decCode; rw [hd]; rfl
      exact congrArg some h1.symm

/-- The Sat-free twin of decEv_act_of_code. If the selected event code is 1 + q and q is a
session of the shape, the decoded event is the action of session q. The repository's version
(ProtSat.Encoding.decEv_act_of_code) needs Sat a (encode P B), because it goes through the
one-hot clauses; this one reads the definition of decEv directly, so it survives on an
agreement-only formula. -/
theorem decEv_act_of_decCode {q : Nat} (hq : q < shS (shapeOf P B))
    (hk : decCode P B a i = 1 + q) :
    decEv (shapeOf P B) P a i =
      Ev.act q (decDeliver (shapeOf P B) a i q) (decNonce (shapeOf P B) a i q) := by
  have hd0 : (evOh (shapeOf P B) i).decode a = some (decCode P B a i) :=
    decode_eq_some_decCode (by omega : decCode P B a i ≠ 0)
  have hd : (evOh (shapeOf P B) i).decode a = some (q + 1) :=
    hd0.trans (congrArg some (by omega : decCode P B a i = q + 1))
  -- Written with q + 1 rather than 1 + q on purpose: Nat.add recurses on its second
  -- argument, so q + 1 reduces to succ q and the "is the code zero" test can decide it.
  have hne : decEv (shapeOf P B) P a i =
      (if h : q + 1 < 1 + shS (shapeOf P B) then
        Ev.act (q + 1 - 1) (decDeliver (shapeOf P B) a i (q + 1 - 1))
          (decNonce (shapeOf P B) a i (q + 1 - 1))
      else
        match instAt (shapeOf P B) (q + 1 - 1 - shS (shapeOf P B)) with
        | some inst => match valAt (shapeOf P B) inst.concl with
          | some t => Ev.ded t
          | none => Ev.idle
        | none => Ev.idle) := by
    unfold decEv
    rw [hd]
    rfl
  rw [hne, dite_eq_left (by omega : q + 1 < 1 + shS (shapeOf P B))]
  rfl

/-- The whole decoded trace read by position. Specialising the event index lemma to
n = B.steps: position i of the complete decoded trace is the event of step i. This is the
form the agreement SOUND proof consumes, because the trace it must feed to the claim/commit
monitor is the whole trace. -/
theorem evAt_decEvsFrom_steps {i : Nat} (hi : i < B.steps) :
    Complete.evAt (decEvsFrom P B a B.steps) i = decEv (shapeOf P B) P a i := by
  rw [evAt_decEvsFrom (Nat.le_refl _) hi]
  rw [show B.steps - B.steps + i = i by omega]

/-- The whole decoded visit list read by position. Position i of the complete decoded
configuration list is the configuration of the decoded run at step i. -/
theorem cfgAt_decCfgsFrom_steps {i : Nat} (hi : i ≤ B.steps) :
    Complete.cfgAt (decCfgsFrom P B a B.steps) i = decRun P B a i := by
  rw [cfgAt_decCfgsFrom (Nat.le_refl _) hi]
  rw [show B.steps - B.steps + i = i by omega]

/-- A code the event group can select is below the number of event alternatives of the shape:
decode only ever returns an element of the group's domain, and evOh's domain is
List.range (shEv sh). No clause hypothesis is used. -/
theorem lt_shEv_of_decode_some {i k : Nat}
    (h : (evOh (shapeOf P B) i).decode a = some k) : k < shEv (shapeOf P B) := by
  have hvals : (evOh (shapeOf P B) i).vals = List.range (shEv (shapeOf P B)) := rfl
  have h2 : decodeGo (evOh (shapeOf P B) i).vals (evOh (shapeOf P B) i).varOf a = some k := h
  have hmem : k ∈ (evOh (shapeOf P B) i).vals := (decodeGo_some _ _ _ _ h2).1
  rw [hvals] at hmem
  exact List.mem_range.mp hmem

/-- **What an idle decoded event can tell you without any clause hypothesis.** Either the
selected code is 0 - the honest idle - or the code names a deduction instance and the event
idled because that instance teaches nothing the shape can name. The second alternative cannot
actually happen for a shapeOf P B (every deduction instance's conclusion is a universe
message), but that is a theorem about ProtSat.Encode.dedInstsOf, not about decEv, which is
why the disjunction is as far as this file can go. -/
theorem decEv_idle_cases {i : Nat} (h : decEv (shapeOf P B) P a i = Ev.idle) :
    decCode P B a i = 0
    ∨ ∃ n, n < nInst (shapeOf P B) ∧ decCode P B a i = 1 + shS (shapeOf P B) + n := by
  cases hd : (evOh (shapeOf P B) i).decode a with
  | none =>
      left
      unfold decCode
      rw [hd]
      rfl
  | some k =>
      unfold decEv at h
      rw [hd] at h
      have hred : (if k = 0 then Ev.idle else
            if h : k < 1 + shS (shapeOf P B) then
              Ev.act (k - 1) (decDeliver (shapeOf P B) a i (k - 1)) (decNonce (shapeOf P B) a i (k - 1))
            else
              match instAt (shapeOf P B) (k - 1 - shS (shapeOf P B)) with
              | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
              | none => Ev.idle) = Ev.idle := h
      cases k with
      | zero =>
          left
          unfold decCode
          rw [hd]
          rfl
      | succ k' =>
          have h3 : (if h : k'.succ < 1 + shS (shapeOf P B) then
              Ev.act k' (decDeliver (shapeOf P B) a i k') (decNonce (shapeOf P B) a i k')
            else
              match instAt (shapeOf P B) (k' - shS (shapeOf P B)) with
              | some inst => match valAt (shapeOf P B) inst.concl with
                | some t => Ev.ded t
                | none => Ev.idle
              | none => Ev.idle) = Ev.idle := hred
          by_cases hlt : k'.succ < 1 + shS (shapeOf P B)
          · rw [dite_eq_left hlt] at h3
            exact absurd h3 (by simp)
          · right
            have hk' : decCode P B a i = k'.succ := by unfold decCode; rw [hd]; rfl
            have hlt' : k'.succ < 1 + shS (shapeOf P B) + nInst (shapeOf P B) :=
              lt_shEv_of_decode_some hd
            refine ⟨k' - shS (shapeOf P B), by omega, ?_⟩
            rw [hk']
            omega

/-- The decoded event is idle when the event group selected nothing: the none branch of decEv
and the getD 0 of decCode are the same convention. -/
theorem decEv_idle_of_decode_none {i : Nat}
    (h : (evOh (shapeOf P B) i).decode a = none) :
    decEv (shapeOf P B) P a i = Ev.idle ∧ decCode P B a i = 0 := by
  refine ⟨by unfold decEv; rw [h], by unfold decCode; rw [h]; rfl⟩

/-! ### The reindexed pair really is a run segment -/

/-- **The decoded segment is a run, pointwise.** Reading the decoded event and configuration
segments by position, every position is a transition of the operational semantics - inside the
segment by the step clauses, and past the end because a finished run idles. This is
ProtSat.Encoding.decRunFrom_runs read through ProtSat.Complete.runs_rel. -/
theorem relAt_decSegment (h : Sat a (encode P B)) (hU : univClosed (shapeOf P B) P)
    (n : Nat) (hn : n ≤ B.steps) (i : Nat) :
    Rel P (Complete.cfgAt (decCfgsFrom P B a n) i)
        (Complete.evAt (decEvsFrom P B a n) i)
        (Complete.cfgAt (decCfgsFrom P B a n) (i + 1)) :=
  (Complete.runs_rel (decRunFrom_runs h hU n hn)).2 i

/-- **The step relation inside the segment, re-indexed to absolute steps.** For position i of
the last n steps, the decoded run takes the step the semantics prescribes: from
decRun (steps - n + i) to decRun (steps - n + i + 1) on the event decEv (steps - n + i). -/
theorem decSegment_rel (h : Sat a (encode P B)) (hU : univClosed (shapeOf P B) P)
    (n : Nat) (hn : n ≤ B.steps) (i : Nat) (hi : i < n) :
    Rel P (decRun P B a (B.steps - n + i))
        (decEv (shapeOf P B) P a (B.steps - n + i))
        (decRun P B a (B.steps - n + (i + 1))) := by
  have h1 := relAt_decSegment h hU n hn i
  rw [cfgAt_decCfgsFrom hn (by omega), evAt_decEvsFrom hn hi,
      cfgAt_decCfgsFrom hn (by omega : i + 1 ≤ n)] at h1
  exact h1

/-- The reindexed pair is a run segment in the inductive sense: the last n decoded steps form
a run that starts where the decoded run was after steps - n steps. This restates
ProtSat.Encoding.decRunFrom_runs; it is here so the ingredients of this file are used. -/
theorem runs_decSegment (h : Sat a (encode P B)) (hU : univClosed (shapeOf P B) P)
    (n : Nat) (hn : n ≤ B.steps) :
    Runs P (decRun P B a (B.steps - n)) (decEvsFrom P B a n) (decCfgsFrom P B a n) :=
  decRunFrom_runs h hU n hn

/-- The full decoded segment starts at the initial configuration: reading the whole decoded
run at position 0 gives initCfg P. No hypothesis is needed: the segment always begins where
the run begins. -/
theorem cfgAt_decCfgsFrom_steps_zero :
    Complete.cfgAt (decCfgsFrom P B a B.steps) 0 = initCfg P := by
  rw [cfgAt_decCfgsFrom_zero (Nat.le_refl _)]
  rw [show B.steps - B.steps = 0 by omega]
  unfold decRun
  rfl
