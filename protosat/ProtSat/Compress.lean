/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Contract

/-!
# ProtSat: trace compression (roadmap stage 9)

## Why this module exists

Every safety statement in ProtSat is indexed by a step count the *user* chose: `Query.bounds.steps`
says how many events an execution may have, and `boundedSafe q` only speaks about executions inside
that number. A verdict is therefore only as good as the number written next to it, and nothing
in the model tells the analyst which number to write down.

This module starts closing that gap for the current **straight-line** role language. Because no role
contains a jump or a loop, the model itself answers the question "how many session actions can ever
happen": the answer is `actionCount P`, the total number of actions over the instantiated sessions.
Together with the finite message universe `univ P B`, that yields a bound *derived from the model*
such that safety up to the derived bound is safety for executions of every length that stays inside
the same sessions and the same message universe.

The three ingredients are:

* **T1** (`sessEv_count_le_actionCount`): every run performs at most `actionCount P` session events,
  because every session event advances a program counter and no counter can pass its role's length.
* **T2** (`ded_steps_le_univ`): inside a duplicate-free universe `U`, a chain of deduction
  steps that each contribute a message the attacker did not already know has length at most
  `U.length`.
* **T3** (`runs_dropRedundant`): an idle event, and a deduction event whose message is already
  known, can be removed from a run. Not *literally*: the list representation of knowledge means
  `Ev.ded t` at a configuration that already knows `t` still changes the configuration, by
  appending a second copy. Removal is therefore proved against the extensional equality of
  configurations `CfgEq`, a congruence for the step relation and for every predicate the contract
  reads off a configuration.

## What this module does not do

It does not canonicalise the knowledge representation, and it does not compress traces that witness
the *authentication* goals: `Inst.idx` records a position in the trace, and shortening a trace
renumbers every later position, so `authBreak` is not invariant under the removal T3 performs
without a further argument about reindexing. The compression theorem proved here is the one for
`Goal.secrecy`, which is the goal the contract's gates and the whole CNF pipeline are built around.

Nothing here imports the CNF, the SAT solver or the encoding: this is a theorem about the repaired
reference semantics of `ProtSat.Reference`. Because the *old* semantics declares `Cfg`, `Ev`,
`initCfg`, `Rel`, `Runs`, `pcOf`, `sessAt` and `storeOf` directly in `ProtSat`, this module
refers to the repaired ones as `Reference.x` throughout.
-/

namespace ProtSat.Compress

open ProtSat Term Protocol Attacker
open ProtSat.Reference.Explore
open ProtSat.Reference.Contract

/-- The repaired configuration type, spelled out once so the statements below stay readable. -/
abbrev RCfg := ProtSat.Reference.Cfg

/-! ### Three list facts the counting arguments need -/

/-- Splitting a list at an occurrence of one of its elements: every element sits between a prefix
that avoids it and a suffix. -/
theorem List.exists_split_of_mem {α : Type} [DecidableEq α] :
    ∀ {l : List α} {a : α}, a ∈ l -> ∃ t u, l = t ++ [a] ++ u ∧ a ∉ t := by
  intro l
  induction l with
  | nil => intro a h; exact absurd h (by simp)
  | cons x xs ih =>
      intro a h
      by_cases hx : x = a
      · subst hx
        exact ⟨[], xs, by simp, by simp⟩
      · obtain (he | ht) := List.mem_cons.mp h
        · exact absurd he.symm hx
        · obtain ⟨t, u, h1, h2⟩ := ih ht
          refine ⟨x :: t, u, ?_, ?_⟩
          · rw [h1]
            rfl
          · intro h3
            rw [List.mem_cons] at h3
            obtain (he | ht') := h3
            · exact absurd he.symm hx
            · exact h2 ht'

/-- A duplicate-free list stays duplicate-free when repeated elements are dropped. -/
theorem List.nodup_eraseDups {α : Type} [DecidableEq α] :
    ∀ (l : List α), l.eraseDups.Nodup := by
  have h : ∀ (n : Nat) (l : List α), l.length ≤ n -> l.eraseDups.Nodup := by
    intro n
    induction n with
    | zero =>
        intro l hl
        cases l with
        | nil => simp
        | cons a as => exact absurd hl (by simp [List.length_cons])
    | succ n ih =>
        intro l hl
        cases l with
        | nil => simp
        | cons a as =>
            rw [List.length_cons] at hl
            rw [List.eraseDups_cons]
            refine List.Nodup.cons ?_ (ih (as.filter fun b => !b == a) ?_)
            · intro hmem
              rw [List.mem_eraseDups, List.mem_filter] at hmem
              exact absurd hmem.2 (by simp)
            · have := List.length_filter_le (fun b => !b == a) as
              omega
  intro l
  exact h l.length l (Nat.le_refl _)

/-- **Counting.** A duplicate-free list whose elements all lie in a duplicate-free list `k` has at
most `k.length` elements. This is the only place finiteness of the universe is used. -/
theorem List.length_le_of_nodup_forall_mem {α : Type} [DecidableEq α] :
    ∀ (k : List α), k.Nodup -> ∀ (l : List α), l.Nodup ->
      (∀ a ∈ l, a ∈ k) -> l.length ≤ k.length := by
  intro k
  induction k with
  | nil =>
      intro _ l _ hmem
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons a as => exact absurd (hmem a (List.Mem.head _)) (by simp)
      rw [hnil]
  | cons b bs ih =>
      intro hk l hl hmem
      have hbs : bs.Nodup := hk.tail
      by_cases hb : b ∈ l
      · obtain ⟨t, u, hl_eq, hnot⟩ := List.exists_split_of_mem hb
        have h1 : ((t ++ [b]) ++ u).Nodup := by rw [← hl_eq]; exact hl
        obtain ⟨htb, hu, hdisj⟩ := List.nodup_append.mp h1
        obtain ⟨ht, hb1, hdisj2⟩ := List.nodup_append.mp htb
        have hbu' : b ∉ u := fun hc => hdisj b (List.mem_append_right t (List.Mem.head _)) b hc rfl
        have hut : (t ++ u).Nodup := by
          rw [List.nodup_append]
          exact ⟨ht, hu, fun a ha c hc => hdisj a (List.mem_append_left [b] ha) c hc⟩
        have hmem' : ∀ a ∈ t ++ u, a ∈ bs := by
          intro a ha
          rw [List.mem_append] at ha
          obtain (ht' | hu') := ha
          · have hal : a ∈ l := by
              rw [hl_eq, List.mem_append, List.mem_append, List.mem_singleton]
              exact Or.inl (Or.inl ht')
            obtain (hab | hbs) := List.mem_cons.mp (hmem a hal)
            · exfalso
              exact hnot (hab ▸ ht')
            · exact hbs
          · have hal : a ∈ l := by
              rw [hl_eq, List.mem_append, List.mem_append, List.mem_singleton]
              exact Or.inr hu'
            obtain (hab | hbs) := List.mem_cons.mp (hmem a hal)
            · exfalso
              exact hbu' (hab ▸ hu')
            · exact hbs
        have hle := ih hbs (t ++ u) hut hmem'
        rw [hl_eq]
        rw [List.length_append] at hle
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · have hmem' : ∀ a ∈ l, a ∈ bs := by
          intro a ha
          obtain (hab | hbs) := List.mem_cons.mp (hmem a ha)
          · exfalso
            exact hb (hab ▸ ha)
          · exact hbs
        exact Nat.le_succ_of_le (ih hbs l hl hmem')

/-- Two functions that agree below `n` have maps over `List.range n` with the same sum. -/
theorem List.sum_range_congr {f g : Nat -> Nat} :
    ∀ {n : Nat}, (∀ i, i < n -> f i = g i) ->
      (List.map f (List.range n)).sum = (List.map g (List.range n)).sum := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The sum over `List.range n` where one index is raised by one: the total drops by one. -/
theorem List.sum_range_upd {f g : Nat -> Nat} {n q : Nat} (hq : q < n)
    (h1 : f q + 1 = g q) (h2 : ∀ i, i ≠ q -> f i = g i) :
    (List.map f (List.range n)).sum + 1 = (List.map g (List.range n)).sum := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      by_cases hn : n = q
      · subst hn
        rw [List.sum_range_congr (fun i hi => h2 i (by omega))]
        omega
      · have hIH : (List.map f (List.range n)).sum + 1 = (List.map g (List.range n)).sum :=
          ih (by omega)
        have hfn : f n = g n := h2 n hn
        omega

/-! ### T1: the session-action bound derived from the model -/

/-- The session an event names, if it names one. -/
def evSession : ProtSat.Reference.Ev -> Option Nat
  | ProtSat.Reference.Ev.recv q _ => some q
  | ProtSat.Reference.Ev.generate q _ => some q
  | ProtSat.Reference.Ev.act q => some q
  | _ => none

/-- A `session event` names a session, and therefore moves that session's program counter. The
other two events, `Ev.idle` and `Ev.ded`, are attacker events: they touch no session at all. -/
def isSessEv : ProtSat.Reference.Ev -> Bool
  | ProtSat.Reference.Ev.recv _ _ => true
  | ProtSat.Reference.Ev.generate _ _ => true
  | ProtSat.Reference.Ev.act _ => true
  | _ => false

/-- Two sessions named by the same event are the same session. -/
theorem evSession_eq {e : ProtSat.Reference.Ev} {s q : Nat}
    (h1 : evSession e = some s) (h2 : evSession e = some q) : s = q := by
  have h : some s = some q := by rw [← h1, ← h2]
  exact Option.some.inj h

/-- Every event either names exactly one session or names none. -/
theorem evSession_some_or_none (e : ProtSat.Reference.Ev) :
    (∃ s, evSession e = some s) ∨ evSession e = none := by
  cases e
  · exact Or.inr rfl
  · rename_i t; exact Or.inr rfl
  · rename_i s m; exact Or.inl ⟨s, rfl⟩
  · rename_i s n; exact Or.inl ⟨s, rfl⟩
  · rename_i s; exact Or.inl ⟨s, rfl⟩

/-- **H, the derived session-action bound of a protocol**: the total number of actions over the
sessions the model instantiates. Because the role language is straight line - no action jumps, and
every session event advances a program counter by exactly one - this is also the greatest number of
session events any execution can perform. -/
def actionCount (P : Protocol) : Nat :=
  ((List.range P.sessions.length).map (fun q => P.roleLen q)).sum

/-- The **control fuel** of a configuration: how many session actions are still possible. Session
`q` may still execute `roleLen P q - pcOf C q` actions, and `fuel` is the sum over the sessions. -/
def fuel (P : Protocol) (C : RCfg) : Nat :=
  ((List.range P.sessions.length).map (fun q => P.roleLen q - ProtSat.Reference.pcOf C q)).sum

/-- Indexing a mapped list maps the index. -/
theorem rget_map {α β : Type} (f : α -> β) :
    ∀ (l : List α) (q : Nat), ProtSat.rget (l.map f) q = (ProtSat.rget l q).map f := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons x xs ih =>
      intro q
      cases q with
      | zero => rfl
      | succ q => simpa [ProtSat.rget] using ih q

/-- Every session of the initial configuration sits at program counter zero. -/
theorem pcOf_initCfg (P : Protocol) (q : Nat) :
    ProtSat.Reference.pcOf (ProtSat.Reference.initCfg P) q = 0 := by
  unfold ProtSat.Reference.pcOf ProtSat.Reference.sessAt ProtSat.Reference.initCfg
  rw [rget_map]
  cases ProtSat.rget P.sessions q with
  | none => rfl
  | some s => rfl

/-- **The derived bound is the initial fuel.** -/
theorem fuel_initCfg (P : Protocol) : fuel P (ProtSat.Reference.initCfg P) = actionCount P := by
  unfold fuel actionCount
  refine List.sum_range_congr
    (f := fun q => P.roleLen q - ProtSat.Reference.pcOf (ProtSat.Reference.initCfg P) q)
    (g := fun q => P.roleLen q) ?_
  intro q _
  rw [pcOf_initCfg]
  omega

/-- Writing a session state never changes the length of the session vector. -/
theorem rput_length {α : Type} (f : α -> α) :
    ∀ (l : List α) (q : Nat), (ProtSat.rput f l q).length = l.length := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons x xs ih =>
      intro q
      cases q with
      | zero => rfl
      | succ q => simp [ProtSat.rput, ih q]

/-- An in-range index finds an element. -/
theorem rget_some_of_lt {α : Type} :
    ∀ (l : List α) (q : Nat), q < l.length -> ∃ x, ProtSat.rget l q = some x := by
  intro l
  induction l with
  | nil => intro q h; exact absurd h (by simp)
  | cons x xs ih =>
      intro q h
      cases q with
      | zero => exact ⟨x, rfl⟩
      | succ q => exact ih q (by simpa using h)

@[simp] theorem mapSess_sess (f : SessState -> SessState) (C : RCfg) (q : Nat) :
    (ProtSat.Reference.mapSess f C q).sess = ProtSat.rput f C.sess q := rfl

/-- Configurations with the same session vector have the same program counters. -/
theorem pcOf_congr_sess {C D : RCfg} (h : C.sess = D.sess) (q : Nat) :
    ProtSat.Reference.pcOf C q = ProtSat.Reference.pcOf D q := by
  unfold ProtSat.Reference.pcOf ProtSat.Reference.sessAt
  rw [h]

/-- A session update leaves every *other* program counter alone. -/
theorem pcOf_mapSess_other {C : RCfg} {f : SessState -> SessState} {q s : Nat} (h : s ≠ q) :
    ProtSat.Reference.pcOf (ProtSat.Reference.mapSess f C q) s = ProtSat.Reference.pcOf C s := by
  unfold ProtSat.Reference.pcOf ProtSat.Reference.sessAt ProtSat.Reference.mapSess
  rw [rget_rput_other h]

/-- A session update whose function advances the counter advances that counter by one. -/
theorem pcOf_mapSess_pc {C : RCfg} {f : SessState -> SessState} {q : Nat}
    (hf : ∀ s, (f s).pc = s.pc + 1) (hq : q < C.sess.length) :
    ProtSat.Reference.pcOf (ProtSat.Reference.mapSess f C q) q =
      ProtSat.Reference.pcOf C q + 1 := by
  obtain ⟨s, hs⟩ := rget_some_of_lt C.sess q hq
  unfold ProtSat.Reference.pcOf ProtSat.Reference.sessAt ProtSat.Reference.mapSess
  rw [rget_rput_same, hs]
  simp [Option.map_some, Option.getD_some, hf]

/-- **What a deterministic action does to the session vector.** Every action that can execute
advances the acting session by exactly one and touches no other session. This is the straight-line
property: the role language has no jump, so a program counter only ever moves forward by one. -/
theorem actStep_sess {P : Protocol} {C C' : RCfg} {q : Nat} {act : Action}
    (h : ProtSat.Reference.actStep P C q act = some C') :
    ∃ f : SessState -> SessState, (∀ s, (f s).pc = s.pc + 1) ∧
      C'.sess = ProtSat.rput f C.sess q := by
  cases act with
  | fresh _ _ => simp [ProtSat.Reference.actStep] at h
  | recv _ _ => simp [ProtSat.Reference.actStep] at h
  | send _ e =>
      cases he : Expr.eval e (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he] at h
      | some t =>
          simp [ProtSat.Reference.actStep, he] at h
          subst h
          exact ⟨ProtSat.bump, fun s => rfl, rfl⟩
  | assign x e =>
      cases he : Expr.eval e (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he] at h
      | some t =>
          simp [ProtSat.Reference.actStep, he] at h
          subst h
          exact ⟨ProtSat.bumpStore x t, fun s => rfl, rfl⟩
  | check e1 e2 =>
      cases he1 : Expr.eval e1 (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he1] at h
      | some v1 =>
          cases he2 : Expr.eval e2 (ProtSat.Reference.storeOf C q) with
          | none => simp [ProtSat.Reference.actStep, he1, he2] at h
          | some v2 =>
              by_cases hv : v1 == v2
              · simp [ProtSat.Reference.actStep, he1, he2, hv] at h
                subst h
                exact ⟨ProtSat.bump, fun s => rfl, rfl⟩
              · simp [ProtSat.Reference.actStep, he1, he2, hv] at h
  | secret e =>
      cases he : Expr.eval e (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he] at h
      | some t =>
          simp [ProtSat.Reference.actStep, he] at h
          subst h
          exact ⟨ProtSat.bump, fun s => rfl, rfl⟩
  | claim tag peer v =>
      by_cases hd : (ProtSat.Reference.authData P C q peer v).isSome
      · simp [ProtSat.Reference.actStep, hd] at h
        subst h
        exact ⟨ProtSat.bump, fun s => rfl, rfl⟩
      · simp [ProtSat.Reference.actStep, hd] at h
  | commit tag peer v =>
      by_cases hd : (ProtSat.Reference.authData P C q peer v).isSome
      · simp [ProtSat.Reference.actStep, hd] at h
        subst h
        exact ⟨ProtSat.bump, fun s => rfl, rfl⟩
      · simp [ProtSat.Reference.actStep, hd] at h

/-- **The shape of a step.** An attacker event leaves the session vector alone; a session event
replaces exactly one session by a state whose counter is one higher. Everything T1 needs about the
control state follows from this single case analysis. -/
theorem rel_ev_cases {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    (h : ProtSat.Reference.Rel P C e C') :
    (evSession e = none ∧ C'.sess = C.sess) ∨
      ∃ (s : Nat) (f : SessState -> SessState), (∀ x, (f x).pc = x.pc + 1) ∧
        C'.sess = ProtSat.rput f C.sess s ∧ evSession e = some s := by
  unfold ProtSat.Reference.Rel at h
  cases e
  · left
    simp [ProtSat.Reference.stepOf] at h
    subst h
    exact ⟨rfl, rfl⟩
  · rename_i t
    left
    by_cases hb : oneStepBool C.kn t
    · simp [ProtSat.Reference.stepOf, hb] at h
      subst h
      exact ⟨rfl, rfl⟩
    · simp [ProtSat.Reference.stepOf, hb] at h
  · rename_i s m
    rw [ProtSat.Reference.stepOf] at h
    cases hact : P.actionAt s (ProtSat.Reference.pcOf C s) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | recv _ x =>
            by_cases hm : m ∈ C.kn
            · simp [hact, hm] at h
              subst h
              right
              exact ⟨s, ProtSat.bumpStore x m, fun st => rfl, rfl, rfl⟩
            · simp [hact, hm] at h
        | _ => simp [hact] at h
  · rename_i s n
    rw [ProtSat.Reference.stepOf] at h
    cases hact : P.actionAt s (ProtSat.Reference.pcOf C s) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | fresh x _ =>
            simp [hact] at h
            rcases h with ⟨_, _, heq⟩
            subst heq
            right
            exact ⟨s, ProtSat.bumpStore x (Term.nonce n), fun st => rfl, rfl, rfl⟩
        | _ => simp [hact] at h
  · rename_i s
    rw [ProtSat.Reference.stepOf] at h
    cases hact : P.actionAt s (ProtSat.Reference.pcOf C s) with
    | none => simp [hact] at h
    | some act =>
        rw [hact] at h
        by_cases hu : ProtSat.Reference.actionUsable P C s act
        · simp [hact, hu] at h
          obtain ⟨f, hf, hsess⟩ := actStep_sess h
          right
          exact ⟨s, f, hf, hsess, rfl⟩
        · simp [hact, hu] at h

/-- The session vector keeps its length through a step. -/
theorem sess_length_of_rel {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    (h : ProtSat.Reference.Rel P C e C') : C'.sess.length = C.sess.length := by
  cases rel_ev_cases h with
  | inl h => rw [h.2]
  | inr h =>
      obtain ⟨s, f, _, hsess, _⟩ := h
      rw [hsess, rput_length]

/-- A step that names a session advances exactly that session's program counter. -/
theorem pcOf_of_rel_some {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev} {s : Nat}
    (h : ProtSat.Reference.Rel P C e C') (hs : evSession e = some s) (hq : s < C.sess.length) :
    ProtSat.Reference.pcOf C' s = ProtSat.Reference.pcOf C s + 1 := by
  cases rel_ev_cases h with
  | inl h =>
      rw [h.1] at hs
      exact absurd hs (by simp)
  | inr h =>
      obtain ⟨r, f, hf, hsess, he⟩ := h
      obtain hr : r = s := evSession_eq he hs
      subst hr
      rw [pcOf_congr_sess (hsess.trans (mapSess_sess f C r).symm) r]
      exact pcOf_mapSess_pc hf hq

/-- A step that does not name session `q` leaves `q`'s program counter alone. -/
theorem pcOf_of_rel_ne {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    (h : ProtSat.Reference.Rel P C e C') (q : Nat) (he : evSession e ≠ some q) :
    ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q := by
  cases rel_ev_cases h with
  | inl h => exact pcOf_congr_sess h.2 q
  | inr h =>
      obtain ⟨s, f, _, hsess, hse⟩ := h
      rw [pcOf_congr_sess (hsess.trans (mapSess_sess f C s).symm) q]
      exact pcOf_mapSess_other (fun h2 => he (by rw [hse, h2]))

/-- An attacker event leaves every program counter where it was. -/
theorem pcOf_of_rel_none {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    (h : ProtSat.Reference.Rel P C e C') (hs : evSession e = none) (q : Nat) :
    ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q :=
  pcOf_of_rel_ne h q (fun h2 => absurd (hs ▸ h2) (by simp))

/-- A run of the empty trace visits exactly its initial configuration. -/
theorem runs_nil_inv {P : Protocol} {C : RCfg} {D : List RCfg}
    (h : ProtSat.Reference.Runs P C [] D) :
    D = [C] := by
  have h2 : ProtSat.Reference.run P C [] = some D := h
  exact (Option.some.inj h2).symm

/-- A step that names a session leaves every *other* program counter alone. -/
theorem pcOf_of_rel_some_other {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    {s q : Nat} (h : ProtSat.Reference.Rel P C e C') (hs : evSession e = some s) (hne : q ≠ s) :
    ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q :=
  pcOf_of_rel_ne h q (fun h2 => hne (evSession_eq h2 hs))

/-- If session ~q~ has an action at program counter ~pc~, then ~pc~ is inside the role. -/
theorem lt_roleLen_of_actionAt {P : Protocol} {q pc : Nat} {act : Action}
    (h : P.actionAt q pc = some act) : pc < P.roleLen q := by
  cases hrole : P.roleAt q with
  | none =>
      rw [ProtSat.Protocol.actionAt, hrole] at h
      exact absurd h (by simp)
  | some r =>
      have h2 : (r.acts.drop pc).head? = some act := by
        have h3 : ((P.roleAt q).map (fun rr => (rr.acts.drop pc).head?)).getD none = some act := h
        rw [hrole] at h3
        exact h3
      have hne : r.acts.drop pc ≠ [] := by
        intro hz
        rw [hz] at h2
        exact absurd h2 (by simp)
      have hr' : P.roleLen q = r.acts.length := by
        unfold ProtSat.Protocol.roleLen
        rw [hrole]
      have hlen : (r.acts.drop pc).length = r.acts.length - pc := by rw [List.length_drop]
      have hpos : 0 < (r.acts.drop pc).length := by
        cases l : r.acts.drop pc with
        | nil => exact absurd l hne
        | cons a as => simp
      omega

/-- A session that performs an event of a step is a session the model instantiates, and its program
counter is strictly inside its role. -/
theorem lt_of_rel_sessEv {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    (h : ProtSat.Reference.Rel P C e C') {q : Nat} (hq : evSession e = some q) :
    q < P.sessions.length ∧ ProtSat.Reference.pcOf C q < P.roleLen q := by
  unfold ProtSat.Reference.Rel at h
  cases e
  · simp [evSession] at hq
  · rename_i t
    simp [evSession] at hq
  · rename_i s m
    rw [ProtSat.Reference.stepOf] at h
    cases hact : P.actionAt s (ProtSat.Reference.pcOf C s) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | recv _ _ =>
            by_cases hm : m ∈ C.kn
            · simp [hact, hm] at h
              obtain hsq : s = q := by simpa [evSession] using hq
              subst hsq
              exact ⟨lt_sessions_of_actionAt hact, lt_roleLen_of_actionAt hact⟩
            · simp [hact, hm] at h
        | _ => simp [hact] at h
  · rename_i s n
    rw [ProtSat.Reference.stepOf] at h
    cases hact : P.actionAt s (ProtSat.Reference.pcOf C s) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | fresh _ _ =>
            simp [hact] at h
            obtain hsq : s = q := by simpa [evSession] using hq
            subst hsq
            exact ⟨lt_sessions_of_actionAt hact, lt_roleLen_of_actionAt hact⟩
        | _ => simp [hact] at h
  · rename_i s
    rw [ProtSat.Reference.stepOf] at h
    cases hact : P.actionAt s (ProtSat.Reference.pcOf C s) with
    | none => simp [hact] at h
    | some act =>
        rw [hact] at h
        obtain hsq : s = q := by simpa [evSession] using hq
        subst hsq
        exact ⟨lt_sessions_of_actionAt hact, lt_roleLen_of_actionAt hact⟩

/-- A session that performs an event of a step is a session the model instantiates. -/
theorem lt_sessions_of_rel_sessEv {P : Protocol} {C C' : RCfg} {e : ProtSat.Reference.Ev}
    (h : ProtSat.Reference.Rel P C e C') {q : Nat} (hq : evSession e = some q) :
    q < P.sessions.length := (lt_of_rel_sessEv h hq).1

/-- **T1, per session.** A role cannot execute more steps than it has actions: in any run the number
of events naming session `q` is at most the number of actions `q`'s role still has left. This is the
correct statement for the current language, and it is *not* a hypothesis about the model: roles are
straight-line programs, so no session can act more than `roleLen` times and no run can loop. -/
theorem sessEv_count_le_roleLen {P : Protocol} {q : Nat} {C : RCfg}
    {tr : List ProtSat.Reference.Ev} {Cs : List RCfg}
    (hlen : C.sess.length = P.sessions.length)
    (hpc : ProtSat.Reference.pcOf C q ≤ P.roleLen q)
    (h : ProtSat.Reference.Runs P C tr Cs) :
    (tr.filter (fun e => evSession e = some q)).length ≤
      P.roleLen q - ProtSat.Reference.pcOf C q := by
  induction tr generalizing C Cs with
  | nil =>
      unfold ProtSat.Reference.Runs at h
      simp [ProtSat.Reference.run] at h
      subst h
      simp
  | cons e rest ih =>
      unfold ProtSat.Reference.Runs at h
      cases hstep : ProtSat.Reference.stepOf P C e with
      | none => simp [ProtSat.Reference.run, hstep] at h
      | some C' =>
        have hrel : ProtSat.Reference.Rel P C e C' := hstep
        obtain ⟨Rest, hcs, hRest⟩ := run_cons hstep h
        subst hcs
        have hlen' : C'.sess.length = P.sessions.length := by
          rw [sess_length_of_rel hrel, hlen]
        by_cases he : evSession e = some q
        · obtain ⟨h1, h2⟩ := lt_of_rel_sessEv hrel he
          have hlt : q < C.sess.length := by omega
          have hpc' : ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q + 1 :=
            pcOf_of_rel_some hrel he hlt
          have hbnd : ProtSat.Reference.pcOf C' q ≤ P.roleLen q := by omega
          have hih := ih (C := C') (Cs := Rest) hlen' hbnd hRest
          rw [List.filter_cons_of_pos (by simpa using he)]
          simp only [List.length_cons]
          omega
        · have heq : ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q :=
            pcOf_of_rel_ne hrel q he
          have hpc2 : ProtSat.Reference.pcOf C' q ≤ P.roleLen q := by omega
          have hih := ih (C := C') (Cs := Rest) hlen' hpc2 hRest
          rw [List.filter_cons_of_neg (by simpa using he)]
          omega

/-- The fuel of a configuration is unchanged by a step that is not a session event. -/
theorem fuel_congr {P : Protocol} {C C' : RCfg}
    (h : ∀ q, q < P.sessions.length -> ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q) :
    fuel P C' = fuel P C := by
  unfold fuel
  refine List.sum_range_congr
    (f := fun q => P.roleLen q - ProtSat.Reference.pcOf C' q)
    (g := fun q => P.roleLen q - ProtSat.Reference.pcOf C q) ?_
  intro q hq
  rw [h q hq]

/-- The fuel drops by exactly one when one session advances its counter. -/
theorem fuel_upd {P : Protocol} {C C' : RCfg} {q : Nat} (hq : q < P.sessions.length)
    (hpc : ProtSat.Reference.pcOf C' q = ProtSat.Reference.pcOf C q + 1)
    (hother : ∀ s, s ≠ q -> ProtSat.Reference.pcOf C' s = ProtSat.Reference.pcOf C s)
    (hbound : ProtSat.Reference.pcOf C' q ≤ P.roleLen q) : fuel P C' + 1 = fuel P C := by
  unfold fuel
  refine List.sum_range_upd
    (f := fun q => P.roleLen q - ProtSat.Reference.pcOf C' q)
    (g := fun q => P.roleLen q - ProtSat.Reference.pcOf C q) hq ?_
    (fun s hs => by rw [hother s hs])
  omega

/-- **T1, total.** Every run performs at most `fuel P C` session events. -/
theorem sessEv_count_le_fuel {P : Protocol} {C : RCfg} {tr : List ProtSat.Reference.Ev}
    {Cs : List RCfg} (hlen : C.sess.length = P.sessions.length)
    (hpc : ∀ q, q < P.sessions.length -> ProtSat.Reference.pcOf C q ≤ P.roleLen q)
    (h : ProtSat.Reference.Runs P C tr Cs) :
    (tr.filter (fun e => isSessEv e = true)).length ≤ fuel P C := by
  induction tr generalizing C Cs with
  | nil =>
      unfold ProtSat.Reference.Runs at h
      simp [ProtSat.Reference.run] at h
      subst h
      simp
  | cons e rest ih =>
      unfold ProtSat.Reference.Runs at h
      cases hstep : ProtSat.Reference.stepOf P C e with
      | none => simp [ProtSat.Reference.run, hstep] at h
      | some C' =>
        have hrel : ProtSat.Reference.Rel P C e C' := hstep
        obtain ⟨Rest, hcs, hRest⟩ := run_cons hstep h
        subst hcs
        have hlen' : C'.sess.length = P.sessions.length := by
          rw [sess_length_of_rel hrel, hlen]
        by_cases hu : isSessEv e = true
        · obtain ⟨q, hq⟩ : ∃ q, evSession e = some q := by
            cases e
            · simp [isSessEv] at hu
            · rename_i t; simp [isSessEv] at hu
            · rename_i s m; exact ⟨s, rfl⟩
            · rename_i s n; exact ⟨s, rfl⟩
            · rename_i s; exact ⟨s, rfl⟩
          have hq' : q < P.sessions.length := lt_sessions_of_rel_sessEv hrel hq
          have hstrict : ProtSat.Reference.pcOf C q < P.roleLen q := (lt_of_rel_sessEv hrel hq).2
          have hpc' : ∀ s, s < P.sessions.length -> ProtSat.Reference.pcOf C' s ≤ P.roleLen s := by
            intro s hs
            by_cases he : evSession e = some s
            · obtain ⟨h1, h2⟩ := lt_of_rel_sessEv hrel he
              have := pcOf_of_rel_some hrel he (by omega)
              omega
            · rw [pcOf_of_rel_ne hrel s he]
              exact hpc s hs
          have hih := ih (C := C') (Cs := Rest) hlen' hpc' hRest
          rw [List.filter_cons_of_pos (by simpa using hu)]
          simp only [List.length_cons]
          have hfu : fuel P C' + 1 = fuel P C :=
            fuel_upd hq' (pcOf_of_rel_some hrel hq (by omega))
              (fun s hs => pcOf_of_rel_some_other hrel hq hs)
              (by rw [pcOf_of_rel_some hrel hq (by omega)]; omega)
          omega
        · rw [List.filter_cons_of_neg (by simpa using hu)]
          have hnone : evSession e = none := by
            cases e <;> simp_all [evSession, isSessEv]
          have hpc' : ∀ s, s < P.sessions.length -> ProtSat.Reference.pcOf C' s ≤ P.roleLen s := by
            intro s hs
            rw [pcOf_of_rel_none hrel hnone s]
            exact hpc s hs
          have hih := ih (C := C') (Cs := Rest) hlen' hpc' hRest
          have hcong : fuel P C' = fuel P C :=
            fuel_congr (fun s hs => pcOf_of_rel_none hrel hnone s)
          omega

/-- **T1 at the initial configuration.** Any run of `P` from its initial configuration performs at
most `actionCount P` session events: the bound comes from the model, not the analyst. -/
theorem sessEv_count_le_actionCount {P : Protocol} {tr : List ProtSat.Reference.Ev}
    {Cs : List RCfg} (h : ProtSat.Reference.Runs P (ProtSat.Reference.initCfg P) tr Cs) :
    (tr.filter (fun e => isSessEv e = true)).length ≤ actionCount P := by
  have hlen : (ProtSat.Reference.initCfg P).sess.length = P.sessions.length := by
    unfold ProtSat.Reference.initCfg
    exact List.length_map _
  have hpc : ∀ q, q < P.sessions.length ->
      ProtSat.Reference.pcOf (ProtSat.Reference.initCfg P) q ≤ P.roleLen q := by
    intro q _
    rw [pcOf_initCfg]
    omega
  have := sessEv_count_le_fuel hlen hpc h
  rwa [fuel_initCfg] at this

/-! ### T2: deduction saturation inside a finite universe -/

/-- The message a deduction event proposes, with an arbitrary value for events that are not
deductions. -/
def dedMsg : ProtSat.Reference.Ev -> Term
  | ProtSat.Reference.Ev.ded t => t
  | _ => Term.agent 0

/-- A deduction event's message is what `dedMsg` reports. -/
theorem dedMsg_ded (t : Term) : dedMsg (ProtSat.Reference.Ev.ded t) = t := rfl

/-- `NewDeds tr Cs`: the trace `tr` consists only of deduction events, and each of them proposes a
message the configuration it fires from does **not** already contain. This is the "genuinely new"
hypothesis of the saturation bound. -/
inductive NewDeds : List ProtSat.Reference.Ev -> List RCfg -> Prop where
  | nil : ∀ C, NewDeds [] [C]
  | cons : ∀ (C : RCfg) (t : Term) (tr : List ProtSat.Reference.Ev) (Cs : List RCfg),
      t ∉ C.kn -> NewDeds tr Cs -> NewDeds (ProtSat.Reference.Ev.ded t :: tr) (C :: Cs)

/-- Inversion for `NewDeds`: a nonempty trace of new deductions has a head message that is not in
the head configuration, and a tail that is again all new deductions. -/
theorem newDeds_inv {t : Term} {tr : List ProtSat.Reference.Ev} {C : RCfg} {Cs : List RCfg}
    (h : NewDeds (ProtSat.Reference.Ev.ded t :: tr) (C :: Cs)) : t ∉ C.kn ∧ NewDeds tr Cs := by
  cases h with
  | cons _ _ _ _ h1 h2 => exact ⟨h1, h2⟩

/-- The message universe is duplicate-free by construction: it ends with an `eraseDups`. -/
theorem univ_nodup (P : Protocol) (B : Bounded.Bounds) : (Bounded.univ P B).Nodup :=
  List.nodup_eraseDups _

/-- **T2: the deduction saturation bound.** Inside a finite universe, a chain of deduction
steps that each add a genuinely new message has length at most the size of the universe: the
attacker can learn
each message once, and it cannot learn a message it already holds. -/
theorem ded_steps_le_univ {P : Protocol} {B : Bounded.Bounds}
    {tr : List ProtSat.Reference.Ev} {Cs : List RCfg} (h : BoundedRun P B tr Cs)
    (hd : NewDeds tr Cs) : tr.length ≤ (Bounded.univ P B).length := by
  classical
  obtain ⟨hrun, _hlen, hb⟩ := h
  -- The deduced messages are pairwise distinct, they all lie in the universe, and none of them was
  -- known at the start. The last of these three is what makes the induction go through: a message
  -- that is new at every step can never repeat a message learned earlier.
  have hmain : ∀ (C : RCfg) (tr : List ProtSat.Reference.Ev) (Cs : List RCfg),
      ProtSat.Reference.Runs P C tr Cs -> NewDeds tr Cs -> (∀ C' ∈ Cs, inBounds P B C') ->
        ((tr.map dedMsg).Nodup ∧ (∀ m ∈ tr.map dedMsg, m ∈ Bounded.univ P B) ∧
          (∀ t ∈ C.kn, t ∉ tr.map dedMsg)) := by
    intro C tr
    induction tr generalizing C with
    | nil =>
        intro Cs hrun _ _
        have hcs := runs_nil_inv hrun
        subst hcs
        exact ⟨by simp, by simp, by simp⟩
    | cons e rest ih =>
        intro Cs hrun hd hb
        cases e with
        | ded t =>
            have hrun' : ProtSat.Reference.run P C
                (ProtSat.Reference.Ev.ded t :: rest) = some Cs :=
              hrun
            cases hstep : ProtSat.Reference.stepOf P C (ProtSat.Reference.Ev.ded t) with
            | none => simp [ProtSat.Reference.Runs, ProtSat.Reference.run, hstep] at hrun'
            | some C' =>
                obtain ⟨Rest, hcs, hRest⟩ := run_cons hstep hrun'
                subst hcs
                obtain ⟨hnew, hrest⟩ := newDeds_inv hd
                have hrel : ProtSat.Reference.Rel P C (ProtSat.Reference.Ev.ded t) C' := hstep
                unfold ProtSat.Reference.Rel at hrel
                rw [ProtSat.Reference.stepOf] at hrel
                by_cases hb' : oneStepBool C.kn t
                · rw [if_pos hb'] at hrel
                  obtain rfl : C' = ProtSat.Reference.publish C t := (Option.some.inj hrel).symm
                  have hih := ih (ProtSat.Reference.publish C t) Rest hRest hrest
                    (fun D hD => hb D (List.Mem.tail _ hD))
                  obtain ⟨L2, hL⟩ := run_nonempty hRest
                  have hmem2 : ProtSat.Reference.publish C t ∈ C :: Rest := by
                    rw [hL]
                    exact List.Mem.tail C (List.Mem.head L2)
                  have hkt : t ∈ (ProtSat.Reference.publish C t).kn := by
                    rw [ProtSat.Reference.publish_kn]
                    simp
                  have hut : t ∈ Bounded.univ P B :=
                    (hb (ProtSat.Reference.publish C t) hmem2).1 t hkt
                  have htnot : t ∉ rest.map dedMsg := hih.2.2 t hkt
                  refine ⟨List.Nodup.cons htnot hih.1, ?_, ?_⟩
                  · intro q hq
                    rw [List.mem_map] at hq
                    obtain ⟨x, hx, hqx⟩ := hq
                    cases hx with
                    | head _ => exact hqx ▸ hut
                    | tail _ hmem => exact hih.2.1 q (List.mem_map.mpr ⟨x, hmem, hqx⟩)
                  · intro s hs hor
                    simp only [List.map_cons, List.mem_cons] at hor
                    obtain (heq | hmem) := hor
                    · rw [heq] at hs
                      exact hnew hs
                    · exact hih.2.2 s (List.mem_append.mpr (Or.inl hs)) hmem
                · rw [if_neg hb'] at hrel
                  exact absurd hrel (by simp)
        | idle => cases hd
        | recv s m => cases hd
        | generate s n => cases hd
        | act s => cases hd
  obtain ⟨hnodup, hmem, _hkn⟩ := hmain (ProtSat.Reference.initCfg P) tr Cs hrun hd hb
  have huniv : (tr.map dedMsg).length = tr.length := by rw [List.length_map]
  have hle := List.length_le_of_nodup_forall_mem (Bounded.univ P B) (univ_nodup P B)
    (tr.map dedMsg) hnodup hmem
  omega

/-! ### T3: extensional equality of configurations, and removal of redundant events -/

/-- **Extensional equality of configurations.** The knowledge, the allocation history and the
secret obligations are *lists*, so the same information can be recorded with redundant copies, and
an attacker step that deduces a message the attacker already holds really does change the
configuration - it appends another copy. Two configurations are extensionally equal when their
session vectors, allocation histories and obligation histories agree exactly and their knowledge
agrees as a set. Every predicate the contract reads from a configuration, and the step relation
itself, only look at membership, so this is a congruence: that is what makes compression
possible. -/
def CfgEq (C D : RCfg) : Prop :=
  C.sess = D.sess ∧ C.alloc = D.alloc ∧ C.oblig = D.oblig ∧ (∀ t, t ∈ C.kn ↔ t ∈ D.kn)

/-- Extensional equality is reflexive. -/
theorem cfgEq_refl (C : RCfg) : CfgEq C C :=
  ⟨rfl, rfl, rfl, fun _ => Iff.rfl⟩

/-- Extensional equality is symmetric. -/
theorem cfgEq_symm {C D : RCfg} (h : CfgEq C D) : CfgEq D C :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun t => (h.2.2.2 t).symm⟩

/-- Extensional equality is transitive. -/
theorem cfgEq_trans {C D E : RCfg} (h1 : CfgEq C D) (h2 : CfgEq D E) : CfgEq C E :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
    fun t => Iff.trans (h1.2.2.2 t) (h2.2.2.2 t)⟩

/-- Membership in a list with one element appended. -/
theorem mem_append_one {α : Type} [DecidableEq α] {l : List α} {a b : α} :
    a ∈ l ++ [b] ↔ a ∈ l ∨ a = b := by
  rw [List.mem_append, List.mem_singleton]

/-- Appending a message the attacker already knows changes nothing extensionally. -/
theorem cfgEq_publish_self {C : RCfg} {t : Term} (h : t ∈ C.kn) :
    CfgEq C (ProtSat.Reference.publish C t) := by
  refine ⟨rfl, rfl, rfl, fun x => ?_⟩
  rw [ProtSat.Reference.publish_kn, mem_append_one]
  exact ⟨Or.inl, fun hx => hx.elim id (fun hy => hy.symm ▸ h)⟩

/-- Publishing is compatible with extensional equality. -/
theorem cfgEq_publish {C D : RCfg} (h : CfgEq C D) (t : Term) :
    CfgEq (ProtSat.Reference.publish C t) (ProtSat.Reference.publish D t) := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x => ?_⟩
  rw [ProtSat.Reference.publish_kn, ProtSat.Reference.publish_kn, mem_append_one,
    mem_append_one]
  exact ⟨fun hx => hx.imp (fun y => (h.2.2.2 x).mp y) id,
    fun hx => hx.imp (fun y => (h.2.2.2 x).mpr y) id⟩

/-- Recording an allocation is compatible with extensional equality. -/
theorem cfgEq_allocate {C D : RCfg} (h : CfgEq C D) (n : NonceName) :
    CfgEq (ProtSat.Reference.allocate C n) (ProtSat.Reference.allocate D n) := by
  refine ⟨h.1, by rw [ProtSat.Reference.allocate_alloc, ProtSat.Reference.allocate_alloc, h.2.1],
    h.2.2.1, fun x => ?_⟩
  exact h.2.2.2 x

/-- Declaring a secret obligation is compatible with extensional equality. -/
theorem cfgEq_declareObl {C D : RCfg} (h : CfgEq C D) (v : Term) :
    CfgEq (ProtSat.Reference.declareObl C v) (ProtSat.Reference.declareObl D v) := by
  refine ⟨h.1, h.2.1,
    by rw [ProtSat.Reference.declareObl_oblig, ProtSat.Reference.declareObl_oblig, h.2.2.1],
    fun x => ?_⟩
  exact h.2.2.2 x

/-- Updating one session is compatible with extensional equality. -/
theorem cfgEq_mapSess {C D : RCfg} (h : CfgEq C D) (f : SessState -> SessState) (q : Nat) :
    CfgEq (ProtSat.Reference.mapSess f C q) (ProtSat.Reference.mapSess f D q) := by
  refine ⟨by unfold ProtSat.Reference.mapSess; rw [h.1], h.2.1, h.2.2.1, fun x => ?_⟩
  exact h.2.2.2 x

/-- The store of a session is a property of the extensional configuration. -/
theorem storeOf_congr {C D : RCfg} (h : CfgEq C D) (q : Nat) :
    ProtSat.Reference.storeOf C q = ProtSat.Reference.storeOf D q := by
  unfold ProtSat.Reference.storeOf ProtSat.Reference.sessAt
  rw [h.1]

/-- The one-step deduction test reads the knowledge base only through membership. -/
theorem oneStepBool_congr {K K' : List Term} (h : ∀ t, t ∈ K ↔ t ∈ K') (t : Term) :
    oneStepBool K t = oneStepBool K' t := by
  classical
  rw [Bool.eq_iff_iff, ProtSat.oneStepBool_iff, ProtSat.oneStepBool_iff]
  exact ⟨oneStep_mono (fun x hx => (h x).mp hx), oneStep_mono (fun x hx => (h x).mpr hx)⟩

/-- Extensionally equal configurations hold the same keys, so the same expressions are usable. -/
theorem availableKeys_congr {P : Protocol} {C D : RCfg} (h : CfgEq C D) (q : Nat) :
    ProtSat.Reference.availableKeys P C q = ProtSat.Reference.availableKeys P D q := by
  unfold ProtSat.Reference.availableKeys
  rw [← storeOf_congr h q]

/-- Whether an action is enabled is a property of the extensional configuration. -/
theorem actionUsable_congr {P : Protocol} {C D : RCfg} (h : CfgEq C D) (q : Nat) (act : Action) :
    ProtSat.Reference.actionUsable P C q act = ProtSat.Reference.actionUsable P D q act := by
  unfold ProtSat.Reference.actionUsable ProtSat.Reference.canUse
  refine List.all_congr rfl (fun e => ?_)
  unfold ProtSat.Reference.requiredPrivKeys
  rw [availableKeys_congr h q]

/-- The authentication annotation of a step depends only on the extensional configuration. -/
theorem authData_congr {P : Protocol} {C D : RCfg} (h : CfgEq C D) (q : Nat) (peer v : Expr) :
    ProtSat.Reference.authData P C q peer v = ProtSat.Reference.authData P D q peer v := by
  unfold ProtSat.Reference.authData
  rw [← storeOf_congr h q]

/-- **A deterministic action respects extensional equality.** -/
theorem actStep_pres {P : Protocol} {C D : RCfg} {q : Nat} {act : Action} {C' : RCfg}
    (h : CfgEq C D) (hs : ProtSat.Reference.actStep P C q act = some C') :
    ∃ D', ProtSat.Reference.actStep P D q act = some D' ∧ CfgEq C' D' := by
  cases act with
  | fresh _ _ => simp [ProtSat.Reference.actStep] at hs
  | recv _ _ => simp [ProtSat.Reference.actStep] at hs
  | send _ e =>
      cases he : Expr.eval e (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he] at hs
      | some t =>
          simp [ProtSat.Reference.actStep, he] at hs
          subst hs
          have he' : Expr.eval e (ProtSat.Reference.storeOf D q) = some t := by
            rw [← storeOf_congr h q]
            exact he
          exact ⟨ProtSat.Reference.publish (ProtSat.Reference.mapSess ProtSat.bump D q) t,
            by simp [ProtSat.Reference.actStep, he'], cfgEq_publish (cfgEq_mapSess h _ q) t⟩
  | assign x e =>
      cases he : Expr.eval e (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he] at hs
      | some t =>
          simp [ProtSat.Reference.actStep, he] at hs
          subst hs
          have he' : Expr.eval e (ProtSat.Reference.storeOf D q) = some t := by
            rw [← storeOf_congr h q]
            exact he
          exact ⟨ProtSat.Reference.mapSess (ProtSat.bumpStore x t) D q,
            by simp [ProtSat.Reference.actStep, he'], cfgEq_mapSess h _ q⟩
  | check e1 e2 =>
      cases he1 : Expr.eval e1 (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he1] at hs
      | some v1 =>
          cases he2 : Expr.eval e2 (ProtSat.Reference.storeOf C q) with
          | none => simp [ProtSat.Reference.actStep, he1, he2] at hs
          | some v2 =>
              by_cases hv : v1 == v2
              · simp [ProtSat.Reference.actStep, he1, he2, hv] at hs
                subst hs
                have h1 : Expr.eval e1 (ProtSat.Reference.storeOf D q) = some v1 := by
                  rw [← storeOf_congr h q]
                  exact he1
                have h2 : Expr.eval e2 (ProtSat.Reference.storeOf D q) = some v2 := by
                  rw [← storeOf_congr h q]
                  exact he2
                exact ⟨ProtSat.Reference.mapSess ProtSat.bump D q,
                  by simp [ProtSat.Reference.actStep, h1, h2, hv], cfgEq_mapSess h _ q⟩
              · simp [ProtSat.Reference.actStep, he1, he2, hv] at hs
  | secret e =>
      cases he : Expr.eval e (ProtSat.Reference.storeOf C q) with
      | none => simp [ProtSat.Reference.actStep, he] at hs
      | some t =>
          simp [ProtSat.Reference.actStep, he] at hs
          subst hs
          have he' : Expr.eval e (ProtSat.Reference.storeOf D q) = some t := by
            rw [← storeOf_congr h q]
            exact he
          exact ⟨ProtSat.Reference.declareObl (ProtSat.Reference.mapSess ProtSat.bump D q) t,
            by simp [ProtSat.Reference.actStep, he'],
            cfgEq_declareObl (cfgEq_mapSess h _ q) t⟩
  | claim tag peer v =>
      by_cases hd : (ProtSat.Reference.authData P C q peer v).isSome
      · simp [ProtSat.Reference.actStep, hd] at hs
        subst hs
        have hd' : (ProtSat.Reference.authData P D q peer v).isSome := by
          rw [← authData_congr h q peer v]
          exact hd
        exact ⟨ProtSat.Reference.mapSess ProtSat.bump D q,
          by simp [ProtSat.Reference.actStep, hd'], cfgEq_mapSess h _ q⟩
      · simp [ProtSat.Reference.actStep, hd] at hs
  | commit tag peer v =>
      by_cases hd : (ProtSat.Reference.authData P C q peer v).isSome
      · simp [ProtSat.Reference.actStep, hd] at hs
        subst hs
        have hd' : (ProtSat.Reference.authData P D q peer v).isSome := by
          rw [← authData_congr h q peer v]
          exact hd
        exact ⟨ProtSat.Reference.mapSess ProtSat.bump D q,
          by simp [ProtSat.Reference.actStep, hd'], cfgEq_mapSess h _ q⟩
      · simp [ProtSat.Reference.actStep, hd] at hs

/-- **The step relation respects extensional equality.** If `C` and `D` hold the same information
and `C` takes one step, then `D` takes the same step and the successors again hold the same
information. This is the congruence that lets redundant events be removed. -/
theorem stepOf_pres {P : Protocol} {C D : RCfg} {e : ProtSat.Reference.Ev} {C' : RCfg}
    (h : CfgEq C D) (hstep : ProtSat.Reference.stepOf P C e = some C') :
    ∃ D', ProtSat.Reference.stepOf P D e = some D' ∧ CfgEq C' D' := by
  cases e
  · simp [ProtSat.Reference.stepOf] at hstep
    subst hstep
    exact ⟨D, by simp [ProtSat.Reference.stepOf], h⟩
  · rename_i t
    by_cases hb : oneStepBool C.kn t
    · simp [ProtSat.Reference.stepOf, hb] at hstep
      subst hstep
      have hbD : oneStepBool D.kn t := by
        rw [← oneStepBool_congr (h.2.2.2) t]
        exact hb
      exact ⟨ProtSat.Reference.publish D t, by simp [ProtSat.Reference.stepOf, hbD],
        cfgEq_publish h t⟩
    · simp [ProtSat.Reference.stepOf, hb] at hstep
  · rename_i q m
    have hpceq : ProtSat.Reference.pcOf C q = ProtSat.Reference.pcOf D q :=
      pcOf_congr_sess h.1 q
    cases hact : P.actionAt q (ProtSat.Reference.pcOf C q) with
    | none => simp [ProtSat.Reference.stepOf, hact] at hstep
    | some act =>
        cases act with
        | recv av xv =>
            by_cases hm : m ∈ C.kn
            · simp [ProtSat.Reference.stepOf, hact, hm] at hstep
              subst hstep
              have hmD : m ∈ D.kn := (h.2.2.2 m).mp hm
              have hactD : P.actionAt q (ProtSat.Reference.pcOf D q) =
                some (Action.recv av xv) := by rw [← hpceq]; exact hact
              exact ⟨ProtSat.Reference.mapSess (ProtSat.bumpStore xv m) D q,
                by simp [ProtSat.Reference.stepOf, hactD, hmD], cfgEq_mapSess h _ q⟩
            · simp [ProtSat.Reference.stepOf, hact, hm] at hstep
        | _ => simp [ProtSat.Reference.stepOf, hact] at hstep
  · rename_i q n
    have hpceq : ProtSat.Reference.pcOf C q = ProtSat.Reference.pcOf D q :=
      pcOf_congr_sess h.1 q
    cases hact : P.actionAt q (ProtSat.Reference.pcOf C q) with
    | none => simp [ProtSat.Reference.stepOf, hact] at hstep
    | some act =>
        cases act with
        | fresh xv Nv =>
            by_cases hdom : n ∈ P.nonceDomain
            · by_cases hn : n ∈ C.alloc
              · simp [ProtSat.Reference.stepOf, hact, hdom, hn] at hstep
              · simp [ProtSat.Reference.stepOf, hact, hdom, hn] at hstep
                subst hstep
                have hnD : n ∉ D.alloc := fun hx => hn (by rw [h.2.1]; exact hx)
                have hactD : P.actionAt q (ProtSat.Reference.pcOf D q) =
                  some (Action.fresh xv Nv) := by rw [← hpceq]; exact hact
                exact ⟨ProtSat.Reference.allocate
                    (ProtSat.Reference.mapSess (ProtSat.bumpStore xv (Term.nonce n)) D q) n,
                  by simp [ProtSat.Reference.stepOf, hactD, hdom, hnD],
                  cfgEq_allocate (cfgEq_mapSess h _ q) n⟩
            · simp [ProtSat.Reference.stepOf, hact, hdom] at hstep
        | _ => simp [ProtSat.Reference.stepOf, hact] at hstep
  · rename_i q
    have hpceq : ProtSat.Reference.pcOf C q = ProtSat.Reference.pcOf D q :=
      pcOf_congr_sess h.1 q
    cases hact : P.actionAt q (ProtSat.Reference.pcOf C q) with
    | none => simp [ProtSat.Reference.stepOf, hact] at hstep
    | some act =>
        by_cases hu : ProtSat.Reference.actionUsable P C q act
        · simp [ProtSat.Reference.stepOf, hact, hu] at hstep
          have huD : ProtSat.Reference.actionUsable P D q act = true := by
            rw [← actionUsable_congr h q act]
            exact hu
          have hactD : P.actionAt q (ProtSat.Reference.pcOf D q) = some act := by
            rw [← hpceq]
            exact hact
          obtain ⟨D', hD', hcd⟩ := actStep_pres h hstep
          have hstepD : ProtSat.Reference.stepOf P D (ProtSat.Reference.Ev.act q) = some D' := by
            rw [ProtSat.Reference.stepOf, hactD]
            simp only [huD, reduceIte]
            exact hD'
          exact ⟨D', hstepD, hcd⟩
        · simp [ProtSat.Reference.stepOf, hact, hu] at hstep

/-- Leaking is a property of the extensional configuration. -/
theorem leaks_congr {P : Protocol} {C D : RCfg} (h : CfgEq C D) :
    ProtSat.Reference.leaks P C ↔ ProtSat.Reference.leaks P D := by
  unfold ProtSat.Reference.leaks ProtSat.Reference.declaredSecrets
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, hk⟩
    rw [List.mem_append] at hs
    obtain h1 | h2 := hs
    · exact ⟨s, List.mem_append_left _ h1, (h.2.2.2 s).mp hk⟩
    · rw [← h.2.2.1]
      exact ⟨s, List.mem_append_right _ h2, (h.2.2.2 s).mp hk⟩
  · rintro ⟨s, hs, hk⟩
    rw [List.mem_append] at hs
    obtain h1 | h2 := hs
    · exact ⟨s, List.mem_append_left _ h1, (h.2.2.2 s).mpr hk⟩
    · rw [h.2.2.1]
      exact ⟨s, List.mem_append_right _ h2, (h.2.2.2 s).mpr hk⟩

/-- Being inside the public bounds is a property of the extensional configuration. -/
theorem inBounds_congr {P : Protocol} {B : Bounded.Bounds} {C D : RCfg} (h : CfgEq C D) :
    inBounds P B C ↔ inBounds P B D := by
  unfold inBounds
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun t ht => h1 t (by rwa [h.2.2.2 t]), fun v hv => h2 v (by rwa [h.2.2.1]),
      fun s hs p hp => h3 s (by rwa [h.1]) p hp, fun n hn => h4 n (by rwa [h.2.1])⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun t ht => h1 t (by rwa [← h.2.2.2 t]),
      fun v hv => h2 v (by rwa [← h.2.2.1]),
      fun s hs p hp => h3 s (by rwa [← h.1]) p hp, fun n hn => h4 n (by rwa [← h.2.1])⟩

/-- The start configuration of a run is among the configurations it visits. -/
theorem runs_head_mem {P : Protocol} {C : RCfg} {tr : List ProtSat.Reference.Ev} {Cs : List RCfg}
    (h : ProtSat.Reference.Runs P C tr Cs) : C ∈ Cs := by
  obtain ⟨L2, hL⟩ := run_nonempty h
  rw [hL]
  exact List.Mem.head _

/-- **The redundant events of a trace.** `dropRedundant tr added` deletes every idle event, and
every deduction whose message the accumulator already contains - the accumulator being the set of
messages the attacker is already committed to knowing. `dedAdded tr added` is what the accumulator
becomes, so its growth counts the deductions that survive. -/
def dropRedundant : List ProtSat.Reference.Ev -> List Term -> List ProtSat.Reference.Ev
  | [], added => []
  | ProtSat.Reference.Ev.idle :: tr, added => dropRedundant tr added
  | ProtSat.Reference.Ev.ded t :: tr, added =>
      if t ∈ added then dropRedundant tr added
      else ProtSat.Reference.Ev.ded t :: dropRedundant tr (t :: added)
  | e :: tr, added => e :: dropRedundant tr added

/-- The accumulator after dropping redundant events: the messages the kept deductions add. -/
def dedAdded : List ProtSat.Reference.Ev -> List Term -> List Term
  | [], added => added
  | ProtSat.Reference.Ev.ded t :: tr, added =>
      if t ∈ added then dedAdded tr added else dedAdded tr (t :: added)
  | _ :: tr, added => dedAdded tr added

/-- The defining equations of the two compressions, stated so that the match reduces. -/
@[simp] theorem dropRedundant_nil (added : List Term) :
    dropRedundant [] added = [] := rfl

/-- An idle event is dropped. -/
@[simp] theorem dropRedundant_idle (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dropRedundant (ProtSat.Reference.Ev.idle :: tr) added = dropRedundant tr added := rfl

/-- A deduction is dropped exactly when its message is already in the accumulator. -/
theorem dropRedundant_ded (tr : List ProtSat.Reference.Ev) (added : List Term) (t : Term) :
    dropRedundant (ProtSat.Reference.Ev.ded t :: tr) added =
      if t ∈ added then dropRedundant tr added
      else ProtSat.Reference.Ev.ded t :: dropRedundant tr (t :: added) := rfl

/-- A delivery is kept. -/
@[simp] theorem dropRedundant_recv (q : Nat) (m : Term)
    (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dropRedundant (ProtSat.Reference.Ev.recv q m :: tr) added =
      ProtSat.Reference.Ev.recv q m :: dropRedundant tr added := rfl

/-- A generation is kept. -/
@[simp] theorem dropRedundant_generate (q : Nat) (n : NonceName)
    (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dropRedundant (ProtSat.Reference.Ev.generate q n :: tr) added =
      ProtSat.Reference.Ev.generate q n :: dropRedundant tr added := rfl

/-- A deterministic action is kept. -/
@[simp] theorem dropRedundant_act (q : Nat) (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dropRedundant (ProtSat.Reference.Ev.act q :: tr) added =
      ProtSat.Reference.Ev.act q :: dropRedundant tr added := rfl

@[simp] theorem dedAdded_nil (added : List Term) : dedAdded [] added = added := rfl

/-- A deduction adds its message to the accumulator exactly when it survives. -/
theorem dedAdded_ded (tr : List ProtSat.Reference.Ev) (added : List Term) (t : Term) :
    dedAdded (ProtSat.Reference.Ev.ded t :: tr) added =
      if t ∈ added then dedAdded tr added else dedAdded tr (t :: added) := rfl

/-- An idle event does not change the accumulator. -/
@[simp] theorem dedAdded_idle (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dedAdded (ProtSat.Reference.Ev.idle :: tr) added = dedAdded tr added := rfl

/-- A delivery does not change the accumulator. -/
@[simp] theorem dedAdded_recv (q : Nat) (m : Term) (tr : List ProtSat.Reference.Ev)
    (added : List Term) : dedAdded (ProtSat.Reference.Ev.recv q m :: tr) added =
      dedAdded tr added := rfl

/-- A generation does not change the accumulator. -/
@[simp] theorem dedAdded_generate (q : Nat) (n : NonceName)
    (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dedAdded (ProtSat.Reference.Ev.generate q n :: tr) added = dedAdded tr added := rfl

/-- A deterministic action does not change the accumulator. -/
@[simp] theorem dedAdded_act (q : Nat) (tr : List ProtSat.Reference.Ev) (added : List Term) :
    dedAdded (ProtSat.Reference.Ev.act q :: tr) added = dedAdded tr added := rfl

/-- The messages a compressed trace deduces are pairwise distinct, if the accumulator was. -/
theorem nodup_dedAdded : ∀ (tr : List ProtSat.Reference.Ev) (added : List Term),
    added.Nodup -> (dedAdded tr added).Nodup := by
  intro tr
  induction tr with
  | nil => intro added hn; exact hn
  | cons e rest ih =>
      intro added hn
      cases e with
      | ded t =>
          by_cases hb : t ∈ added
          · rw [dedAdded_ded, if_pos hb]
            exact ih added hn
          · rw [dedAdded_ded, if_neg hb]
            exact ih (t :: added) (List.Nodup.cons hb hn)
      | idle => exact ih added hn
      | recv q m => exact ih added hn
      | generate q n => exact ih added hn
      | act q => exact ih added hn

/-- Dropping redundant events never drops a session event. -/
theorem filter_isSessEv_dropRedundant (tr : List ProtSat.Reference.Ev) (added : List Term) :
    (dropRedundant tr added).filter (fun e => isSessEv e = true) =
      tr.filter (fun e => isSessEv e = true) := by
  induction tr generalizing added with
  | nil => rfl
  | cons e rest ih =>
      cases e with
      | idle => exact ih added
      | ded t =>
          by_cases hb : t ∈ added
          · rw [dropRedundant_ded, if_pos hb, List.filter_cons_of_neg (by simp [isSessEv])]
            exact ih added
          · rw [dropRedundant_ded, if_neg hb, List.filter_cons_of_neg (by simp [isSessEv])]
            exact ih (t :: added)
      | recv q m =>
          rw [dropRedundant_recv]
          rw [List.filter_cons_of_pos (by simp [isSessEv])]
          exact congrArg (fun l => ProtSat.Reference.Ev.recv q m :: l) (ih added)
      | generate q n =>
          rw [dropRedundant_generate]
          rw [List.filter_cons_of_pos (by simp [isSessEv])]
          exact congrArg (fun l => ProtSat.Reference.Ev.generate q n :: l) (ih added)
      | act q =>
          rw [dropRedundant_act]
          rw [List.filter_cons_of_pos (by simp [isSessEv])]
          exact congrArg (fun l => ProtSat.Reference.Ev.act q :: l) (ih added)

/-- The length of the compressed trace is at most the number of deductions it keeps plus the number
of session events it keeps. -/
theorem length_dropRedundant (tr : List ProtSat.Reference.Ev) (added : List Term) :
    (dropRedundant tr added).length + added.length ≤
      (dedAdded tr added).length + (tr.filter (fun e => isSessEv e = true)).length := by
  induction tr generalizing added with
  | nil => simp
  | cons e rest ih =>
      cases e with
      | idle => exact ih added
      | ded t =>
          by_cases hb : t ∈ added
          · rw [dropRedundant_ded, dedAdded_ded, if_pos hb, if_pos hb]
            rw [List.filter_cons_of_neg (by simp [isSessEv])]
            exact ih added
          · rw [dropRedundant_ded, dedAdded_ded, if_neg hb, if_neg hb]
            rw [List.filter_cons_of_neg (by simp [isSessEv])]
            simp only [List.length_cons]
            have h := ih (t :: added)
            simp only [List.length_cons] at h
            omega
      | recv q m =>
          rw [dropRedundant_recv, dedAdded_recv]
          rw [List.filter_cons_of_pos (by simp [isSessEv])]
          simp only [List.length_cons]
          have h := ih added
          omega
      | generate q n =>
          rw [dropRedundant_generate, dedAdded_generate]
          rw [List.filter_cons_of_pos (by simp [isSessEv])]
          simp only [List.length_cons]
          have h := ih added
          omega
      | act q =>
          rw [dropRedundant_act, dedAdded_act]
          rw [List.filter_cons_of_pos (by simp [isSessEv])]
          simp only [List.length_cons]
          have h := ih added
          omega

/-- **T3: redundant events can be removed from a run.** Given a run of `tr` from `C`, and a
configuration `C₀` extensionally equal to `C` whose knowledge already contains the accumulator,
there is a run of the compressed trace from `C₀` whose configurations correspond extensionally to
the ones the original run visited, in both directions. Removal is *not* literal: a deduction of a
message already known changes the configuration by appending a copy, which is exactly why the
statement is made up to `CfgEq`. Every message the compressed trace still deduces is either already
in the accumulator or in the knowledge of a configuration the compressed run visits. -/
theorem runs_dropRedundant {P : Protocol} {C₀ C : RCfg} {tr : List ProtSat.Reference.Ev}
    {added : List Term} (h₀ : CfgEq C₀ C) (hadd : ∀ t ∈ added, t ∈ C.kn)
    (h₀add : ∀ t ∈ added, t ∈ C₀.kn) :
    ∀ (Cs : List RCfg), ProtSat.Reference.Runs P C tr Cs →
      ∃ (Cs' : List RCfg), ProtSat.Reference.Runs P C₀ (dropRedundant tr added) Cs' ∧
        (∀ C' ∈ Cs', ∃ C'' ∈ Cs, CfgEq C' C'') ∧ (∀ C'' ∈ Cs, ∃ C' ∈ Cs', CfgEq C' C'') ∧
        (∀ t ∈ dedAdded tr added, t ∈ added ∨ ∃ C' ∈ Cs', t ∈ C'.kn) := by
  intro Cs hrun
  induction tr generalizing C Cs C₀ added with
  | nil =>
      have hcs := runs_nil_inv hrun
      subst hcs
      refine ⟨[C₀], ProtSat.Reference.runs_nil P C₀, ?_, ?_, ?_⟩
      · intro D hD
        rw [List.mem_singleton] at hD
        subst hD
        exact ⟨C, List.Mem.head _, h₀⟩
      · intro D hD
        rw [List.mem_singleton] at hD
        subst hD
        exact ⟨C₀, List.Mem.head _, h₀⟩
      · intro t ht
        exact Or.inl ht
  | cons e rest ih =>
      cases hstep : ProtSat.Reference.stepOf P C e with
      | none =>
          have h2 : ProtSat.Reference.run P C (e :: rest) = none := by
            rw [ProtSat.Reference.run, hstep]
          have h3 : ProtSat.Reference.run P C (e :: rest) = some Cs := hrun
          exact absurd (h2.symm.trans h3) (by simp)
      | some C' =>
          obtain ⟨Rest, hcs, hRest⟩ := run_cons hstep hrun
          subst hcs
          have hrel : ProtSat.Reference.Rel P C e C' := hstep
          cases e with
          | idle =>
              have hc' : C' = C := by
                have hsid : ProtSat.Reference.stepOf P C
                    ProtSat.Reference.Ev.idle = some C' := hstep
                simp [ProtSat.Reference.stepOf] at hsid
                exact hsid.symm
              subst hc'
              rw [dropRedundant_idle, dedAdded_idle]
              obtain ⟨Cs', hrun', hcov, hcov', hded⟩ := ih h₀ hadd h₀add Rest hRest
              refine ⟨Cs', hrun', ?_, ?_, hded⟩
              · intro D hD
                obtain ⟨F, hF, hfd⟩ := hcov D hD
                exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C₀, runs_head_mem hrun', h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov' D h2
                  exact ⟨F, hF, hfd⟩
          | ded t =>
              by_cases hb : oneStepBool C.kn t
              · simp [ProtSat.Reference.stepOf, hb] at hstep
                subst hstep
                by_cases hin : t ∈ added
                · rw [dropRedundant_ded, dedAdded_ded, if_pos hin, if_pos hin]
                  have h₀' : CfgEq C₀ (ProtSat.Reference.publish C t) :=
                    cfgEq_trans h₀ (cfgEq_publish_self (hadd t hin))
                  obtain ⟨Cs', hrun', hcov, hcov', hded⟩ :=
                    ih (C := ProtSat.Reference.publish C t) h₀'
                      (fun x hx => List.mem_append_left _ (hadd x hx)) h₀add Rest hRest
                  refine ⟨Cs', hrun', ?_, ?_, hded⟩
                  · intro D hD
                    obtain ⟨F, hF, hfd⟩ := hcov D hD
                    exact ⟨F, List.Mem.tail _ hF, hfd⟩
                  · intro D hD
                    rw [List.mem_cons] at hD
                    obtain h1 | h2 := hD
                    · subst h1
                      exact ⟨C₀, runs_head_mem hrun', h₀⟩
                    · obtain ⟨F, hF, hfd⟩ := hcov' D h2
                      exact ⟨F, hF, hfd⟩
                · have hbD : oneStepBool C₀.kn t := by
                      rw [oneStepBool_congr (h₀.2.2.2) t]
                      exact hb
                  have hstepD :
                      ProtSat.Reference.Rel P C₀ (ProtSat.Reference.Ev.ded t)
                        (ProtSat.Reference.publish C₀ t) := by
                    simp [ProtSat.Reference.Rel, ProtSat.Reference.stepOf, hbD]
                  rw [dropRedundant_ded, dedAdded_ded, if_neg hin, if_neg hin]
                  obtain ⟨Cs', hrun', hcov, hcov', hded⟩ :=
                    ih (C := ProtSat.Reference.publish C t)
                      (C₀ := ProtSat.Reference.publish C₀ t) (added := t :: added)
                      (cfgEq_publish h₀ t)
                      (fun x hx => by
                        rw [List.mem_cons] at hx
                        obtain heq | h3 := hx
                        · subst heq
                          rw [ProtSat.Reference.publish_kn]
                          exact List.mem_append_right _ (List.Mem.head _)
                        · rw [ProtSat.Reference.publish_kn]
                          exact List.mem_append_left _ (hadd x h3))
                      (fun x hx => by
                        rw [List.mem_cons] at hx
                        obtain heq | h3 := hx
                        · subst heq
                          rw [ProtSat.Reference.publish_kn]
                          exact List.mem_append_right _ (List.Mem.head _)
                        · rw [ProtSat.Reference.publish_kn]
                          exact List.mem_append_left _ (h₀add x h3)) Rest hRest
                  have hrun'' : ProtSat.Reference.Runs P C₀
                      (ProtSat.Reference.Ev.ded t :: dropRedundant rest (t :: added))
                      (C₀ :: Cs') := ProtSat.Reference.runs_cons hstepD hrun'
                  refine ⟨C₀ :: Cs', hrun'', ?_, ?_, ?_⟩
                  · intro D hD
                    rw [List.mem_cons] at hD
                    obtain h1 | h2 := hD
                    · subst h1
                      exact ⟨C, List.Mem.head _, h₀⟩
                    · obtain ⟨F, hF, hfd⟩ := hcov D h2
                      exact ⟨F, List.Mem.tail _ hF, hfd⟩
                  · intro D hD
                    rw [List.mem_cons] at hD
                    obtain h1 | h2 := hD
                    · subst h1
                      exact ⟨C₀, List.Mem.head _, h₀⟩
                    · obtain ⟨F, hF, hfd⟩ := hcov' D h2
                      exact ⟨F, List.Mem.tail _ hF, hfd⟩
                  · intro x hx
                    obtain h1 | h2 := hded x hx
                    · rw [List.mem_cons] at h1
                      obtain heq | h3 := h1
                      · have hkt : x ∈ (ProtSat.Reference.publish C₀ t).kn := by
                          rw [ProtSat.Reference.publish_kn, ← heq]
                          exact List.mem_append_right _ (List.Mem.head _)
                        have hmem : ProtSat.Reference.publish C₀ t ∈ Cs' :=
                          runs_head_mem hrun'
                        exact Or.inr ⟨ProtSat.Reference.publish C₀ t, List.Mem.tail _ hmem, hkt⟩
                      · exact Or.inl h3
                    · obtain ⟨F, hF, hde⟩ := h2
                      exact Or.inr ⟨F, List.Mem.tail _ hF, hde⟩
              · simp [ProtSat.Reference.stepOf, hb] at hstep
          | recv q m =>
              obtain ⟨D₀, hstep₀, hcd⟩ := stepOf_pres (cfgEq_symm h₀) hstep
              rw [dropRedundant_recv, dedAdded_recv]
              obtain ⟨Cs', hrun', hcov, hcov', hded⟩ :=
                ih (C := C') (C₀ := D₀) (cfgEq_symm hcd)
                  (fun x hx => ProtSat.Reference.kn_mono hrel x (hadd x hx))
                  (fun x hx => ProtSat.Reference.kn_mono hstep₀ x (h₀add x hx)) Rest hRest
              have hrun'' : ProtSat.Reference.Runs P C₀
                  (ProtSat.Reference.Ev.recv q m :: dropRedundant rest added) (C₀ :: Cs') :=
                ProtSat.Reference.runs_cons hstep₀ hrun'
              refine ⟨C₀ :: Cs', hrun'', ?_, ?_, ?_⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C, List.Mem.head _, h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov D h2
                  exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C₀, List.Mem.head _, h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov' D h2
                  exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro x hx
                obtain h1 | h2 := hded x hx
                · exact Or.inl h1
                · obtain ⟨F, hF, hde⟩ := h2
                  exact Or.inr ⟨F, List.Mem.tail _ hF, hde⟩
          | generate q n =>
              obtain ⟨D₀, hstep₀, hcd⟩ := stepOf_pres (cfgEq_symm h₀) hstep
              rw [dropRedundant_generate, dedAdded_generate]
              obtain ⟨Cs', hrun', hcov, hcov', hded⟩ :=
                ih (C := C') (C₀ := D₀) (cfgEq_symm hcd)
                  (fun x hx => ProtSat.Reference.kn_mono hrel x (hadd x hx))
                  (fun x hx => ProtSat.Reference.kn_mono hstep₀ x (h₀add x hx)) Rest hRest
              have hrun'' : ProtSat.Reference.Runs P C₀
                  (ProtSat.Reference.Ev.generate q n :: dropRedundant rest added) (C₀ :: Cs') :=
                ProtSat.Reference.runs_cons hstep₀ hrun'
              refine ⟨C₀ :: Cs', hrun'', ?_, ?_, ?_⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C, List.Mem.head _, h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov D h2
                  exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C₀, List.Mem.head _, h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov' D h2
                  exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro x hx
                obtain h1 | h2 := hded x hx
                · exact Or.inl h1
                · obtain ⟨F, hF, hde⟩ := h2
                  exact Or.inr ⟨F, List.Mem.tail _ hF, hde⟩
          | act q =>
              obtain ⟨D₀, hstep₀, hcd⟩ := stepOf_pres (cfgEq_symm h₀) hstep
              rw [dropRedundant_act, dedAdded_act]
              obtain ⟨Cs', hrun', hcov, hcov', hded⟩ :=
                ih (C := C') (C₀ := D₀) (cfgEq_symm hcd)
                  (fun x hx => ProtSat.Reference.kn_mono hrel x (hadd x hx))
                  (fun x hx => ProtSat.Reference.kn_mono hstep₀ x (h₀add x hx)) Rest hRest
              have hrun'' : ProtSat.Reference.Runs P C₀
                  (ProtSat.Reference.Ev.act q :: dropRedundant rest added) (C₀ :: Cs') :=
                ProtSat.Reference.runs_cons hstep₀ hrun'
              refine ⟨C₀ :: Cs', hrun'', ?_, ?_, ?_⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C, List.Mem.head _, h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov D h2
                  exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro D hD
                rw [List.mem_cons] at hD
                obtain h1 | h2 := hD
                · subst h1
                  exact ⟨C₀, List.Mem.head _, h₀⟩
                · obtain ⟨F, hF, hfd⟩ := hcov' D h2
                  exact ⟨F, List.Mem.tail _ hF, hfd⟩
              · intro x hx
                obtain h1 | h2 := hded x hx
                · exact Or.inl h1
                · obtain ⟨F, hF, hde⟩ := h2
                  exact Or.inr ⟨F, List.Mem.tail _ hF, hde⟩

/-! ### T4: the compression theorem and the derived bound -/

/-- **T4 (secrecy): every leak has a short witness.** Given *any* execution of `P` that leaks a
declared secret and stays inside the universe `univ P B`, there is one with at most
`actionCount P + (univ P B).length` events that still leaks, still stays inside the universe, and
still runs the same sessions. The bound is derived from the model: `actionCount P` is the total
number of actions across the instantiated sessions (T1) and `(univ P B).length` is the size of the
message universe (T2). The proof removes every idle event and every deduction of an already-known
message (T3), which is only legitimate up to the extensional equality of configurations. -/
theorem compress_secrecy {P : Protocol} {B : Bounded.Bounds} {tr : List ProtSat.Reference.Ev}
    {Cs : List RCfg} (hrun : ProtSat.Reference.Runs P (ProtSat.Reference.initCfg P) tr Cs)
    (hb : boundedCfgs P B Cs) (hv : ProtSat.Reference.traceLeaks P Cs) :
    ∃ (tr' : List ProtSat.Reference.Ev) (Cs' : List RCfg),
      ProtSat.Reference.Runs P (ProtSat.Reference.initCfg P) tr' Cs' ∧ boundedCfgs P B Cs' ∧
        tr'.length ≤ actionCount P + (Bounded.univ P B).length ∧
          ProtSat.Reference.traceLeaks P Cs' := by
  classical
  let added := (ProtSat.Reference.initCfg P).kn.eraseDups
  have hadd : ∀ t ∈ added, t ∈ (ProtSat.Reference.initCfg P).kn := fun t ht =>
    List.mem_eraseDups.mp ht
  obtain ⟨Cs', hrun', hcov, hcov', hded⟩ :=
    runs_dropRedundant (cfgEq_refl _) hadd hadd Cs hrun
  have hlen1 : (dropRedundant tr added).length + added.length ≤
      (dedAdded tr added).length + (tr.filter (fun e => isSessEv e = true)).length :=
    length_dropRedundant tr added
  have hsess : (tr.filter (fun e => isSessEv e = true)).length ≤ actionCount P :=
    sessEv_count_le_actionCount hrun
  have huniv : (dedAdded tr added).Nodup :=
    nodup_dedAdded tr added (List.nodup_eraseDups _)
  have hbounded : boundedCfgs P B Cs' := by
    intro D hD
    obtain ⟨E, hE, hde⟩ := hcov D hD
    exact (inBounds_congr hde).mpr (hb E hE)
  have hsub : ∀ x ∈ dedAdded tr added, x ∈ Bounded.univ P B := by
    intro x hx
    obtain h1 | h2 := hded x hx
    · exact Bounded.initKn_subset_univ P B x (hadd x h1)
    · obtain ⟨C', hC', hx'⟩ := h2
      exact (hbounded C' hC').1 x hx'
  have hda : (dedAdded tr added).length ≤ (Bounded.univ P B).length :=
    List.length_le_of_nodup_forall_mem (Bounded.univ P B) (univ_nodup P B)
      (dedAdded tr added) huniv hsub
  refine ⟨dropRedundant tr added, Cs', hrun', hbounded, ?_, ?_⟩
  · omega
  · obtain ⟨C, hC, hleak⟩ := hv
    obtain ⟨D, hD, hde⟩ := hcov' C hC
    exact ⟨D, hD, (leaks_congr hde).mpr hleak⟩

/-- The size of the message universe a query fixes. -/
def universeSize (q : Query) : Nat := (Bounded.univ q.protocol q.bounds).length

/-- **The bound derived from the model**: the total number of session actions plus the size of the
message universe. This is the number a search could reach, and the number after which nothing new
can happen. -/
def derivedSteps (q : Query) : Nat := actionCount q.protocol + universeSize q

/-- The derived bounds: the query's own rounds, and at least as many steps as the model can use
up (the analyst's own number is kept if it is larger). -/
def derivedBounds (q : Query) : Bounded.Bounds :=
  { steps := max q.bounds.steps (derivedSteps q), rounds := q.bounds.rounds }

/-- The same query with the derived bound: same protocol, same sessions, same universe. -/
def derived (q : Query) : Query := { q with bounds := derivedBounds q }

/-- The derived bounds really are an enlargement of the query's own bounds. -/
theorem bounds_le_derived (q : Query) : q.bounds.le (derived q).bounds := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  show q.bounds.rounds ≤ (derivedBounds q).rounds
  exact Nat.le_refl _

/-- **Safety for executions of every length**, inside the sessions, message universe and nonce
domain the query fixes: no execution of any number of events that stays inside the query's own
universe violates a selected goal. This is what a bounded verdict should have meant, and the
compression theorem is what makes the derived bound deliver it. -/
def allLengthsSafe (q : Query) : Prop :=
  ∀ (tr : List ProtSat.Reference.Ev) (Cs : List RCfg),
    ProtSat.Reference.Runs q.protocol (ProtSat.Reference.initCfg q.protocol) tr Cs →
    boundedCfgs q.protocol q.bounds Cs →
      ∀ g ∈ q.goals, ¬ goalViolation q.protocol g Cs tr

/-- **T4, the prize.** For a query that asks only about secrecy, safety at the derived bound is
safety at every length: the finite search stops being a question the analyst picked and becomes a
question the model answers. -/
theorem safe_at_derived_bound (q : Query) (hg : ∀ g ∈ q.goals, g = Goal.secrecy)
    (h : boundedSafe (derived q)) : allLengthsSafe q := by
  intro tr Cs hrun hb g hg' hv
  obtain rfl : g = Goal.secrecy := hg g hg'
  obtain ⟨tr', Cs', hrun', hb', hlen', hv'⟩ := compress_secrecy hrun hb hv
  have hg'' : Goal.secrecy ∈ (derived q).goals := by show Goal.secrecy ∈ q.goals; exact hg'
  have hlen'' : tr'.length ≤ (derived q).bounds.steps :=
    Nat.le_trans hlen' (Nat.le_max_right _ _)
  have hb'' : boundedCfgs (derived q).protocol (derived q).bounds Cs' := by
    show boundedCfgs q.protocol (derivedBounds q) Cs'
    exact hb'
  exact h ⟨Goal.secrecy, hg'', tr', Cs', ⟨hrun', hlen'', hb''⟩,
    (goalViolation_secrecy (derived q).protocol Cs' tr' |>.mpr hv')⟩

/-- **The derived bound decides the query's own question.** Safety at the derived bound implies
`boundedSafe q` for the bounds the analyst actually wrote down - by the bound monotonicity that is
already in the contract, and by nothing else. -/
theorem boundedSafe_of_derived (q : Query) (h : boundedSafe (derived q)) : boundedSafe q :=
  boundedSafe_mono_bounds (bounds_le_derived q) h

/-! ### T5: the derived bound on a real model -/

/-- The contract's secure gate query, as used by the worked instance below. -/
def secureQ : Query := ProtSat.Reference.Contract.Gates.secureQ

/-- The transient-pair query of `ProtSat.ExprDomain`, the model the CNF cannot represent. -/
def transientQ : Query := ProtSat.Reference.Contract.Gates.transientQ

/-!
**A worked instance.** On the contract's own secure gate model the derived bound is a number the
search can actually reach: three session actions (one session, a role of three actions) plus a
thirteen-message universe, so sixteen events. The query's own bound is three; the model says that
checking up to sixteen settles every length.
-/

/-- The secure gate instantiates one session whose role has three actions. -/
theorem secureQ_actionCount : actionCount secureQ.protocol = 3 := by decide

/-- Its message universe has thirteen messages at the query's own closure bound. -/
theorem secureQ_universeSize : universeSize secureQ = 13 := by decide

/-- **The derived bound, as a closed number: sixteen events.** The query itself asks about three;
checking up to sixteen settles every length inside this universe. -/
theorem secureQ_derivedSteps : derivedSteps secureQ = 16 := by decide

/-- The transient-pair model of `ProtSat.ExprDomain`, the one the CNF cannot represent, also gets
a derived bound: three session actions and a seven-message universe. -/
theorem transientQ_derivedSteps : derivedSteps transientQ = 10 := by decide

/-! ### Idle removal as a literal shortening, and where the authentication goals break -/

/-- **T3 in its literal form: a run whose first event is idle can be shortened.** Unlike a
redundant deduction, `Ev.idle` really is a no-op (`stepOf P C idle = some C`), so the shortened run
visits a configuration list with exactly the same members: the dropped configuration is the start
configuration, which the shorter run visits anyway. Hence the leak verdict is unchanged, and no
extensional argument is needed. -/
theorem drop_leading_idle {P : Protocol} {tr : List ProtSat.Reference.Ev} {Cs : List RCfg}
    (h : ProtSat.Reference.Runs P (ProtSat.Reference.initCfg P)
      (ProtSat.Reference.Ev.idle :: tr) Cs) :
    ∃ Cs', ProtSat.Reference.Runs P (ProtSat.Reference.initCfg P) tr Cs' ∧
      (∀ C, C ∈ Cs ↔ C ∈ Cs') ∧
        (ProtSat.Reference.traceLeaks P Cs ↔ ProtSat.Reference.traceLeaks P Cs') := by
  have h2 : ProtSat.Reference.run P (ProtSat.Reference.initCfg P)
      (ProtSat.Reference.Ev.idle :: tr) = some Cs := h
  simp [ProtSat.Reference.run, ProtSat.Reference.stepOf] at h2
  obtain ⟨a, ha, hcs⟩ := h2
  subst hcs
  obtain ⟨rest, hrest⟩ := run_nonempty ha
  have hmem : ∀ C, C ∈ (ProtSat.Reference.initCfg P :: a) ↔ C ∈ a := by
    intro C
    rw [List.mem_cons, hrest, List.mem_cons]
    tauto
  refine ⟨a, ha, hmem, ?_⟩
  refine ⟨fun ⟨C, hC, hl⟩ => ⟨C, hmem C |>.mp hC, hl⟩,
    fun ⟨C, hC, hl⟩ => ⟨C, hmem C |>.mpr hC, hl⟩⟩
/-!
**The precise obstruction for the authentication goals.** The compression T3 performs deletes
events from the trace, and `ProtSat.Reference.Inst.idx` is the *position* of the action in the
trace. `claimMatches` compares positions (`r.idx < c.idx`) and `agreesInj` counts them, so the
authentication events of a compressed trace are those of the original with every index after a
deletion shifted down. Nothing in the current representation makes that shift invisible: two runs
can visit extensionally equal configurations and perform the same claims and commits in the same
order and still have different `insts` lists, because the `idx` fields differ. Extending the
compression theorem to `Goal.agreement` and `Goal.agreementInj` therefore needs one of

* an index-free formulation of agreement - renumber the events of `insts` by their rank in the
  list, which is invariant under deleting non-action events; or
* a proof that deleting a non-session event renumbers `insts` by a strictly monotone map, plus the
  observation that `claimMatches`, `agrees` and `agreesInj` are invariant under such a renumbering.

Both are statements about `Inst.idx`, not about the knowledge representation. What this module
does establish is that the *knowledge* side is already extensional: `CfgEq` is a congruence for
`stepOf`, `inBounds` and `leaks`, which is the half of the argument the roadmap's warning about
redundant copies asks for. -/

end ProtSat.Compress
