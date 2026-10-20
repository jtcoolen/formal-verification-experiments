/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Complete
import ProtSat.ExprDomain
import ProtSat.Certificate
import ProtSat.Represent

/-!
# ProtSat: what the public bound already implies (roadmap stage 4, second installment)

Complete.RunOK collects twelve boundedness conditions and Complete.encoding_complete assumes the
whole bundle as WithinBounds. The roadmap asks that compiler representability conditions "should
follow from that predicate and validated query data, rather than added as independent execution-wide
assumptions". Ten of the twelve do follow from the public bound, and this module proves it; for the
two that do not, it says exactly which they are and where they are repaired.

Given BoundedTrace P B tr Cs - a real run, at most B.steps events, every visited configuration
inside univ P B - the status of each field is:

| field | status |
|---|---|
| knU, storeU | the public bound *is* these two (knU_of_bounded, storeU_of_bounded) |
| sessLen, pcB, varB | preserved along the run (cfgOK_init, cfgOK_step, cfgOK_of_runs_mem) |
| varsB, eIdxB, writtenB, pcActB | theorems about the protocol (lt_shV_of_mem, eIdx_lt, lt_shV_of_written, lt_shPc_succ), never about the run; pcActB and the session-index half of actB need lt_sessions_of_actionAt, which is what makes "Rel only lets an instantiated session act" a theorem |
| dedU | derived: a deduction event adds its conclusion to the *next* configuration, which the public bound puts inside the universe (dedU_of_bounded) |
| actB, the m and d fields | **not derivable**: rSend, rAssign, rCheck, rSecret, rClaim, rCommit quantify m and d freely, so the event carries dummy fields that may name anything - the defect roadmap stage 2 repairs with action-specific events |
| exprB | **not derivable from any bound** (Represent.no_bound_discharges_exprB); fixed by the value domain Represent.exprVals, not by the bounds |

withinBounds_of_residual therefore turns the opaque twelve into two dummy-field conditions and
exprB, and Query.boundedSafe_of_encodingUnsat_of_residual is the bridge with that smaller
hypothesis.
-/

namespace ProtSat.BoundedExec

open ProtSat Term Protocol Bounded Encode Encoding Complete ExprDomain

/-! ### Reading a run at an arbitrary position -/

/-- A run visits at least one configuration. -/
theorem runs_Cs_ne_nil {P : Protocol} {C0 : Cfg} {tr : List Ev} {Cs : List Cfg}
    (h : Runs P C0 tr Cs) : Cs ≠ [] := by
  have hl := runs_length h
  intro hz
  rw [hz] at hl
  simp at hl

/-- Reading past the end repeats the last configuration, so every read is a member. -/
theorem cfgAt_mem {Cs : List Cfg} (h : Cs ≠ []) (i : Nat) : cfgAt Cs i ∈ Cs := by
  cases Cs with
  | nil => exact absurd rfl h
  | cons C rest =>
      cases i with
      | zero => rw [cfgAt_head]; exact List.Mem.head _
      | succ i =>
          cases rest with
          | nil => rw [show cfgAt (C :: []) (i + 1) = C from rfl]; exact List.Mem.head _
          | cons y ys =>
              rw [cfgAt_cons_succ (by simp) i]
              exact List.mem_cons.mpr (Or.inr (cfgAt_mem (by simp) i))

/-- Reading a list position gives an element of the list. -/
theorem mem_of_rget_some {α : Type} {l : List α} {q : Nat} {a : α} (h : rget l q = some a) :
    a ∈ l := by
  induction l generalizing q with
  | nil => exact absurd h (by simp [rget])
  | cons x xs ih =>
      cases q with
      | zero =>
          rw [rget] at h
          cases h
          exact List.Mem.head _
      | succ q =>
          rw [rget] at h
          exact List.mem_cons.mpr (Or.inr (ih h))

/-- Bool membership implies Prop membership. -/
theorem contains_mem {U : List Term} {t : Term} (h : U.contains t = true) : t ∈ U := by
  simpa using h

theorem cfgInUniverse_kn {C : Cfg} {U : List Term} (h : cfgInUniverse C U = true) {t : Term}
    (ht : t ∈ C.kn) : t ∈ U := by
  rw [cfgInUniverse, Bool.and_eq_true, List.all_eq_true] at h
  exact contains_mem (h.1 t ht)

theorem cfgInUniverse_store {C : Cfg} {U : List Term} (h : cfgInUniverse C U = true) {q : Nat}
    (hq : q < C.sess.length) {v : Term} (hv : v ∈ storeVals (storeOf C q)) : v ∈ U := by
  rw [cfgInUniverse, Bool.and_eq_true] at h
  rw [List.all_eq_true] at h
  obtain ⟨_, hall⟩ := h
  rw [List.all_eq_true] at hall
  obtain ⟨st, hst⟩ := sessAt_lt hq
  have hst2 := hall st (mem_of_rget_some hst)
  rw [List.all_eq_true] at hst2
  have hstore : storeOf C q = st.store := by
    show (Option.map (fun s => s.store) (rget C.sess q)).getD [] = st.store
    rw [show rget C.sess q = some st from hst]
    simp
  rw [storeVals, hstore, List.mem_map] at hv
  obtain ⟨p, hp, hpy⟩ := hv
  subst hpy
  exact contains_mem (hst2 p hp)


/-! ### The two fields that are the public bound itself -/

/-- RunOK.knU: the attacker only ever knows universe messages. -/
theorem knU_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i : Nat) {t : Term} (ht : t ∈ (cfgAt Cs i).kn) :
    t ∈ (shapeOf P B).U :=
  cfgInUniverse_kn (hbt.2.2 _ (cfgAt_mem (runs_Cs_ne_nil hbt.1) i)) ht

/-! ### Which sessions may act -/

/-- An action is only ever read at an *instantiated* session: roleAt goes through P.sessions, so a
session index with an action is a session index. This is what makes the q bound of RunOK.actB, and
the protocol-level program-counter bound, theorems rather than hypotheses. -/
theorem lt_sessions_of_actionAt {P : Protocol} {q c : Nat} (h : P.actionAt q c ≠ none) :
    q < P.sessions.length := by
  by_cases hq : q < P.sessions.length
  · exact hq
  · refine absurd h ?_
    have hrole : P.roleAt q = none := by
      unfold Protocol.roleAt
      rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hq)]
      simp
    unfold Protocol.actionAt
    rw [hrole]
    simp

theorem nS1_eq_sessions (P : Protocol) (B : Bounds) :
    (shapeOf P B).nS1 = P.sessions.length := rfl

/-- A session that acts has a role position to consume. -/
theorem actionAt_of_act {P : Protocol} {C C2 : Cfg} {q : Nat} {m : Term} {d : NonceName}
    (h : Rel P C (Ev.act q m d) C2) : P.actionAt q (pcOf C q) ≠ none := by
  cases h with
  | rFresh h _ _ => intro hz; exact absurd h (by rw [hz]; simp)
  | rSend h _ => intro hz; exact absurd h (by rw [hz]; simp)
  | rRecv h _ => intro hz; exact absurd h (by rw [hz]; simp)
  | rAssign h _ => intro hz; exact absurd h (by rw [hz]; simp)
  | rCheck h _ _ => intro hz; exact absurd h (by rw [hz]; simp)
  | rSecret h => intro hz; exact absurd h (by rw [hz]; simp)
  | rClaim h => intro hz; exact absurd h (by rw [hz]; simp)
  | rCommit h => intro hz; exact absurd h (by rw [hz]; simp)

/-- The acting session of a transition is an instantiated one. -/
theorem lt_nS1_of_act {P : Protocol} {B : Bounds} {C C2 : Cfg} {q : Nat} {m : Term}
    {d : NonceName} (h : Rel P C (Ev.act q m d) C2) : q < (shapeOf P B).nS1 :=
  lt_sessions_of_actionAt (actionAt_of_act h)

/-! ### The three structural fields, preserved along the run -/

/-- The shape facts every configuration of a run satisfies. -/
structure CfgOK (P : Protocol) (B : Bounds) (C : Cfg) : Prop where
  /-- RunOK.sessLen. -/
  sessLen : C.sess.length = (shapeOf P B).nS1
  /-- RunOK.pcB. -/
  pcB : ∀ q, q < (shapeOf P B).nS1 → pcOf C q < shPc (shapeOf P B)
  /-- RunOK.varB. -/
  varB : ∀ q x, q < (shapeOf P B).nS1 → x ∈ (storeOf C q).map Prod.fst →
    x < shV (shapeOf P B)

theorem pcOf_initCfg (P : Protocol) (q : Nat) : pcOf (initCfg P) q = 0 := by
  unfold pcOf sessAt initCfg
  cases h : rget (P.sessions.map fun _ => ({ pc := 0, store := [] } : SessState)) q with
  | none => rfl
  | some st =>
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp (mem_of_rget_some h)
      rfl

theorem storeOf_initCfg (P : Protocol) (q : Nat) : storeOf (initCfg P) q = [] := by
  unfold storeOf sessAt initCfg
  cases h : rget (P.sessions.map fun _ => ({ pc := 0, store := [] } : SessState)) q with
  | none => rfl
  | some st =>
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp (mem_of_rget_some h)
      rfl

theorem cfgOK_init (P : Protocol) (B : Bounds) : CfgOK P B (initCfg P) where
  sessLen := by
    unfold initCfg
    rw [List.length_map]
    rfl
  pcB := by
    intro q _
    rw [pcOf_initCfg]
    exact shPc_pos _
  varB := by
    intro q x _ hx
    rw [storeOf_initCfg] at hx
    exact absurd hx (by simp)

/-- The variables a write introduces are the ones the action declares, plus those already there. -/
theorem mem_writeVar_vars {x : Var} {t : Term} {s : List (Var × Term)} {y : Var}
    (hy : y ∈ (writeVar x t s).map Prod.fst) : y = x ∨ y ∈ s.map Prod.fst := by
  unfold writeVar at hy
  rw [List.map_cons, List.mem_cons] at hy
  rcases hy with hy | hy
  · exact Or.inl hy
  · right
    obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hy
    obtain ⟨hps, _⟩ := List.mem_filter.mp hp
    have : p.1 ∈ s.map Prod.fst := List.mem_map.mpr ⟨p, hps, rfl⟩
    simpa [hpy] using this

/-- A step that only advances a program counter. -/
theorem cfgOK_succAdvance {P : Protocol} {B : Bounds} {C : Cfg} {q : Nat}
    (hok : CfgOK P B C) (hne : P.actionAt q (pcOf C q) ≠ none) :
    CfgOK P B (succAdvance C q) := by
  obtain ⟨hS, hpc, hv⟩ := hok
  refine ⟨by rw [sessLength_succAdvance, hS], ?_, ?_⟩
  · intro r hr
    by_cases hre : r = q
    · subst hre
      rw [pcOf_succAdvance' C r (by rw [hS]; exact hr)]
      exact lt_shPc_succ (lt_roleLen_of_actionAt hne) (roleLen_le_nPc1 hr)
    · rw [pcOf_succAdvance_other C q r hre]
      exact hpc r hr
  · intro r x hr hx
    rw [storeOf_succAdvance] at hx
    exact hv r x hr hx

/-- A step that publishes: the store of the acting session is untouched. -/
theorem cfgOK_succSend {P : Protocol} {B : Bounds} {C : Cfg} {q : Nat} {t : Term}
    (hok : CfgOK P B C) (hne : P.actionAt q (pcOf C q) ≠ none) :
    CfgOK P B (succSend C q t) := by
  obtain ⟨hS, hpc, hv⟩ := hok
  refine ⟨by rw [sessLength_succSend, hS], ?_, ?_⟩
  · intro r hr
    by_cases hre : r = q
    · subst hre
      rw [pcOf_succSend' C r t (by rw [hS]; exact hr)]
      exact lt_shPc_succ (lt_roleLen_of_actionAt hne) (roleLen_le_nPc1 hr)
    · rw [pcOf_succSend_other C q r t hre]
      exact hpc r hr
  · intro r x hr hx
    by_cases hre : r = q
    · subst hre
      rw [storeOf_succSend_same] at hx
      exact hv r x hr hx
    · rw [storeOf_succSend_other C q r t hre] at hx
      exact hv r x hr hx

/-- A step that writes a variable the action declares. -/
theorem cfgOK_succStore {P : Protocol} {B : Bounds} {C : Cfg} {q : Nat} {x : Var} {t : Term}
    (hok : CfgOK P B C) {act : Action} (hact : P.actionAt q (pcOf C q) = some act)
    (hx : x ∈ act.written) : CfgOK P B (succStore C q x t) := by
  obtain ⟨hS, hpc, hv⟩ := hok
  refine ⟨by rw [sessLength_succStore, hS], ?_, ?_⟩
  · intro r hr
    by_cases hre : r = q
    · subst hre
      rw [pcOf_succStore' C r x t (by rw [hS]; exact hr)]
      exact lt_shPc_succ (lt_roleLen_of_actionAt (by rw [hact]; simp)) (roleLen_le_nPc1 hr)
    · rw [pcOf_succStore_other C q r x t hre]
      exact hpc r hr
  · intro r y hr hy
    by_cases hre : r = q
    · subst hre
      obtain ⟨st, hst⟩ := sessAt_lt (by rw [hS]; exact hr)
      rw [storeOf_succStore_same C r x t st hst] at hy
      rcases mem_writeVar_vars hy with hy | hy
      · subst hy
        exact lt_shV_of_written hact hx
      · exact hv r y hr hy
    · rw [storeOf_succStore_other C q r x t hre] at hy
      exact hv r y hr hy

/-- Every step preserves the structural facts. -/
theorem cfgOK_step {P : Protocol} {B : Bounds} {C C2 : Cfg} {e : Ev}
    (hrel : Rel P C e C2) (hok : CfgOK P B C) : CfgOK P B C2 := by
  cases hrel with
  | rIdle => exact hok
  | rDed =>
      refine ⟨hok.sessLen, ?_, ?_⟩
      · intro q hq; exact hok.pcB q hq
      · intro q x hq hx; exact hok.varB q x hq hx
  | rFresh hact _ _ =>
      exact cfgOK_succStore hok hact (by simp [Action.written])
  | rRecv hact _ =>
      exact cfgOK_succStore hok hact (by simp [Action.written])
  | rAssign hact _ =>
      exact cfgOK_succStore hok hact (by simp [Action.written])
  | rSend hact _ =>
      exact cfgOK_succSend hok (by rw [hact]; simp)
  | rCheck hact _ _ =>
      exact cfgOK_succAdvance hok (by rw [hact]; simp)
  | rSecret hact =>
      exact cfgOK_succAdvance hok (by rw [hact]; simp)
  | rClaim hact =>
      exact cfgOK_succAdvance hok (by rw [hact]; simp)
  | rCommit hact =>
      exact cfgOK_succAdvance hok (by rw [hact]; simp)

/-- Every position of a run satisfies them: induction on the position, stepping with `cfgOK_step`. -/
theorem cfgOK_at {P : Protocol} {B : Bounds} {C0 : Cfg} (hok : CfgOK P B C0) :
    ∀ {tr : List Ev} {Cs : List Cfg}, Runs P C0 tr Cs → ∀ i : Nat, CfgOK P B (cfgAt Cs i) := by
  intro tr Cs h i
  have hrel := (runs_rel h).2
  have h0 := (runs_rel h).1
  induction i with
  | zero => rw [← h0]; exact hok
  | succ i ih => exact cfgOK_step (hrel i) ih

theorem cfgOK_at_init {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (h : Runs P (initCfg P) tr Cs) (i : Nat) : CfgOK P B (cfgAt Cs i) :=
  cfgOK_at (cfgOK_init P B) h i

/-- Read at any position: RunOK.sessLen, pcB, varB. -/
theorem sessLen_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i : Nat) :
    (cfgAt Cs i).sess.length = (shapeOf P B).nS1 :=
  (cfgOK_at_init hbt.1 i).sessLen

/-- RunOK.storeU: sessions only ever store universe messages. -/
theorem storeU_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q : Nat) (hq : q < (shapeOf P B).nS1) {v : Term}
    (hv : v ∈ storeVals (storeOf (cfgAt Cs i) q)) : v ∈ (shapeOf P B).U :=
  cfgInUniverse_store (hbt.2.2 _ (cfgAt_mem (runs_Cs_ne_nil hbt.1) i))
    (by rw [sessLen_of_bounded hbt i]; exact hq) hv

/-- Reading a position beyond the list gives nothing. -/
theorem none_of_not_lt_rget {α : Type} {l : List α} :
    ∀ {q : Nat}, ¬ q < l.length -> rget l q = none := by
  induction l with
  | nil => intro q _; rfl
  | cons x xs ih =>
      intro q h
      cases q with
      | zero => exact absurd (Nat.succ_pos _) h
      | succ q => exact ih (by simpa [List.length_cons] using h)

theorem storeOf_eq_nil_of_not_lt {C : Cfg} {q : Nat} (h : ¬ q < C.sess.length) :
    storeOf C q = [] := by
  unfold storeOf sessAt
  rw [none_of_not_lt_rget h]
  simp

/-- The store form Represent.eval_valAtX_uIdxX consumes: every session store of a bounded run is
universe-valued. -/
theorem storeIn_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q : Nat) :
    storeIn (univ P B) (storeOf (cfgAt Cs i) q) := by
  intro p hp
  by_cases hq : q < (shapeOf P B).nS1
  · exact storeU_of_bounded hbt i q hq (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · rw [storeOf_eq_nil_of_not_lt (by rw [sessLen_of_bounded hbt i]; exact hq)] at hp
    exact absurd hp (by simp)

theorem pcB_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q : Nat) (hq : q < (shapeOf P B).nS1) :
    pcOf (cfgAt Cs i) q < shPc (shapeOf P B) :=
  (cfgOK_at_init hbt.1 i).pcB q hq

theorem varB_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q x : Nat) (hq : q < (shapeOf P B).nS1)
    (hx : x ∈ (storeOf (cfgAt Cs i) q).map Prod.fst) : x < shV (shapeOf P B) :=
  (cfgOK_at_init hbt.1 i).varB q x hq hx

/-! ### The four fields that are theorems about the protocol -/

theorem varsB_of_protocol (P : Protocol) (B : Bounds) :
    ∀ E ∈ allExprs P, ∀ x ∈ Expr.vars E, x < shV (shapeOf P B) :=
  fun E hE x hx => lt_shV_of_mem hE hx

theorem eIdxB_of_protocol (P : Protocol) (B : Bounds) :
    ∀ E ∈ allExprs P, eIdx P E < shE (shapeOf P B) :=
  fun E hE => eIdx_lt hE

theorem writtenB_of_protocol (P : Protocol) (B : Bounds) :
    ∀ q c act, P.actionAt q c = some act → ∀ x ∈ act.written, x < shV (shapeOf P B) :=
  fun q c act hact x hx => lt_shV_of_written hact hx

theorem pcActB_of_protocol (P : Protocol) (B : Bounds) :
    ∀ q c, P.actionAt q c ≠ none → c + 1 < shPc (shapeOf P B) := by
  intro q c hne
  exact lt_shPc_succ (lt_roleLen_of_actionAt hne)
    (roleLen_le_nPc1 (by rw [nS1_eq_sessions]; exact lt_sessions_of_actionAt hne))

/-! ### The deduction field -/

/-- A deduction event's successor is determined. -/
theorem succDed_of_rel_ded {P : Protocol} {C C' : Cfg} {t : Term}
    (h : Rel P C (Ev.ded t) C') : C' = succDed C t := by
  cases h
  rfl

/-- A deduction event adds its conclusion to the next configuration, so the public bound forces it
into the universe. -/
theorem dedU_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i : Nat) {t : Term} (he : evAt tr i = Ev.ded t) :
    t ∈ (shapeOf P B).U := by
  have hrel := (runs_rel hbt.1).2 i
  rw [he] at hrel
  have hcfg := succDed_of_rel_ded hrel
  have hmem : t ∈ (succDed (cfgAt Cs i) t).kn :=
    List.mem_append.mpr (Or.inr (List.Mem.head _))
  rw [← hcfg] at hmem
  exact knU_of_bounded hbt (i + 1) hmem

/-! ### The residual, and the assembly -/

/-- The condition the public bound still does not imply. It used to be three: the delivered message
and the nonce choice of an action event were demanded unconditionally, which no bound can give
because six of the eight action rules quantify those fields freely. RunOK.actB now bounds them
*where the action reads them*, which the public bound does imply (actB_of_bounded), so the residual
is expression representability alone - discharged by a gap-free query
(Represent.exprB_of_domainGap_false) or by the extended value domain (Represent.shapeX). -/
structure Residual (P : Protocol) (B : Bounds) (tr : List Ev) (Cs : List Cfg) : Prop where
  /-- RunOK.exprB, undischarged by the bound alone because no finite universe is closed under the
    protocol constructors (Represent.no_bound_discharges_exprB). -/
  exprB : ∀ i q e, e ∈ allExprs P →
    admissible (shapeOf P B) (Expr.eval e (storeOf (cfgAt Cs i) q)) = true

/-- The only rule that reads the delivered message is `rRecv`, and it reads it as a message the
attacker already knows. -/
theorem kn_of_rel_act_recv {P : Protocol} {C C' : Cfg} {q : Nat} {a : Agent} {x : Var}
    {m : Term} {d : NonceName} (h : Rel P C (Ev.act q m d) C')
    (hact : P.actionAt q (pcOf C q) = some (Action.recv a x)) : m ∈ C.kn := by
  cases h with
  | rRecv _ hm => exact hm
  | rFresh h _ _ => exact absurd hact (by rw [h]; simp)
  | rSend h _ => exact absurd hact (by rw [h]; simp)
  | rAssign h _ => exact absurd hact (by rw [h]; simp)
  | rCheck h _ _ => exact absurd hact (by rw [h]; simp)
  | rSecret h => exact absurd hact (by rw [h]; simp)
  | rClaim h => exact absurd hact (by rw [h]; simp)
  | rCommit h => exact absurd hact (by rw [h]; simp)

/-- The only rule that reads the nonce choice is `rFresh`, and it reads it from the declared
domain. -/
theorem domain_of_rel_act_fresh {P : Protocol} {C C' : Cfg} {q : Nat} {x : Var} {N : NonceName}
    {m : Term} {d : NonceName} (h : Rel P C (Ev.act q m d) C')
    (hact : P.actionAt q (pcOf C q) = some (Action.fresh x N)) : d ∈ P.nonceDomain := by
  cases h with
  | rFresh _ hd _ => exact hd
  | rSend h _ => exact absurd hact (by rw [h]; simp)
  | rRecv h _ => exact absurd hact (by rw [h]; simp)
  | rAssign h _ => exact absurd hact (by rw [h]; simp)
  | rCheck h _ _ => exact absurd hact (by rw [h]; simp)
  | rSecret h => exact absurd hact (by rw [h]; simp)
  | rClaim h => exact absurd hact (by rw [h]; simp)
  | rCommit h => exact absurd hact (by rw [h]; simp)

/-- **The two residual fields are the two no rule reads.** Where a rule does read one, the public
bound already bounds it: a receive delivers a known message, a generation picks a domain nonce. So
`Residual.actM` and `Residual.actD` are not missing facts about the execution - they are artefacts
of an event type that stores fields the transition ignores. -/
theorem actM_of_recv {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q : Nat) {a : Agent} {x : Var} {m : Term} {d : NonceName}
    (he : evAt tr i = Ev.act q m d)
    (hact : P.actionAt q (pcOf (cfgAt Cs i) q) = some (Action.recv a x)) :
    m ∈ (shapeOf P B).U := by
  have hrel : Rel P (cfgAt Cs i) (Ev.act q m d) (cfgAt Cs (i + 1)) := by
    rw [← he]
    exact (runs_rel hbt.1).2 i
  exact knU_of_bounded hbt i (kn_of_rel_act_recv hrel hact)

theorem actD_of_fresh {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q : Nat) {x : Var} {N : NonceName} {m : Term}
    {d : NonceName} (he : evAt tr i = Ev.act q m d)
    (hact : P.actionAt q (pcOf (cfgAt Cs i) q) = some (Action.fresh x N)) :
    d ∈ (shapeOf P B).D := by
  have hrel : Rel P (cfgAt Cs i) (Ev.act q m d) (cfgAt Cs (i + 1)) := by
    rw [← he]
    exact (runs_rel hbt.1).2 i
  exact domain_of_rel_act_fresh hrel hact

/-- **RunOK.actB, from the public bound.** The acting session is instantiated; a delivered
message is bounded where the action reads it (a receive takes a message the attacker knows, and
the bound puts known messages in the universe); a nonce choice is bounded where the action reads
it (the generation rule already demands it from the declared domain). -/
theorem actB_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (i q : Nat) {m : Term} {d : NonceName}
    (he : evAt tr i = Ev.act q m d) :
    q < (shapeOf P B).nS1 ∧
      (readsDelivery P q (pcOf (cfgAt Cs i) q) -> m ∈ (shapeOf P B).U) ∧
      (readsNonce P q (pcOf (cfgAt Cs i) q) -> d ∈ (shapeOf P B).D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hrel : Rel P (cfgAt Cs i) (Ev.act q m d) (cfgAt Cs (i + 1)) := by
      rw [← he]
      exact (runs_rel hbt.1).2 i
    exact lt_nS1_of_act hrel
  · rintro ⟨a, x, hact⟩
    exact actM_of_recv hbt i q he hact
  · rintro ⟨x, N, hact⟩
    exact actD_of_fresh hbt i q he hact

/-- The twelve conditions, now with ten of them theorems. -/
theorem withinBounds_of_residual {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hres : Residual P B tr Cs) :
    WithinBounds P B (cfgAt Cs) (evAt tr) := by
  refine ⟨fun i t ht => knU_of_bounded hbt i ht,
    fun i q v hq => storeU_of_bounded hbt i q hq,
    fun i q m d he => actB_of_bounded hbt i q he,
    fun i t he => dedU_of_bounded hbt i he,
    fun i q hq => pcB_of_bounded hbt i q hq,
    fun i q x hq => varB_of_bounded hbt i q x hq,
    hres.exprB,
    fun i => sessLen_of_bounded hbt i,
    varsB_of_protocol P B, eIdxB_of_protocol P B, writtenB_of_protocol P B,
    fun q c hne => pcActB_of_protocol P B q c hne⟩

/-- **Roadmap stage 4, gate.** For a query whose value domain reports no gap, every bounded
execution satisfies WithinBounds: the compiler representability conditions are theorems about the
public bound and the query, not hypotheses about the run. -/
theorem withinBounds_of_bounded {P : Protocol} {B : Bounds} {tr : List Ev} {Cs : List Cfg}
    (hbt : BoundedTrace P B tr Cs) (hgap : Represent.domainGap P B = false) :
    WithinBounds P B (cfgAt Cs) (evAt tr) :=
  withinBounds_of_residual hbt
    ⟨fun i q e he =>
      Represent.exprB_of_domainGap_false hgap (fun i q => storeIn_of_bounded hbt i q) i q e he⟩

/-! ### The residual is a real gap, not a formality -/

open ProtSat.ExprDomain

/-- The transient-pair model: recv x; check (fst (pair x x)) x; send K. -/
def P0 : Protocol := boundsP

/-- Its bounds, at which the intermediate pair is outside the universe. -/
def B0 : Bounds := boundsB

/-- The same execution as `Regressions.Bounds.cert`, except that the two events whose actions
ignore the delivered message carry a message *outside* the universe. The rules for check and send
quantify `m` and `d) freely, so this is still a legal run of the same protocol through the same
configurations. -/
def dummyCert : Certificate where
  init := initCfg P0
  steps :=
    [ { ev := Ev.act 0 (Term.agent 0) 0,
        after := succStore (initCfg P0) 0 0 (Term.agent 0) },
      { ev := Ev.act 0 (Term.pair (Term.agent 0) (Term.agent 0)) 0,
        after := succAdvance (succStore (initCfg P0) 0 0 (Term.agent 0)) 0 },
      { ev := Ev.act 0 (Term.pair (Term.agent 0) (Term.agent 0)) 0,
        after := succSend (succAdvance (succStore (initCfg P0) 0 0 (Term.agent 0)) 0) 0
          (Term.key (Key.shrk 0 0)) } ]

/-- The checker accepts it: every step is a real transition, dummy fields included. -/
theorem dummy_steps_ok : checkSteps P0 (initCfg P0) dummyCert.steps = true := by decide

theorem dummy_runs : Runs P0 (initCfg P0) (certTrace dummyCert) (certCfgs dummyCert) :=
  checkSteps_runs P0 dummyCert.steps (initCfg P0) dummy_steps_ok

/-- The run stays inside the universe: the dummy message is never stored, never published. -/
theorem dummy_inUniverse : runsInUniverse (certCfgs dummyCert) (univ P0 B0) := by
  intro C hC
  simp only [certCfgs, dummyCert, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> decide

/-- So it is a bounded execution of the query. -/
theorem dummy_bounded : BoundedTrace P0 B0 (certTrace dummyCert) (certCfgs dummyCert) :=
  ⟨dummy_runs, by decide, dummy_inUniverse⟩

/-- **The delivered-message condition is not implied by the public bound.** The second event of
`dummyCert` names a message outside the universe, although the check action it belongs to ignores
the field entirely. -/
theorem dummy_not_actM :
    ¬ (∀ i q m d, evAt (certTrace dummyCert) i = Ev.act q m d → m ∈ (shapeOf P0 B0).U) := by
  intro hall
  have h2 : evAt (certTrace dummyCert) 1 =
      Ev.act 0 (Term.pair (Term.agent 0) (Term.agent 0)) 0 := by decide
  have hnot : Term.pair (Term.agent 0) (Term.agent 0) ∉ (shapeOf P0 B0).U := by decide
  have hmem := hall 1 0 (Term.pair (Term.agent 0) (Term.agent 0)) 0 h2
  exact hnot hmem

/-- The gap is not vacuous in the other direction either: the *canonical* labelling of the same run
satisfies the two dummy-field conditions, so the residual excludes only the arbitrary labelings. -/
def canonicalCert : Certificate where
  init := initCfg P0
  steps :=
    [ { ev := Ev.act 0 (Term.agent 0) 0, after := succStore (initCfg P0) 0 0 (Term.agent 0) },
      { ev := Ev.act 0 (Term.agent 0) 0,
        after := succAdvance (succStore (initCfg P0) 0 0 (Term.agent 0)) 0 },
      { ev := Ev.act 0 (Term.agent 0) 0,
        after := succSend (succAdvance (succStore (initCfg P0) 0 0 (Term.agent 0)) 0) 0
          (Term.key (Key.shrk 0 0)) } ]

theorem canonical_steps_ok : checkSteps P0 (initCfg P0) canonicalCert.steps = true := by decide

theorem canonical_bounded : BoundedTrace P0 B0 (certTrace canonicalCert) (certCfgs canonicalCert) :=
  ⟨checkSteps_runs P0 canonicalCert.steps (initCfg P0) canonical_steps_ok, by decide, by
    intro C hC
    simp only [certCfgs, canonicalCert, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl <;> decide⟩

/-- An action event only occurs inside the trace. -/
theorem lt_length_of_evAt_act {tr : List Ev} {i q : Nat} {m : Term} {d : NonceName}
    (h : evAt tr i = Ev.act q m d) : i < tr.length := by
  by_cases hi : i < tr.length
  · exact hi
  · rw [evAt_past i (Nat.le_of_not_lt hi)] at h
    exact absurd h (by simp)

/-- Every event of the canonical labelling carries the delivered message and the nonce the run
actually uses - both inside the shape. -/
theorem canonical_evAt {i : Nat} {q : Nat} {m : Term} {d : NonceName}
    (h : evAt (certTrace canonicalCert) i = Ev.act q m d) :
    q = 0 /\ m = Term.agent 0 /\ d = 0 := by
  have hi : i < (certTrace canonicalCert).length := lt_length_of_evAt_act h
  have hlen : (certTrace canonicalCert).length = 3 := rfl
  rw [hlen] at hi
  rcases i with (_ | _ | _ | ⟨k⟩)
  · have hr : evAt (certTrace canonicalCert) 0 = Ev.act 0 (Term.agent 0) 0 := rfl
    rw [hr] at h
    exact ⟨by cases h; rfl, by cases h; rfl, by cases h; rfl⟩
  · have hr : evAt (certTrace canonicalCert) 1 = Ev.act 0 (Term.agent 0) 0 := rfl
    rw [hr] at h
    exact ⟨by cases h; rfl, by cases h; rfl, by cases h; rfl⟩
  · have hr : evAt (certTrace canonicalCert) 2 = Ev.act 0 (Term.agent 0) 0 := rfl
    rw [hr] at h
    exact ⟨by cases h; rfl, by cases h; rfl, by cases h; rfl⟩
  · exact absurd hi (by omega)

/-- With the canonical labelling the two dummy-field conditions hold, and the only thing left is
expression representability - which is exactly what `Represent.exprVals` addresses. -/
theorem canonical_actM_actD :
    (∀ i q m d, evAt (certTrace canonicalCert) i = Ev.act q m d → m ∈ (shapeOf P0 B0).U) ∧
      (∀ i q m d, evAt (certTrace canonicalCert) i = Ev.act q m d →
        d ∈ (shapeOf P0 B0).D) := by
  refine ⟨?_, ?_⟩
  · intro i q m d h
    obtain ⟨rfl, hm, hd⟩ := canonical_evAt h
    subst hm
    exact agents_subset_univ P0 B0 0 (by decide)
  · intro i q m d h
    obtain ⟨rfl, hm, hd⟩ := canonical_evAt h
    subst hd
    show (0 : NonceName) ∈ P0.nonceDomain
    decide

/-! ### What the two residual fields really are -/

/-- **And the unconditional form is not merely unprovable, it is false for a whole class of
protocols.** With an empty nonce domain, `actB` demands `d ∈ []` of every action event - including
sends, checks and claims, which generate nothing. Any run in which a session acts is therefore
outside `actB`, so the CNF completeness theorem is vacuous for it. This is exactly the gate roadmap
stage 2 sets ("a send/check must work with an empty fresh-nonce domain"), and the repaired semantics
meets it because its events carry no such field. -/
theorem actB_vacuous_with_empty_nonce_domain {P : Protocol} {B : Bounds} {tr : List Ev}
    {Cs : List Cfg} (hD : P.nonceDomain = []) (i q : Nat) {m : Term} {d : NonceName}
    (he : evAt tr i = Ev.act q m d) :
    ¬ (∀ i q m d, evAt tr i = Ev.act q m d →
        q < (shapeOf P B).nS1 /\ m ∈ (shapeOf P B).U /\ d ∈ (shapeOf P B).D) := by
  intro hall
  obtain ⟨_, _, hd⟩ := hall i q m d he
  have hd' : d ∈ P.nonceDomain := hd
  rw [hD] at hd'
  exact absurd hd' (by simp)

/-- **The residual is genuinely not implied by the bound.** The transient-pair run stores a universe
message and computes a pair the universe cannot name, so expression representability fails for a
bounded execution. This is the hypothesis the extended value domain (Represent.shapeX) exists to
discharge, and the only one left after actB became conditional. -/
theorem exprB_not_derivable :
    ¬ (∀ (tr : List Ev) (Cs : List Cfg), BoundedTrace P0 B0 tr Cs →
        ∀ i q e, e ∈ allExprs P0 →
          admissible (shapeOf P0 B0) (Expr.eval e (storeOf (cfgAt Cs i) q)) = true) := by
  intro hall
  have h1 := hall (certTrace canonicalCert) (certCfgs canonicalCert) canonical_bounded 1 0
    (Expr.pair (Expr.var 0) (Expr.var 0)) (by decide)
  have hstore : storeOf (cfgAt (certCfgs canonicalCert) 1) 0 = [(0, Term.agent 0)] := by decide
  have heval : Expr.eval (Expr.pair (Expr.var 0) (Expr.var 0))
      (storeOf (cfgAt (certCfgs canonicalCert) 1) 0) =
      some (Term.pair (Term.agent 0) (Term.agent 0)) := by rw [hstore]; decide
  have hnot : Term.pair (Term.agent 0) (Term.agent 0) ∉ (shapeOf P0 B0).U := by decide
  rw [heval] at h1
  exact hnot (by simpa [admissible] using h1)

end ProtSat.BoundedExec