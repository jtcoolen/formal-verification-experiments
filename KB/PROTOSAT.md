# PROTOSAT — durable state snapshot (SAT-based protocol analyser project)

Read this first after any context compaction.  It is the authoritative status of the
protosat/ package; STATE.md covers the older quantum/Merkle/Dijkstra work.

## Environment

* Package: protosat/ — its own Lake project, toolchain leanprover/lean4:v4.34.1,
  Mathlib v4.34.1 (rev d13f23b7).
* Mathlib oleans are prebuilt (8908 files, 6.6 GB under protosat/.lake).  Do NOT re-run
  lake exe cache get; the default cache dir ~/.cache/mathlib is outside the workspace and
  is denied by the sandbox — the working invocation is
  MATHLIB_CACHE_DIR=$PWD/.mathlibcache lake exe cache get
* Build: cd protosat && lake build ProtSat  →  "Build completed successfully (694 jobs)".
* Single-file check: lake env lean ProtSat/<Name>.lean
* No sorry, no axiom, no partial def, no native_decide anywhere in ProtSat/.

## Module map (what exists and what it proves)

| module | content | status |
|---|---|---|
| ProtSat/Syntax.lean | §1 message algebra: Key, Term (normal forms, no destructors), size, depth, subterms with a @[simp] membership API per constructor, size_lt_of_subterms, depth_le_of_subterms, the finite universe pool/poolStep with the four constructor-closure lemmas, subtermClosure (subterm-closed: subtermClosure_subterms), pretty printer. | done |
| ProtSat/CNF.lean | propositional layer: Var = Nat, Lit (var + neg flag), Clause, CNF, Assignment = Var → Bool, Sat, Satisfiable, Unsat, sat_append; one-hot atLeastOne/atMostOne/exactlyOne with sat_atLeastOne, sat_atMostOne, **sat_exactlyOne** (∃! characterisation); Tseitin gates notDef/andDef/orDef/impDef each with a sat_* **iff** theorem. | done |
| ProtSat/Attacker.lean | §2: inductive Ded (11 rules), ded_mono/ded_cons/ded_grow (§2.3), constructor/destructor laws encS_then_decS, encA_then_decA, pair_then_proj (§2.4), Term.nonces/noncesOf and **no_fresh_nonces**, nonce_not_deducible, encS_nonce_not_deducible, inductive OneStep + oneStep_ded + oneStep_mono. | done |
| ProtSat/Protocol.lean | §3 DSL: Expr (with destructors), Expr.eval : Expr → store → Option Term (partial: a stuck destructor disables the action), Expr.vars/isClosed/subexpressions, Action (fresh/send/recv/assign/check/secret/claim/commit), Role, Session, SessState, Secret (closed + store q x), AuthProp, Protocol record with actionAt, roleLen, compromisedKeys, initKn, closedSecretTerms, sessionVars. | done |
| ProtSat/Operational.lean | §3/§4 independent semantics: Cfg, Ev (idle / ded t / act q m d), successors succAdvance/succStore/succSend/succDed with frame lemmas (sessAt_succ*_other, sessAt_succ*_same, kn_succ*), rget/rput list helpers, inductive **Rel** with the ten introduction rules rIdle/rDed/rFresh/rSend/rRecv/rAssign/rCheck/rSecret/rClaim/rCommit, Runs/Trace/runs_length, Leak, AuthInst/authOfStep/claimsOf/commitsOf, AuthBreak (non-injective agreement), Attack.  Does NOT import CNF/DPLL/Encode (independence requirement). | done |
| ProtSat/DPLL.lean | §6 solver core: litVal, mentions, madeTrue, madeFalse, SatList, assign (substitution step), assign_mem, any_filter, **satList_assign** and **satList_assign_back** (the two directions of the assignment step), findUnit, unit_forced, propagate (structurally terminating unit propagation), clauseVars. | core done; dpll + 8D/8E pending |

## Design decisions (do not re-litigate)

* **Terms are normal forms.**  The equational theory (fst/snd/decS/decA laws) is to live in
  ProtSat/Theory.lean (raw syntax + inductive EqT + convergent rewriter + decision
  procedure eq_iff_norm) — that module is not written yet.  Everything else works over
  normal forms, which is sound because the rewrite system is convergent and every
  attacker/protocol construction yields a normal form.
* **Attacker steps are explicit events** (Ev.ded t with OneStep).  This is what makes "L
  steps" bound the attacker's derivation depth, and it is what the encoding mirrors, one
  clause group per rule.
* **Knowledge is a growing list**, never "everything is public": Protocol.initKn contains
  only agent names, public keys and compromised keys.
* **The executable saturation over a finite universe lives in ProtSat/Deduce.lean — not
  written yet.**  Attacker.lean ends with a pointer to it.  Plan: oneStepList ag K (a List
  built by flatMap/map over K, one chunk per rule), oneStepList_sound / oneStep_mem,
  closeStep U K := K ++ U.filter (fun t => decide (t ∈ oneStepList ag K)),
  deduce = iterate, then deduce_sound (§2.1), DedIn + dedIn_deduce (§2.2), ded_dedIn.
* **Auth property = non-injective agreement** (a commit with no matching claim anywhere in
  the trace).  Enough to expose the Lowe attack; avoids per-step pebble variables.
* **Freshness is local**: nonceUsed C d = false (d in no session store, not known).

## Known traps (learned the hard way)

* Lean 4.34 + Mathlib v4.34.1: Finset.any **does not exist**; List.any does.
  Finset.biUnion lives in Mathlib.Data.Finset.Union (Mathlib.Data.Finset.Lattice is a
  directory: use ...Lattice.Basic).
* List.Mem is an inductive, not a =-disjunction: use List.mem_cons then rcases … with rfl | h.
* Nat.lt_of_le_of_lt takes (le, lt); for (lt, le) use Nat.lt_of_lt_of_le.  le_refl is not a
  tactic (use exact Nat.le_refl _).
* Bool.or_eq_true.mp / Bool.and_eq_true.mp are **not valid names**; write rw [Bool.or_eq_true]
  at h then rcases h with h | h.
* decide (p && q) parses as (decide p) && (decide q) — write the decides explicitly.
* In a theorem statement, "! x = true" after ∧ is parsed as Prop negation of a coerced Bool;
  write Bool.not x = true.
* A def used as a *partial application* inside List.filter (filter (litKept v b)) defeats
  simp only [litKept]: eta-expand (fun l => litKept v b l).
* List.updateIdx does not exist; Operational.lean defines rget/rput with rget_rput_same /
  rget_rput_other instead.
* Function.iterate: f^[n+1] x = f (f^[n] x) is Function.iterate_succ_apply'; n+1 is not
  defeq to Nat.succ n for the equation compiler, so prove such equations with
  by simp [def, Function.iterate_succ_apply'].
* File writing: use cat > path <<'EOF' heredocs (quoted delimiter).  Python string patching
  with unicode escapes silently no-ops, and a backtick inside a JS template literal breaks
  the tool call.

## Pending (priority order)

1. ProtSat/Theory.lean — raw syntax + EqT + convergent rewriter + eq_iff_norm (§1).
2. ProtSat/Deduce.lean — executable saturation (§2.1, §2.2).
3. ProtSat/Bounded.lean — bounds record (sessions, steps, depth, agent/nonce domains),
   universe construction from protocol + bounds, initial state, BoundedAttack.
4. ProtSat/Encode.lean — the CNF compilation + decode + **8A/8B** (the principal objective).
5. Finish ProtSat/DPLL.lean — dpllAux, dpll, dpll_sound (8D), dpll_complete (8E).
6. ProtSat/Certificate.lean — attack certificate + independent checker + 8C.
7. ProtSat/Analyzer.lean — pipeline + 8F/8G/8H.
8. ProtSat/Examples/*.lean — the six protocols; Main.lean; Axioms.lean audit;
   protosat/README.md; root README table row.

## Commands

    cd /Users/julian/Downloads/formally_verified/protosat
    lake build ProtSat          # 694 jobs, seconds
    lake env lean ProtSat/DPLL.lean

## Round 3 progress (appended)

* Protocol.lean: Expr.child1/child2, stepEval1/stepEval2, constVal, eval_child1/2,
  eval_constVal, subexpressions_trans, Action.exprs; actionAt/roleAt now use the session's
  role index (sessions may share roles).
* CNF.lean: cnfOf, sat_cnfOf, clause_eval_holds, clause_eval_cons_false/of, clause_eval_append_of_false, Lit.flip, andNDef (+mem/sat), Clause.eval_append, sat_append_left/right.
* OneHot.lean: graph2Clauses (+correct/back), fwdClausesOn / fwd2ClausesOn with
  fwd_correct / fwd_complete (guarded forward clauses - the key to a linear/quadratic
  Tseitin encoding).
* Encode.lean: DedInst + dedInstsOf/dedInsts/nInst/instAt (deduction instances as event
  alternatives), tIx, ixOf (renamed from pos: CNF.pos shadowed it), ixOf_le, rget_lt,
  rget_mem, rget_some_mem, uIdx_lt', slotPair, decodeStore via slotPair.
* Clauses.lean (NEW): admissible/univClosed (the universe hypothesis), decVal/decSt/decXe/
  decDeliver/decNonce/decEv/decLearn/decKnSeq/decCfg, the 11 clause groups (oneHot, init,
  frame, eval, step, ded, pubAux, knSupport, fresh, leakAux, violation), encodeGroups,
  encode, sat_encodeGroup + the 10 sat_* extractors.
* Encoding.lean (NEW): list/shape plumbing (nodup_eraseDups, contains_mem, rget_nodup_inj,
  valAt_inj, uIdx_valAt, admissible_valAt), group membership lemmas, decodePc_true /
  decodePc_of_true / decodePc_lt, readVar_decodeStore (store correspondence),
  mem_allExprs_*, event decomposition (decCode, ev_cases, decLearn_code, decEv_code,
  decLearn_act, decLearn_ded, decCode_of_evAct/evDed, evAct_false_of_ne, evDed_false_of_code),
  step_holds/step_body/frame_holds, pubAux_holds, init_kn_sound, **kn_sound** (knowledge
  soundness), publisherLits_cases.

## Remaining for 8A/8B
1. decXe_eq (Tseitin evaluation correspondence, induction on the expression table).
2. Rel step lemmas per rule + Runs + violation (Leak) -> encoding_sound (8A).
3. The reverse construction (assignment from a run) -> encoding_complete (8B).
4. Then DPLL 8D/8E, Certificate 8C, Analyzer 8F/8G/8H, examples, README.

## Round 4 progress (appended)

Verified state: `lake build` green (700 jobs), `lake env lean Axioms.lean` reports
"theorems audited in ProtSat.*: 818+ / OK - every theorem depends only on propext,
Classical.choice, Quot.sound", no sorry anywhere.

New since round 3:
* Encode.lean: `ixOf` (renamed from pos), `ixOf_le`, `rget_lt`, `rget_mem`, `rget_some_mem`,
  `slotPair` + decodeStore via it, `uIdx_lt'`, `tIx` + lemmas, `DedInst`/`dedInstsOf`/
  `dedInsts`/`nInst`/`instAt` (deduction instances), `shEv = 1 + shS + nInst`,
  `shapeOf.nV1` now covers every variable any role writes OR reads (with Action.written).
* Clauses.lean (new module): the 11 clause groups + `encode` + `encodeGroups` +
  `sat_encodeGroup`; `admissible`/`univClosed` (the universe hypothesis); decoders
  decVal/decSt/decXe/decDeliver/decNonce/decEv/decLearn/decKnSeq/decCfg; publisher aux
  (`vpb`, `pubAuxEntry`, `pubAuxClauses`) so the support clause can use conjunctions;
  leak aux (`vau`, `leakAuxClauses`); `violationClauses` (one big clause);
  `storeSecret` restricted to instantiated sessions.
  **Bug found and fixed:** frame clauses must use a POSITIVE evAct literal
  ([evAct, ¬pc_i, pc_{i+1}]); with a negated guard they are vacuous exactly when they
  matter.
* Encoding.lean (new module): shape facts (U_nodup, valAt_inj, uIdx_valAt, admissible_valAt,
  contains_mem, rget_map, lt_shS/lt_shV/lt_shVal, nS1_eq/steps_eq/D_eq), group extractors
  (sat_oneHot ... sat_violation, mem_oneHot_*), decodePc_true/of_true/lt, readVar_decodeStore
  (store correspondence via lookup_filterMap), expression-table closure
  (Action.closed_exprs, mem_allExprs_sub, mem_allExprs_child1/child2, eIdx_lt, eAt_eIdx),
  event decomposition (decCode, ev_cases, decLearn_code/decEv_code/decLearn_act/decLearn_ded,
  decCode_of_evAct/evDed, evAct_false_of_ne, evDed_false_of_code), clause application helpers
  (step_holds, step_body, frame_holds, sat_gate, publisherLits_cases), the four
  correspondences:
  - decXe_eq (Tseitin evaluation, by structural induction on Expr, using xe_unary/xe_binary/
    xe_var/xe_konst and evalGate_unary/binary/var/konst),
  - kn_sound (Boolean knowledge ⟹ real knowledge, by induction on the step),
  - dedInst_oneStep (every instance is a genuine OneStep; case analysis over dedInstsOf),
  - Agrees/decStep/decRun + agrees_zero + decodePc_frame + decSt_frame.

## Still to do for 8A (next)
1. Strengthen `Agrees` with a 4th component: values in a session store <-> decoded slot
   values (needed for `nonceUsed` in Rel.rFresh).
2. `rel_agrees`: case analysis on the decoded event (idle / ded / act-by-action) proving
   `Rel P C (decEv i) (decStep C i) ∧ Agrees (decStep C i) (i+1)`.
3. `encoding_sound` (8A): decRun is a Runs trace of length ≤ steps, inside the universe,
   and the violation clause yields Leak.
4. `encoding_complete` (8B): build the assignment from a bounded attack (use
   Oh.decode_of_true / graph completeness / exactlyOne characterisation), then DPLL 8D/8E,
   Certificate 8C, Analyzer 8F/8G/8H, the six examples, Theory.lean, Deduce.lean, README.

## Traps learned this round (add to the list above)
* `List.contains` is `List α → α → Bool` and relates to membership via `List.elem_eq_mem`;
  there is no `List.nodup_eraseDups` (proved `nodup_eraseDups` by length induction).
* `Nat.lt.step`/`Nat.le.step` dot notation is awkward; use omega with a `show`.
* `unfold X at h` often fails on defs compiled from pattern matching; `rw [h2] at h` after
  `cases h2 : e` works, and `rfl` proves constructor equations that simp cannot reduce.
* rcases auto-splits nested matches; prefer explicit `cases h with | inl | inr` and
  `rw [eq] at hyps` rather than `subst` on structure equations.
* `set sh := shapeOf P B` makes later `show`/`rw` targets ambiguous; write `shapeOf P B`.
* A def that mentions section variables cannot be a `local notation`; and defs whose type does
  not determine the variables (e.g. `decCode`) must take them as explicit parameters.
* `decide (p ≠ q)` inside a filter: use the Prop `≠` in writeVar so if_pos/if_neg take Prop
  proofs.

## Round 5 - 8A IS PROVED (encoding_sound).  Read this first.

Verified state at commit 'ProtSat 8A COMPLETE':
* cd protosat && export ELAN_HOME=$PWD/../.elan && lake build ProtSat  ->  'Build completed
  successfully (701 jobs)', exit 0.
* lake env lean Axioms.lean  ->  'theorems audited in ProtSat.*: 862 / OK - every theorem
  depends only on propext, Classical.choice, Quot.sound'.
* ProtSat/Deduce.lean (1211 lines, spec 2 executable attacker: deduce_sound, oneStep_mem,
  dedIn_deduce, deduce_mono, encS_decS_step + 8 decide-checked example groups) exists and
  checks clean on its own; it is NOT yet imported by ProtSat.lean - add 'import ProtSat.Deduce'.

### What 8A now says
ProtSat.Encoding.encoding_sound : univClosed (shapeOf P B) P -> Sat a (encode P B) ->
Attack P (decEvsFrom P B a B.steps), with encoding_sound_bounded adding trace length <=
B.steps.  Chain: rel_agrees -> agrees_decRun -> decRunFrom_runs -> decRun_trace ->
violation_leak -> encoding_sound.

### New in Encoding.lean (file order)
* decSt_some_vst, decXe_some_vxe: decoded value implies its variable is true.
* init_kn_complete, kn_frame, decLearn_kn, kn_complete: knowledge completeness (converse of
  kn_sound; needed because Rel.rFresh's side condition is negative).
* sendPublish_mem, dedConcl_mem.
* StoreWF + reworked Agrees (5 components: pc, readVar=decSt, kn=decKnSeq, StoreWF of every
  session store, C.sess.length = nS1).  Agrees.storeVals_iff derives the store-value
  correspondence; storeWF_writeVar is the preservation lemma.
* frame helpers: evAct_false_of_other, pcOf_succ_act, decSt_succ_write, decSt_succ_keep,
  storeWF_succ_keep, storeWF_succ_write, decKn_succ_none, agrees_of_frame,
  agrees_succ_advance.
* decoding helpers: decodeFr_val, decodeDl_val, mem_dedInsts, mem_rget, lt_shV_of_written,
  lt_shV_of_mem, fresh_body, bool_not_true, dedInstsOf_prem_lt (every premise index of a
  universe instance is in range: case analysis over the 11 rule shapes).
* rel_agrees: the big case split (idle / ded-instance / act x 8 actions).
* decEvsFrom / decCfgsFrom (built by cons so they line up with Runs), decRunFrom_runs,
  decCfgsFrom_mem, decRun_trace, violationLits_cases, violation_leak, encoding_sound,
  decEvsFrom_length, encoding_sound_bounded.

### Other modules touched
* Operational.lean: Runs.cons FIXED to 'Runs P C (e::tr) (C :: rest)' (it used to drop the
  start configuration and duplicate the last one; runs_length and the docstring give the
  intended meaning).  Added rput_length, rget_lt_aux, sessAt_lt, pcOf_succ*_other,
  storeOf_succ*_other/same, sessLength_succ*, pcOf_succ*' (length-hypothesis versions).
* Protocol.lean: Expr.eval_congr (evaluation depends only on the readings of the free
  variables - this is what lets a store be represented by per-variable one-hot groups).
* Clauses.lean: stepKeepClauses/writtenVar refactor, advClause, keepClause,
  stepClausesAt_some (the unfolding every clause-membership proof now starts with, because
  stepClausesAt's match does not reduce under rw), keepClause_mem_stepClausesAt,
  advClause_mem_stepClausesAt.

### Traps learned in round 5 (add to the list above)
* NEVER use s.indexOf + slice to truncate a Lean file on a pattern that may occur earlier
  than expected: it silently destroyed 1000 lines of Encoding.lean (recovered from git).
  Use unique anchors, assert the index, or append only.
* rw does not iota-reduce 'match some x with ...'; use simp, or state the reduced form with
  show, or add a ..._some lemma (stepClausesAt_some).
* rw [h] at h2 where h's LHS is a def (valAt, readVar, storeOf, sessAt, evDed) fails:
  unfold in the goal first (unfold storeOf sessAt; rw [...]) or pass the defeq term
  explicitly (show rget C.sess q = some st from hst).
* subst on 'r = q' may eliminate the variable you wanted to keep; write the branch using the
  surviving name.
* Anonymous constructors against a right-nested And: when a component's expected type has
  metavariables (e.g. ?C.kn = ...) the elaborator instantiates ?C from the goal, so ascribe
  the term: (decKn_succ_none h hag hlearn : C.kn = decKnSeq ...).
* Bool.or_eq_false and List.contains_eq_true do not exist; use by_contra + Bool.or_eq_true /
  List.any_eq_true and 'by simpa using h' for contains.
* rw's automatic rfl uses reducible transparency: '(some t).toList' needs an explicit rfl.
* omega does not unfold defs like shVal/shD/shS: supply 'have hs : shVal sh = sh.U.length + 1
  := rfl' and rewrite with it first.
* cases h : e with does not always abstract e from the goal when e is a def application;
  'simp only [h] at hgoal' is more robust.
* List.mem_append_left l (h : a in l1) : a in l1 ++ l takes the RIGHT list explicitly;
  List.mem_append_right l1 (h : a in l2) : a in l1 ++ l2 takes the LEFT one.

### Remaining (priority order)
1. 8B encoding_complete: from a bounded attack build a satisfying assignment.  Plan: define
   assignOf block by block over the semantic facts of the run (bounded List.any over the
   index ranges so it stays computable), then prove each of the 11 clause groups satisfied.
   Target statement: a bounded attack (Runs from initCfg, length <= B.steps, Leak) implies
   Satisfiable (encode P B).
2. DPLL 8D/8E (subagent on ProtSat/DPLL.lean: propagate by well-founded recursion on clause
   length, dpllAux branching on the variable list, dpll_sound / dpll_unsat).
3. Certificate 8C (subagent): certificate = list of events + configs; the checker builds Rel
   proofs; it must not import CNF/DPLL/Encode.
4. Analyzer 8F/8G/8H + Main.lean + the six examples + README + theorem inventory.
5. Theory.lean (raw syntax + convergent rewriter + eq_iff_norm) - optional; the normal-form
   design already satisfies spec 1 via Attacker's constructor/destructor laws.
6. Authentication violations in the encoding: AuthBreak is defined in Operational but the
   violation clause only encodes Leak.  Either add a claim/commit clause group or present the
   Lowe attack as a secrecy breach (B's nonce leaks) and say so explicitly in the README.

### Round 5 addendum: the chosen 8B construction (execute this next round)
Define, for a run given as  run : Nat -> Cfg  (configurations at steps 0..B.steps) and
ev : Nat -> Ev  (the event taken at step i, Ev.idle past the end):
  assignOf P B run ev : Assignment
as 'v is the code of a fact that holds in the run', i.e. a disjunction of bounded
List.any searches over the index ranges, one disjunct per variable family:
  pc : (range (steps+1)).any (fun i => (range (shS sh)).any (fun q => v = vpc sh i q (pcOf (run i) q)))
  st : ... v = vst sh i q x (uIdx sh (readVal (run i) q x)) where readVal returns the unset
       index when readVar x (storeOf (run i) q) = none  (use uIdx sh (readVar x (storeOf (run i) q)))
  kn : ... v = vkn sh i (uIdx sh (some t)) for t in (run i).kn  (bounded by range U.length: use
       (range U.length).any (fun u => v = vkn sh i u && valAt sh u ∈ (run i).kn))
  ev : ... v = vev sh i (eventCode (ev i)) with eventCode idle = 0, act q _ _ = 1+q,
       ded t = 1 + shS + nInst-index of the instance concluding t (needs the event to be a
       *legal* event: the boundedness hypothesis supplies the instance index)
  dl : ... v = vdl sh i q (uIdx sh (delivered (ev i) q))   (delivered = the event's m for act)
  fr : ... v = vfr sh i q (ixOf d sh.D)                    (the nonce the event picks)
  xe : ... v = vxe sh i (eIdx P e) (uIdx sh (Expr.eval e (storeOf (run i) q))) for e in allExprs
  vpb: ... v = vpb sh i q c u && session q acts at (i,c) && its send evaluates to valAt u
  vau: ... v = vau sh i q x u && storeSecret && readVar = valAt u && valAt u ∈ kn
Then prove, once per family, the two-way characterisation
  assignOf (vpc sh i q c) = true <-> i <= steps && q < shS && pcOf (run i) q = c
which needs (i) the block-interval lemmas  vpc sh i q c < bsSt sh,  bsSt sh <= vst ... < bsKn sh,
... (7 blocks, each an upper/lower bound: call them blk_vpc_lt, blk_vst_ge, blk_vst_lt, ...),
proved from the positional codes by Nat.mul_div / omega, and (ii) that the index of a fact is
unique (vpc_inj etc., already in Encode.lean).
Then each of the 11 clause groups is discharged clause by clause:
  oneHot: exactlyOne via the uniqueness of pcOf/readVar/eval values + the range facts;
  init: pc 0 = 0, stores empty (readVar = none -> the unset index), kn = initKn;
  frame: monotonicity of the run (Rel gives store/kn growth) - use the successor lemmas;
  eval: the Tseitin gates follow from decXe-style computation of Expr.eval on the decoded
       values (f1/f2 are exactly uIdx of stepEval1/2);
  step: the action clauses follow from the Rel hypothesis of each step;
  ded/knSupport: the instance that fired is a premise-satisfying one;
  fresh: the nonce is in D and unused (boundedness);
  leakAux/violation: the Leak witness supplies the true literal.
Statement to aim for:
  theorem encoding_complete (hU : univClosed (shapeOf P B) P) {tr : List Ev} {Cs : List Cfg}
    (hrun : Runs P (initCfg P) tr Cs) (hlen : tr.length <= B.steps)
    (hleak : runsLeaks P Cs) (hbnd : WithinBounds P B Cs tr) :
    Satisfiable (encode P B)
with WithinBounds defined in this file (every kn message and every stored value is in U,
every delivered message in U, every generated nonce in D, every event either idle, an act
of an instantiated session, or a ded whose message is in U).

### Subagent status at end of round 5
* DPLL agent 35e59f37-... : re-tasked (it had stopped without editing DPLL.lean).
* Certificate agent 16ce7ce0-... : running (ProtSat/Certificate.lean, spec 7/8C).
* Deduce agent e28034d6-... : DONE, Deduce.lean integrated and building.

---

## Round 6 - DPLL rebuilt (8D/8E), 8C integrated, Analyzer written (8F)

### Verified state
* cd protosat && export ELAN_HOME=$PWD/../.elan && lake build ProtSat -> 'Build completed
  successfully (925 jobs)', exit 0.
* lake env lean Axioms.lean -> 1487 theorems audited, only propext / Classical.choice /
  Quot.sound.  No sorry, admit, partial def or native_decide anywhere.

### What was done
1. ProtSat/DPLL.lean REWRITTEN FROM SCRATCH (the round-5 subagent had left it broken: 8
   compile errors).  Design decisions that matter:
   * unit propagation is 'propagateGo : Nat -> List Clause -> Option (decisions x clauses)'
     with EXPLICIT FUEL, called as 'propagate cs := propagateGo cs.length cs'.  Structural
     recursion, so the equations propagateGo_zero/succ are rfl and every lemma is a plain
     induction on the fuel.  Well-founded recursion was tried first and rejected: Lean
     generates no equation lemmas for it (no fn.eq_2), rfl fails on the defining equations,
     and cases h : fn x then fails with 'Dependent elimination failed'.
   * propagateGo_spec (back / fwd / agr) and propagateGo_vars (5 conjuncts: variable subset,
     decided variables disjoint from the reduced set, decided variables occurred, decisions
     consistent, no empty clause survives) are the whole content of propagation.
   * propagate_noUnit: the fuel cs.length always saturates (each step deletes a clause,
     assign_length_lt) - the saturation half of 8H.
   * dpllAux cs vs asg recurses structurally on vs.  The invariants are NoAssigned cs asg
     (no clause mentions a decided variable - this is what keeps the decision list
     consistent, because a restriction deletes every literal of its variable) and
     VarsIn cs vs.  A branch variable already decided by propagation is skipped.
   * dpllAux_sound proves in one induction: output extends input, every total assignment
     respecting the output satisfies the original set, output is consistent.
     dpllAux_complete: output none => no model agrees with the decisions.
   * dpll f = dpllAux f.clauses (eraseDups (litVars f.clauses)) []; dpll_sound (8D),
     dpll_complete (8E), satisfiable_iff_dpll.
   * Kernel-checked examples (decide): demoUnit, demoConflict, demoBranch (no unit clause,
     unsat only by branching + conflict), demoBranchSat.
2. ProtSat/Certificate.lean (8C) INTEGRATED - it existed but was never imported.
   checkCertificate_sound, checkCertificate_authbreak, certificate_of_runs, 5 accepted and 3
   rejected example certificates, all decide-checked.
3. ProtSat/Complete.lean (8B groundwork) FIXED and integrated: vpb_inj_full / vau_inj_full
   were broken (rw [Nat.add_assoc] twice only rewrites the LHS); fixed with
   'simp only [Nat.add_assoc] at h' + repeated Nat.add_left_cancel.
4. ProtSat/Analyzer.lean WRITTEN (spec 7 and 8F):
   * univClosedBool + univClosedBool_iff (the universe hypothesis is decidable).
   * stepsOf / certOf: the certificate of a satisfying assignment, built by recursion on the
     step bound so it prepends (matching decEvsFrom's cons structure).  stepsOf_ev,
     stepsOf_cfgs, stepsOf_ok (rel_agrees + relDecide_complete), certOf_checked.
   * Verdict (boundsTooSmall | safe | attack c) and analyze P B.
   * analyze_attack_sound (8F) and analyze_attack_bounded (trace length <= B.steps).
   * 8G (safe => no bounded attack) still needs 8B and is NOT claimed.

### Traps learned this round
* Anonymous-constructor patterns are NOT accepted in 'cases h : e with | some ⟨a, b⟩ =>'
  ('Alternative cons has not been provided'); use '| some pf =>' then 'obtain ⟨a, b⟩ := pf'.
* 'cases h : fn x' when the goal mentions (fn x): Lean substitutes the constructor form into
  the GOAL, so the equation h becomes useless ('expected none = none', 'Dependent elimination
  failed').  Robust workaround: prove 'option_cases (o : Option α) : o = none ∨ ∃ a, o = some a'
  by 'cases h : o' with Or.inl rfl / Or.inr ⟨a, rfl⟩, then 'rcases option_cases (fn x) with
  hnone | ⟨r, hr⟩' and 'simp only [hr] at h' (simp, not rw, so the match iota-reduces).
* Term-mode 'match e with' on a non-variable scrutinee does NOT abstract e in the expected
  type; findUnit_cases had to be done with cases + Or.inl rfl.
* Inside one tactic sequence all tactics must share a column: after replacing a cases
  alternative by bullets, the old deeper-indented body gives 'unexpected identifier; expected
  command'.
* 'rw [propagateGo_zero, if_neg h0] at h': the equation lemma must be in the SAME rw list.
  if_pos/if_neg still work but are deprecated (ite_eq_left / ite_eq_right).
* List.not_mem_nil does not have the shape you expect; for 'p ∈ []' write
  'absurd hp (by intro h; cases h)'.
* List.exists_mem_of_ne_nil takes the list explicitly in 4.34 - easier to 'cases l'.
* Destructuring a 5-binder Pi (∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p.2 = q.2) with a 4-binder fun
  gives bizarre 'expected BVar × Bool but got Prop' errors.  Count the binders.
* 'x == x = true' is NOT rfl for a derived BEq on a structure with variables: use
  'beq_iff_eq.mpr rfl'.
* Option.map_eq_some' does not exist in Mathlib v4.34.1; prove option_map_some yourself
  (Option.some.inj in the some branch).
* A docstring before #eval is a parse error ('expected lemma'); use a line comment.
* 'decide' on (dpll f).isSome works: every definition is structural and computable.


## Round 6b (same round, later phase) - examples, demo, docs

* ProtSat/Examples.lean: all six specification-9 protocols.
  - Challenge (secure, SAFE at steps 2 / rounds 0, 1335 vars, 2995 clauses; bounds_ok and the
    UNSAT verdict decided by the kernel).
  - Replay (static authenticator): DPLL finds a 4-event attack; checkCertificate of the
    decoded certificate DECIDED true; Attack derived by 8C.
  - KeyDisclosure: 2-event attack found by the solver + certificate; the control with
    compromised = [] is SAFE (decided).
  - NS (original Needham-Schroeder public key) modelled per instantiation; the 14-event Lowe
    attack trace is kernel-verified by checkCertificate = true (NS.checked / NS.attack).
    The NS SAT instance at those bounds has 2,586,336 variables - too large for the reference
    solver, hence the certificate route.
  - NSL (Lowe's fix): the SAME script is REJECTED (decided false); NSL.prefix_ok and
    NSL.breaks_at_the_check localise the failure to A's identity check.
* Main.lean: lake exe protosatDemo prints shapes, CNF sizes, univClosed, verdicts and
  certificate answers; runs in 1.7 s.
* protosat/README.md (17 KB): model, encoding, solver, certificates, the 8A-8H table with
  exact Lean names, the examples table, guarantees and non-claims, module map.
* Root README: ProtSat row, layout entry, quick start.

### Two CRITICAL bugs found and fixed this round (see the commits)
1. The one-hot at-most-one encoding was pairwise: O(|U|^2) clauses per group (toy protocol:
   6M clauses; smallest realistic instance: 227k clauses, 7 min to solve).  Replaced by a
   linear sequential counter (CNF.atMostOneSeq + proof; Oh gains per-group aux flags in new
   blocks bsApc..bsAfr).  8A (Encoding.lean, 3559 lines) recompiled UNCHANGED.
2. univClosed demanded the finite universe be closed under the protocol's own constructors
   (for pair: pair x y in U for ALL x,y in U) - unsatisfiable, so 8A was VACUOUS for every
   protocol that builds a message.  Fixed with the standard BMC under-approximation:
   Encode.uIdx maps out-of-universe values to the unset index (new valAt_uIdx_filter), an
   action whose value the bounds cannot name is disabled, univClosed is now "every closed
   protocol expression denotes a universe message" (satisfiable + decidable + checked by the
   analyser), and decXe_eq is restated as the one-directional correspondence 8A needs
   (decoded value some t => the real evaluation is some t), proved with the new filter_some.
   xe_unary/xe_binary now state the gate through Option.filter.

### Traps learned (add to the list above)
* A docstring before #eval or set_option is a parse error ("expected lemma"); use --.
* decide on a DPLL solve is far slower than the interpreter (heartbeat/whnf limits); keep
  kernel decide for the cheap closed computations (checkCertificate, univClosedBool, small
  solver examples) and run the big solves in the executable.
* rcases with 'rfl' on 'p = x' may eliminate x (the outer variable) instead of p; use
  explicit equations + 'hueq ▸ h' or subst deliberately.
* 'rw [← hqy] at h' direction confusion: to replace q by y in hqa : a q = true, use
  'rw [hqy] at hqa' (forward).
* '!' before a Prop-valued expression is parsed as negation of a decide: write Bool.not.
* In a term, 'l[i]?.getD x' inside a structured proof can fail to parse; use List.drop/take.
* Protocol has no initKn field - initKn is derived from agents/compromised.  To give the
  attacker a recorded message, model it as something the attacker can DEDUCE from public
  data (that is the honest formulation of a replay anyway).
* NS roles must extract Na with fst/snd of the decrypted pair; getting it wrong shows up as
  relDecide = false at the forwarding step, so debug with
  'certOfTrace P tr |>.steps |>.mapIdx (fun i st => relDecide P prev st.ev st.after)'.

---

## Round 7 - 8B machinery: one-hot groups DONE, init/frame IN PROGRESS

### Verified state
* cd protosat && export ELAN_HOME=$PWD/../.elan && lake build ProtSat -> 'Build completed
  successfully (927 jobs)', exit 0.  Complete.lean is now 2201 lines.
* Commits this round: (1) fixed the three broken aux-flag injectivity proofs (adl/afr used the
  wrong stride: adl's inner stride is shVal, afr's is shD; aev needs its OWN code aev =
  bsAev + i*shEv + j, NOT vev); (2) the 8B machinery below.

### What was added to ProtSat/Complete.lean (all compiling)
1. RunOK extended from 6 to 8 components:
   7. every protocol expression denotes a universe message (or none) in every session store of
      the run (admissible sh (Expr.eval e (storeOf (cfg i) q)) = true for e ∈ allExprs P);
   8. (cfg i).sess.length = sh.nS1.
   Component 7 is REQUIRED for the Tseitin gates to be exact (uIdx can only name universe
   values); without it a run that computes encS x y outside U is not representable.
   Accessors runOK_knU/storeU/act/dedU/pc/var/expr/sessLen are proved with
   'rcases h with ⟨h1,...,h8⟩' (dot-projection chains are off-by-one traps).
2. Rel inversion lemmas: Rel.noAct (event does not act on q => pc/store/sess-length
   preserved), Rel.act_pcOf, Rel.kn_mono, Rel.kn_step (shape of knowledge growth),
   Rel.kn_new (a newly known message was deduced or sent), Rel.ded_oneStep.
3. decide_congr, clause2_left/right, clause3_* (to be added), getD_rangeMap, ixOf_lt.
4. atMostOneSeq_sat_from : THE key lemma for the sequential counter's completeness.  Offset
   formulation: variables indexed i+o = k, flags decide (k <= j+o).  The offset o is
   essential: the recursion drops the head, and for k = 0 the suffix has no selected index
   while its flags are all true.
5. Oh.sat_range : a group with vals = List.range K, exactly index k true and prefix flags,
   satisfies o.clauses (atLeastOne via sat_atLeastOne + atMostOneSeq via the lemma above).
6. univSub sh (subterm-closed universe) + subtermsL_pair1/2, encS1/2, encA1, hash1, tIx_some.
7. dedInstsOf_complete (all 11 OneStep rules -> an enumerated instance), prem_ok0/1/2,
   find?_some_of_exists, dedIx_spec, dedIx_exists.
8. rdPc_lt / rdSt_lt / rdXe_lt / rdDl_lt / rdFr_lt / rdEv_lt (rdEv_lt needs the Rel hypothesis
   of the step, because for a ded event rdEv uses dedIx which needs OneStep).
9. assignOf_ge_bsTotal (collapses the 7 main cascade tests) + assignOf_apc/ast/axe/aev/adl/
   afr/vpb/vau (branch + value combined) + decide_symm.
10. sat_pcOh/sat_stOh/sat_xeOh/sat_evOh/sat_dlOh/sat_frOh + sat_flatMap_id + sat_oneHot.
11. rdFr's out-of-range fallback changed from shD sh (OUT of range -> atLeastOne unsatisfiable)
    to 0 (the freshness group is unconstrained when q does not act).

### Lean traps learned this round (IMPORTANT, they cost hours)
* 'cases h with | ctor a b =>' can only name the constructor's EXPLICIT arguments; index
  arguments that get substituted are introduced INACCESSIBLE - name them with 'rename_i x y'.
  Arity per Rel constructor when the event/successor are variables: rIdle 0, rDed 1 (the
  hypothesis!), rFresh 3, rRecv/rAssign/rSend 2, rCheck/rSecret/rClaim/rCommit 3.
* Structure-instance notation inside a 'have h : ({...} : T) ∈ l' or '⟨{...}, ...⟩' often fails
  to parse/elaborate.  Workarounds: put it on ONE line with the ascription, or reduce the goal
  first (unfold/rw/dsimp) so the instance can be '⟨_, memb, ..., rfl⟩'.
* rw does NOT reduce 'match' terms (compiled to X.match_1 aux defs); 'dsimp only' and
  'simp only [defname]' DO.  For dedInstsOf the working recipe is
  'unfold dedInstsOf; rw [hU]; dsimp only' then 'rw [tIx_some hxU]; dsimp only'.
* 'unfold f; rw [h]' leaves the match unreduced but the RESULT is still defeq: term-mode
  'exact if_pos hq' after 'unfold rdFr; rw [h]' works where 'rw [if_pos ...]' does not.
* List.mem_flatMap.mp at a hypothesis whose list is displayed as '(List.map f l).flatten'
  fails; use 'simp only [defname, List.mem_flatMap, List.mem_range] at h' and then 'obtain'.
* rcases on 'cl ∈ List.map f l' (a List.Mem with a non-cons list) fails with 'Dependent
  elimination failed'; convert with List.mem_map first.  Note List.mem_map gives 'f a = b'
  (function image on the LEFT), so 'obtain ⟨c, hc, rfl⟩' substitutes b := f c and the goal
  then contains the unreduced 'if'.
* 'Nat.lt_succ_of_lt h : n < m -> n < m+1' (NOT n+1 < m+1); use Nat.succ_lt_succ for that.
* 'List.mem_range' after obtain: bounds may come out as '∈ range' or as '<'; 'by simpa using h'
  normalises both.
* ++ is LEFT associative in Lean 4 (infixl:65).  domainKeys/seeds/closeOne membership chains must
  be built with the matching Or.inl/inr nesting.
* omega does not unfold shS/shD/...: supply 'have hs : shS sh = sh.nS1 + 1 := rfl' first.
* 'Bool.and_eq_true.mpr' does not exist; use 'rw [Bool.and_eq_true]' then a pair.
* 'List.getD_eq_getElem' is in Mathlib.Data.List.GetD (must be imported); the robust identity is
  'rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]' + rfl/simp.

### Remaining for 8B (chunk 3 onwards) - the ten other clause groups
Statement being aimed at (in ProtSat.Complete):
  theorem encoding_complete {P B tr Cs} (hU : univClosed (shapeOf P B) P)
    (hsub : univSub (shapeOf P B)) (hrun : Runs P (initCfg P) tr Cs)
    (hlen : tr.length ≤ B.steps) (hleak : runsLeaks P Cs)
    (hbnd : WithinBounds P B (cfgAt Cs) (evAt tr)) : Satisfiable (encode P B)
with the assignment assignOf (shapeOf P B) P (cfgAt Cs) (evAt tr) and the pointwise Rel supplied
by runs_rel (already proved in this file).
Groups and the facts each needs:
* oneHot: DONE (sat_oneHot).
* init: sat_init - pcOf (initCfg P) q = 0, readVar x [] = none -> uIdx none = U.length,
  knHolds sh cfg 0 u = initKnHolds sh P u.  IN PROGRESS (destructuring of the 3-way append).
* frame: sat_frame - Rel.kn_mono + Rel.noAct + evActs (rdEv = 1+q <-> q acts).  IN PROGRESS.
* eval: use fwdClausesOn_complete / fwd2ClausesOn_complete / Oh.decode_of_true; the gate
  equations need component 7 of RunOK: rdXe sh P cfg ev i q (eIdx P E) =
  uIdx sh (Expr.stepEval1 E (valAt sh (rdXe ... (eIdx P c)))) etc.  Also evalLeafGate's var
  case: rdXe(var x) = rdSt x; constant case: eval_constVal.
* step: case split on the Rel rule of step i; advClause via Rel.act_pcOf, keepClause via
  readVar_succStore_other / storeOf_succSend_same / storeOf_succAdvance, actionClauses per
  action kind (fresh: rdFr = ixOf d D + rget D (ixOf d D) = some d + storeOf_succStore_same;
  send: rdXe = uIdx t + Rel.kn growth; recv: rdDl = uIdx m + m ∈ kn from rRecv; assign;
  check: both sides equal).
* ded: evDed i n with n = dedIx; premises known via dedInstOk; conclusion known at i+1.
* pubAux: andNDef via sat_andNDef (aux = asgPb's conjunction, by construction).
* knSupport: Rel.kn_new + the publisher literals (sendPubLit via asgPb, instPublisher via
  dedIx).
* fresh: freshUseClauses - nonceUsed (cfg i) d = false gives 'not in any store' and 'not known'.
* leakAux: andNDef with asgAu (by construction).
* violation: runsLeaks gives a true literal (closedLeakLits: t ∈ kn -> vkn i u with u = uIdx t;
  storeLeakLits: storeSecret + readVar = some t + t ∈ kn -> vau).
Then: Satisfiable intro, and in Analyzer.lean the 8G theorem (SAFE => no bounded attack),
8H termination statements, README + theorem inventory updates.
NOTE: univSub (shapeOf P B) is currently a HYPOTHESIS of 8B.  Proving it (Bounded.univ is
subterm-closed) is possible - the pieces are subtermClosureL_closed + a closeOne-preservation
lemma - but the membership plumbing (left-nested ++ over a 5-fold append) fought back; the
analyzer should instead CHECK it by decide, like univClosed.

### Round 7b (same round, later) - sat_init DONE, sat_frame 90%
* Complete.lean now also has: clause1/clause2_left/clause2_right/clause3_left/mid/right,
  bool_eq_cases, sat_cnfOf3, rget_map, rdEv_act, rdEv_act_of_lt, evActs, assignOf_evAct,
  init_pcOf_zero, init_readVar_none, **sat_init** (clause group 2, complete).
* Build green (927 jobs); lake env lean Axioms.lean -> 1781 theorems, only propext /
  Classical.choice / Quot.sound; lake exe protosatDemo still prints all six examples.
* sat_frame draft is in scratch/frame_draft.lean (NOT yet in the library).  What is left:
  the two 3-literal frame clauses (pc and store).  The knowledge clause is done.
  The remaining obstacle is purely tactical: inside
  'have e3 : (pos (vpc sh (i+1) q c)).eval (assignOf sh P cfg ev) = true := by ...'
  the 'simp [pos_eval, hv]' / 'rw [pos_eval]; exact hv' both report failure, and the error
  then cascades onto the following 'exact clause3_right ...' (the reported goal is the
  leftover 'have' goal, which is why the messages look nonsense).
  NEXT STEP: print the real goal with 'set_option pp.all true' + trace_goal inside the first
  'have e1' block, or restructure to avoid nested 'have ... := by' in bullets:
  prove the three literal evaluations as top-level 'have's BEFORE the rcases on hact/h2, or
  use 'refine clause3_right (assignOf sh P cfg ev) (pos (evAct sh i q)) (neg (vpc sh i q c))
  (pos (vpc sh (i+1) q c)) ?_' with the bullet on its own line.
  Note hact/h2 must be equation hypotheses (rcases bool_eq_cases ... with h|h), NOT by_cases
  (which gives a ¬ hypothesis that simp cannot rewrite with).

### Round 7c - where sat_frame stands (scratch/frame_draft.lean)
The draft proves the knowledge clause and reduces each 3-literal frame clause to a literal
evaluation.  The failing step is mechanical: after
  rcases bool_eq_cases (assignOf sh P cfg ev (vpc sh i q c)) with h2 | h2
the FIRST bullet contains
  have h9 : pcOf (cfg (i + 1)) q = c := by rw [hpc']; ...of_decide_eq_true...
  have hv : assignOf sh P cfg ev (vpc sh (i + 1) q c) = true := by
    rw [assignOf_pc sh P cfg ev (Nat.succ_le_of_lt hi) hq (by simpa using hc)]
    exact decide_eq_true h9
and Lean reports a leftover goal 'Lit.eval (assignOf sh P cfg ev) (pos (vpc sh (i+1) q c)) =
true' at the NEXT tactic, i.e. one of these two 'have' blocks is not closed.  Most likely
'show rdPc ... = pcOf ... from rfl' style defeq steps are the culprit: replace them by
'have h9 : rdPc sh P cfg ev (i+1) q = pcOf (cfg (i+1)) q := rfl' and rewrite with h9, and
close hv with 'rw [assignOf_pc ...]; exact decide_eq_true h9' where h9 : rdPc sh P cfg ev
(i+1) q = c (NOT pcOf ... = c).  Try also 'refine decide_eq_true ?_; ...' to avoid the
defeq display confusion, and remember that a failing 'have ... := by' makes every following
tactic in the bullet target the leftover goal - that is why the error messages look absurd.
Everything else (groups 1 and 2) is done and committed.
