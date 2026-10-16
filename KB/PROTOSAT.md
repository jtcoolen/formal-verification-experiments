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
