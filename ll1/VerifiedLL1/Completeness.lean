/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Parser

/-!
# Phase 3 — completeness, rejection and termination

## What this module establishes

Write `Lang G syms ws` for `∃ ts, MatchList G syms ts ∧ yieldForest ts = ws`; by
Phase 1 this is exactly `Derives G syms (toks ws)`.

* **Rejection (no false accepts).**  For *any* table, if the parser accepts then the
  input is in the language (`parse_ok_imp_language`).  Hence a word outside the
  language is rejected at *every* fuel value (`never_accepts_of_not_language`).
  No hypothesis on the grammar is needed for this direction.
* **Malformed input.**  Acceptance forces the input to be exactly the token word
  followed by the single end-of-input marker (`parse_ok_imp_shape`), so streams that
  do not end in `eof` are never accepted.
* **Completeness.**  `complete_of_match`: if the table is `Correct` and *progressing*
  then every symbol list that has a matching forest is accepted for *some* fuel.
  Together with rejection this yields `language_iff_accepts`: the parser accepts
  **exactly** the language of the grammar.

## Why a progress hypothesis is needed, and what it says

A correct table can still loop: with productions `p → p` and `p → a`, the entry
`M p a = [var p]` is sound, adequate and complete (each condition holds because
`p ⇒* w` iff `p ⇒ p ⇒* w`), yet no fuel ever suffices to parse `a`.
`Examples/Loop.lean` makes that a theorem rather than a remark.

The hypothesis must say that *recursion under the table consumes input*.
`Progressing G M w` does that with a rank `w : N → Nat`:

> if the table expands `A` to `rhs`, and `ts` is a forest matching `rhs` with yield
> `ws`, then a child of `ts` rooted at `B` that is preceded only by children yielding
> `ε` satisfies `w B < w A`.

So each child either starts after something that consumed a token, or has strictly
smaller rank: the pair (tokens remaining, rank) is a lexicographic variant, encoded
below as the single natural `nodeCode K w t = |yield t| · (K+1) + w(root t)`.

`Progressing` talks about the table and the grammar, never about the parser, so the
specification is not circular.  Right recursion is covered: in
`instrs → instr instrs` the recursive child is preceded by `instr`, which never
yields `ε`, so no rank drop is demanded.
-/

-- The section instances `LawfulBEq T` / `LawfulBEq N` are needed by the parser
-- definitions this module reasons about, but not by every lemma stated in the section.
set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N]
  {M : Table T N} {G : Grammar T N}

section Progress

/-- The rank of a tree node: |(yield)| and rank packed into one natural number, so
that the lexicographic variant becomes an ordinary `Nat| descent.  A leaf has rank
`0`; a node has rank `|yield| · (K+1) + w(root) + 1`, so every node outranks every
leaf below it and the `+ 1` keeps node ranks strictly positive. -/
def nodeCode (K : Nat) (w : N → Nat) : Tree T N → Nat
  | Tree.leaf _ => 0
  | t@(Tree.node A _) => (Tree.yield t).length * (K + 1) + w A + 1

theorem nodeCode_leaf (K : Nat) (w : N → Nat) (a : T) : nodeCode K w (Tree.leaf a) = 0 := by
  simp [nodeCode]

theorem nodeCode_node (K : Nat) (w : N → Nat) (A : N) (ts : List (Tree T N)) :
    nodeCode K w (Tree.node A ts) = (Tree.yield (Tree.node A ts)).length * (K + 1) + w A + 1 := by
  simp [nodeCode]

/-- The maximum node rank among the trees of a forest. -/
def forestCode (K : Nat) (w : N → Nat) : List (Tree T N) → Nat
  | [] => 0
  | t :: ts => max (nodeCode K w t) (forestCode K w ts)

@[simp] theorem forestCode_nil (K : Nat) (w : N → Nat) : @forestCode T N K w [] = 0 := rfl
theorem forestCode_cons (K : Nat) (w : N → Nat) (t : Tree T N) (ts : List (Tree T N)) :
    forestCode K w (t :: ts) = max (nodeCode K w t) (forestCode K w ts) := by
  simp [forestCode]

theorem forestCode_le_of_mem (K : Nat) (w : N → Nat) {ts : List (Tree T N)} {t}
    (h : t ∈ ts) : nodeCode K w t ≤ forestCode K w ts := by
  induction ts with
  | nil => exact absurd h (by simp)
  | cons t' rest ih =>
      cases h with
      | head => rw [forestCode_cons]; exact Nat.le_max_left _ _
      | tail _ h' =>
          have := ih h'
          rw [forestCode_cons]
          omega

/-- **Progress.**  Every child of a table expansion that starts at the same input
position has strictly smaller rank. -/
def Table.Progressing (G : Grammar T N) (M : Table T N) (w : N → Nat) : Prop :=
  ∀ (A : N) (x : LTok T) (rhs : List (Sym T N)), M.get A x = some rhs →
    ∀ (pre : List (Tree T N)) (t : Tree T N) (post : List (Tree T N))
      (ws rest : List T) (B : N),
      MatchList G rhs (pre ++ t :: post) →
        Tree.yieldForest (pre ++ t :: post) = ws →
          (∀ u, u ∈ pre → Tree.yield u = []) →
            t.root? = some B →
              lookaheadOf (ws ++ rest) = x → w B < w A

/-- A *non-consuming cycle* is a nonterminal that re-derives itself in one or more
steps. -/
def DerivesPlus (G : Grammar T N) (xs ys : List (Sym T N)) : Prop :=
  ∃ zs, Derives G xs zs ∧ Derives1 G zs ys

/-- Grammars without non-consuming self-derivations. -/
def cycleFree (G : Grammar T N) : Prop :=
  ∀ A, ¬ DerivesPlus G [Sym.var A] [Sym.var A]

end Progress

section Monotone

open Parser

/-- The terminal case of `parseSym` does not depend on the fuel. -/
theorem parseSym_tok_fuel {a : T} {input : List (LTok T)} {f f' : Nat} :
    parseSym M f (Sym.tok a) input = parseSym M f' (Sym.tok a) input := by
  cases input with
  | nil => simp [parseSym]
  | cons x xs =>
      cases x with
      | eof => simp [parseSym]
      | tok b => rw [parseSym_terminal, parseSym_terminal]

/-- Parsing the empty symbol list does not depend on the fuel (as long as there is
some). -/
theorem parseForest_nil_fuel {input : List (LTok T)} {f f' : Nat} :
    parseForest M (f + 1) [] input = parseForest M (f' + 1) [] input := rfl

/-- More fuel never hurts a successful parse: both statements are proved together by
induction on the available fuel. -/
theorem monotone : ∀ fuel : Nat,
    (∀ (fuel' : Nat) (s : Sym T N) (input : List (LTok T)) (t : Tree T N)
        (rest : List (LTok T)),
        parseSym M fuel s input = PRes.ok t rest → fuel ≤ fuel' →
          parseSym M fuel' s input = PRes.ok t rest) ∧
      (∀ (fuel' : Nat) (syms : List (Sym T N)) (input : List (LTok T))
          (ts : List (Tree T N)) (rest : List (LTok T)),
          parseForest M fuel syms input = PRes.ok ts rest → fuel ≤ fuel' →
            parseForest M fuel' syms input = PRes.ok ts rest) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro fuel' s input t rest h hle
        cases s with
        | tok a =>
            rw [parseSym_tok_fuel (a := a) (input := input) (f := fuel') (f' := 0)]
            exact h
        | var A => exact absurd h (by simp [parseSym])
      · intro fuel' syms input ts rest h hle
        cases syms with
        | nil => exact absurd h (by simp [parseForest])
        | cons s ss => exact absurd h (by simp [parseForest])
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · intro fuel' s input t rest h hle
        cases s with
        | tok a =>
            rw [parseSym_tok_fuel (a := a) (input := input) (f := fuel') (f' := fuel + 1)]
            exact h
        | var A =>
            cases fuel' with
            | zero => exact absurd hle (by omega)
            | succ k =>
                cases input with
                | nil => exact absurd h (by simp [parseSym])
                | cons x xs =>
                    rw [parseSym_var] at h
                    cases hget : M.get A x with
                    | none => rw [hget] at h; exact absurd h (by simp)
                    | some rhs =>
                        simp only [hget] at h
                        cases hfor : parseForest M fuel rhs (x :: xs) with
                        | ok ts' rest' =>
                            rw [hfor] at h
                            obtain ⟨h1, h2⟩ := PRes.ok.inj h
                            have h3 : parseForest M k rhs (x :: xs) = PRes.ok ts' rest' :=
                              ih.2 k rhs (x :: xs) ts' rest' hfor (by omega)
                            rw [parseSym_var]
                            simp only [hget, h3]
                            rw [h1, h2]
                        | error e => rw [hfor] at h; exact absurd h (by simp)
      · intro fuel' syms input ts rest h hle
        cases syms with
        | nil =>
            cases fuel' with
            | zero => exact absurd hle (by omega)
            | succ k =>
                rw [parseForest_nil_fuel (input := input) (f := k) (f' := fuel)]
                exact h
        | cons s ss =>
            cases fuel' with
            | zero => exact absurd hle (by omega)
            | succ fuel'' =>
                have hle' : fuel + 1 ≤ fuel'' + 1 := by omega
                have hcase : parseForest M (fuel + 1) (s :: ss) input =
                    pbind (parseSym M fuel s input) fun t rest' =>
                      pbind (parseForest M fuel ss rest') fun ts' rest'' =>
                        PRes.ok (t :: ts') rest'' := rfl
                have hcase' : parseForest M (fuel'' + 1) (s :: ss) input =
                    pbind (parseSym M fuel'' s input) fun t rest' =>
                      pbind (parseForest M fuel'' ss rest') fun ts' rest'' =>
                        PRes.ok (t :: ts') rest'' := rfl
                rw [hcase] at h
                obtain ⟨t, r1, ht, hfor⟩ := pbind_ok h
                obtain ⟨ts', r2, h1, h2⟩ := pbind_ok hfor
                cases h2
                have ht' := ih.1 fuel'' s input t r1 ht (by omega)
                have hf' := ih.2 fuel'' ss r1 ts' rest h1 (by omega)
                rw [hcase', ht']
                simp only [pbind]
                rw [hf']

theorem parseSym_mono (h : parseSym M fuel s input = PRes.ok t rest) (hle : fuel ≤ fuel') :
    parseSym M fuel' s input = PRes.ok t rest := (monotone fuel).1 fuel' s input t rest h hle

theorem parseForest_mono (h : parseForest M fuel syms input = PRes.ok ts rest)
    (hle : fuel ≤ fuel') : parseForest M fuel' syms input = PRes.ok ts rest :=
  (monotone fuel).2 fuel' syms input ts rest h hle

end Monotone

section Completeness

open Parser

theorem length_eq_zero_nil {l : List α} (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a as => exact absurd h (by simp)

theorem length_pos_of_ne_nil {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => simp

/-- The lookahead of a token stream built from two words. -/
theorem headD_ltoks_append (ws vs : List T) :
    (ltoks ws ++ ltoks vs ++ [LTok.eof]).headD LTok.eof = lookaheadOf (ws ++ vs) := by
  cases ws with
  | nil =>
      cases vs with
      | nil => simp [lookaheadOf]
      | cons b rest => simp [ltoks_cons]
  | cons a rest => simp [ltoks_cons]

theorem ltoks_append_eof_ne_nil (ws vs : List T) :
    (ltoks ws ++ ltoks vs ++ [LTok.eof]) ≠ [] := by
  cases ws with
  | nil =>
      cases vs with
      | nil => exact List.cons_ne_nil _ _
      | cons b rest => simp [ltoks_cons]
  | cons a rest => simp [ltoks_cons]

/-- The unfolding of `parseSym` at a nonterminal, phrased with the lookahead taken
out of the input stream with `headD` instead of by pattern matching: the input is
often presented as a concatenation and is not syntactically a cons cell. -/
theorem parseSym_var_lookahead {A : N} (input : List (LTok T)) (x : LTok T)
    (hhd : input.headD LTok.eof = x) {rhs : List (Sym T N)}
    (hget : M.get A x = some rhs) (hne : input ≠ []) (fuel : Nat) :
    parseSym M (fuel + 1) (Sym.var A) input =
      match parseForest M fuel rhs input with
      | PRes.ok ts rest => PRes.ok (Tree.node A ts) rest
      | PRes.error e => PRes.error e := by
  cases input with
  | nil => exact absurd hne (by simp)
  | cons y ys =>
      simp only [List.headD_cons] at hhd
      subst hhd
      rw [parseSym_var, hget]
      rfl

/-- Splitting a matched forest along its head symbol. -/
theorem MatchList.cons_inv {s : Sym T N} {ss : List (Sym T N)} {ts : List (Tree T N)}
    (h : MatchList G (s :: ss) ts) :
    ∃ t rest, ts = t :: rest ∧ MatchList G [s] [t] ∧ MatchList G ss rest := by
  cases s with
  | tok a =>
      obtain ⟨ts', rfl, hrest⟩ := MatchList.eq_leaf_cons h
      exact ⟨Tree.leaf a, ts', rfl, MatchList.tok MatchList.nil, hrest⟩
  | var A =>
      obtain ⟨ts', rhs, rest, rfl, hp, hchild, hrest⟩ := MatchList.eq_node_cons h
      exact ⟨Tree.node A ts', rest, rfl, MatchList.var hp hchild MatchList.nil, hrest⟩

theorem yield_le_yieldForest {ts : List (Tree T N)} {t} (h : t ∈ ts) :
    (Tree.yield t).length ≤ (Tree.yieldForest ts).length := by
  induction ts with
  | nil => exact absurd h (by simp)
  | cons t' rest ih =>
      cases h with
      | head => simp [Tree.yieldForest_cons, Nat.le_add_right]
      | tail _ h' =>
          have := ih h'
          simp [Tree.yieldForest_cons]
          omega

theorem exists_append_cons {as : List (Tree T N)} {a : Tree T N} (h : a ∈ as) :
    ∃ bs cs, as = bs ++ a :: cs := by
  induction as with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
      cases h with
      | head => exact ⟨[], bs, rfl⟩
      | tail _ h' =>
          obtain ⟨bs', cs', heq⟩ := ih h'
          exact ⟨b :: bs', cs', by rw [heq]; rfl⟩

theorem forestCode_lt (K : Nat) (w : N → Nat) {ts : List (Tree T N)} {ν : Nat}
    (hpos : 0 < ν) (h : ∀ t ∈ ts, nodeCode K w t < ν) : forestCode K w ts < ν := by
  induction ts with
  | nil => simpa [forestCode_nil] using hpos
  | cons t' rest ih =>
      rw [forestCode_cons]
      exact Nat.max_lt.mpr ⟨h t' (List.Mem.head _),
        ih (fun x hx => h x (List.Mem.tail _ hx))⟩

/-- **The rank decreases.**  Each child of a table expansion has strictly smaller rank
than the node it replaces: either a preceding sibling consumed a token (so the length
component drops) or `Progressing` lowers the rank component. -/
theorem nodeCode_child (hw : Table.Progressing G M w) (hK : ∀ A, w A ≤ K)
    {A : N} {x : LTok T} {rhs ts'' ws rest : _}
    (hget : M.get A x = some rhs) (hmatch : MatchList G rhs ts'')
    (hyield : Tree.yieldForest ts'' = ws) (hx : lookaheadOf (ws ++ rest) = x) :
    ∀ t ∈ ts'', nodeCode K w t < ws.length * (K + 1) + w A + 1 := by
  intro t ht
  obtain ⟨pre, post, heq⟩ := exists_append_cons ht
  subst heq
  have hlen : ws.length = (Tree.yieldForest pre).length + (Tree.yield t).length
      + (Tree.yieldForest post).length := by
    rw [← hyield]
    simp [Tree.yieldForest_append]
    omega
  have hmem : t ∈ pre ++ t :: post := List.mem_append.mpr (Or.inr (List.Mem.head _))
  have hle : (Tree.yield t).length ≤ ws.length := by
    have := yield_le_yieldForest hmem
    rwa [hyield] at this
  cases t with
  | leaf a =>
      -- a leaf has rank `0`, which is below every node rank
      rw [nodeCode_leaf]
      exact Nat.zero_lt_succ _
  | node B us =>
      have hB : w B ≤ K := hK B
      have hroot : (Tree.node B us).root? = some B := by simp [Tree.root?]
      have hn : nodeCode K w (Tree.node B us) =
          (Tree.yield (Tree.node B us)).length * (K + 1) + w B + 1 :=
        nodeCode_node K w B us
      have hlenChild : (Tree.yield (Tree.node B us)).length ≤ ws.length := hle
      rw [hn]
      by_cases hpre : Tree.yieldForest pre = []
      · -- every preceding sibling yields ε, so `Progressing` lowers the rank component
        have hall : ∀ u, u ∈ pre → Tree.yield u = [] := by
          intro u hu
          have hlenU : (Tree.yield u).length ≤ (Tree.yieldForest pre).length :=
            yield_le_yieldForest hu
          rw [hpre] at hlenU
          simp at hlenU
          exact hlenU
        have hlist : MatchList G rhs (pre ++ Tree.node B us :: post) := hmatch
        have hyf : Tree.yieldForest (pre ++ Tree.node B us :: post) = ws := by
          simpa [Tree.yieldForest_append, hpre] using hyield
        have hw' := hw A x rhs hget pre (Tree.node B us) post ws rest B hlist hyf hall hroot hx
        have hmul : (Tree.yield (Tree.node B us)).length * (K + 1) ≤ ws.length * (K + 1) :=
          Nat.mul_le_mul hlenChild (Nat.le_refl (K + 1))
        omega
      · -- some preceding sibling consumed a token, so the length component drops
        have hpos : 0 < (Tree.yieldForest pre).length := length_pos_of_ne_nil hpre
        have hlt : (Tree.yield (Tree.node B us)).length ≤ ws.length - 1 := by omega
        have hmul : (Tree.yield (Tree.node B us)).length * (K + 1) ≤ (ws.length - 1) * (K + 1) :=
          Nat.mul_le_mul hlt (Nat.le_refl (K + 1))
        have hdecomp : ws.length * (K + 1) = (ws.length - 1) * (K + 1) + (K + 1) := by
          have hcancel : ws.length - 1 + 1 = ws.length := by omega
          rw [← hcancel, Nat.add_mul]
          simp [Nat.one_mul]
        have hK1 : 1 ≤ K + 1 := by omega
        have hwb : w B + 1 ≤ K + 1 := by omega
        omega

/-- **The core completeness argument.**  The symbol statement and the forest
statement are mutually dependent: expanding a symbol produces a forest, and parsing a
forest recurses into symbols.  The symbol part is obtained by strong induction on the
rank bound, and the forest part by induction on the symbol list at the *same* bound
(the tail does not decrease the bound, only its length). -/
theorem complete_core (hM : M.Correct G) {w : N → Nat} (hw : Table.Progressing G M w)
    {K : Nat} (hK : ∀ A, w A ≤ K) : ∀ (μ : Nat),
      (∀ (s : Sym T N) (t : Tree T N) (ws rest : List T),
          MatchList G [s] [t] → Tree.yield t = ws → nodeCode K w t < μ →
            ∃ fuel t', parseSym M fuel s (ltoks ws ++ ltoks rest ++ [LTok.eof]) =
              PRes.ok t' (ltoks rest ++ [LTok.eof]) ∧ Tree.yield t' = ws) ∧
        (∀ (syms : List (Sym T N)) (ts : List (Tree T N)) (ws rest : List T),
          MatchList G syms ts → Tree.yieldForest ts = ws → forestCode K w ts < μ →
            ∃ fuel ts', parseForest M fuel syms (ltoks ws ++ ltoks rest ++ [LTok.eof]) =
              PRes.ok ts' (ltoks rest ++ [LTok.eof]) ∧ Tree.yieldForest ts' = ws) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | ind μ ih =>
      -- the symbol statement at bound μ
      have symStmt : ∀ (s : Sym T N) (t : Tree T N) (ws rest : List T),
          MatchList G [s] [t] → Tree.yield t = ws → nodeCode K w t < μ →
            ∃ fuel t', parseSym M fuel s (ltoks ws ++ ltoks rest ++ [LTok.eof]) =
              PRes.ok t' (ltoks rest ++ [LTok.eof]) ∧ Tree.yield t' = ws := by
        intro s t ws rest hone hyt hcode
        cases s with
        | tok a =>
            obtain ⟨ts', ht, hrest⟩ := MatchList.eq_leaf_cons hone
            obtain ⟨h1, h2⟩ := List.cons.inj ht
            subst h1
            subst h2
            have hws : ws = [a] := by simpa [Tree.yield_leaf] using hyt.symm
            subst hws
            refine ⟨0, Tree.leaf a, ?_, Tree.yield_leaf a⟩
            have hinp : ltoks [a] ++ ltoks rest ++ [LTok.eof] =
                LTok.tok a :: (ltoks rest ++ [LTok.eof]) := rfl
            rw [hinp, parseSym_terminal]
            simp
        | var A =>
            obtain ⟨tsA, rhs, r, ht, hp, hchild, hr⟩ := MatchList.eq_node_cons hone
            obtain ⟨h1, h2⟩ := List.cons.inj ht
            subst h1
            subst h2
            have hws : Tree.yieldForest tsA = ws := by simpa [Tree.yield_node] using hyt
            have hder : Derives G rhs (toks ws) := by
              have := matchList_derives hchild
              rwa [hws] at this
            have hpremise : ∃ rhs', (A, rhs') ∈ G.productions ∧
                Derives G (rhs' ++ toks rest) (toks (ws ++ rest)) := by
              refine ⟨rhs, hp, ?_⟩
              rw [toks_append]
              exact derives_ctx hder [] (toks rest)
            obtain ⟨rhs', hget, hder'⟩ := hM.2.2 A (toks rest) ws rest hpremise
            obtain ⟨ts'', hmatch'', hyield''⟩ :=
              substitute hder' (MatchList.match_toks (ws ++ rest))
            obtain ⟨t1, t2, het, hmatch1, hmatch2⟩ :=
              MatchList.split rhs' (toks rest) ts'' hmatch''
            have ht2 : t2 = rest.map Tree.leaf := MatchList.match_toks_unique hmatch2
            have hy1 : Tree.yieldForest t1 = ws := by
              have hstep : Tree.yieldForest t1 ++ rest = ws ++ rest := by
                have := hyield''
                rw [het, Tree.yieldForest_append, ht2] at this
                simp only [Tree.yieldForest_map_leaf] at this
                exact this
              exact (List.append_left_inj rest).mp hstep
            have hn : nodeCode K w (Tree.node A tsA) = ws.length * (K + 1) + w A + 1 := by
              rw [nodeCode_node, Tree.yield_node, hws]
            have hcode1 : forestCode K w t1 < nodeCode K w (Tree.node A tsA) := by
              refine forestCode_lt K w (by rw [hn]; omega) (fun t ht' => ?_)
              rw [hn]
              exact nodeCode_child hw hK hget hmatch1 hy1 rfl t ht'
            obtain ⟨fuel, ts''', hrun, hy3⟩ :=
              (ih (nodeCode K w (Tree.node A tsA))
                (by simpa using hcode)).2 rhs' t1 ws rest hmatch1 hy1 hcode1
            refine ⟨fuel + 1, Tree.node A ts''', ?_, by simpa [Tree.yield_node] using hy3⟩
            rw [parseSym_var_lookahead (ltoks ws ++ ltoks rest ++ [LTok.eof])
              (lookaheadOf (ws ++ rest)) (headD_ltoks_append ws rest) hget
              (ltoks_append_eof_ne_nil ws rest) fuel]
            rw [hrun]
      -- the forest statement at bound μ, by induction on the symbol list
      have forestStmt : ∀ (syms : List (Sym T N)) (ts : List (Tree T N)) (ws rest : List T),
          MatchList G syms ts → Tree.yieldForest ts = ws → forestCode K w ts < μ →
            ∃ fuel ts', parseForest M fuel syms (ltoks ws ++ ltoks rest ++ [LTok.eof]) =
              PRes.ok ts' (ltoks rest ++ [LTok.eof]) ∧ Tree.yieldForest ts' = ws := by
        intro syms
        induction syms with
        | nil =>
            intro ts ws rest hmatch hyield hcode
            have hnil : ts = [] := MatchList.eq_nil hmatch
            subst hnil
            have hws : ws = [] := by simpa using hyield
            subst hws
            refine ⟨1, [], ?_, rfl⟩
            simp [parseForest_nil]
        | cons s ss ihlist =>
            intro ts ws rest hmatch hyield hcode
            obtain ⟨t, trest, hts, hone, htail⟩ := MatchList.cons_inv hmatch
            subst hts
            have hy1 : Tree.yield t ++ Tree.yieldForest trest = ws := by
              rw [← hyield]
              simp [Tree.yieldForest_cons]
            have hcodeHead : nodeCode K w t < μ := by
              rw [forestCode_cons] at hcode
              omega
            obtain ⟨fuelH, t', hrunH, hyH⟩ :=
              symStmt s t (Tree.yield t) (Tree.yieldForest trest ++ rest) hone rfl hcodeHead
            have hcodeTail : forestCode K w trest < μ := by
              rw [forestCode_cons] at hcode
              omega
            obtain ⟨fuelT, ts'', hrunT, hyT⟩ :=
              ihlist trest (Tree.yieldForest trest) rest htail rfl hcodeTail
            have hrunH' : parseSym M fuelH s
                  (ltoks (Tree.yield t) ++ (ltoks (Tree.yieldForest trest) ++
                    (ltoks rest ++ [LTok.eof]))) =
                  PRes.ok t' (ltoks (Tree.yieldForest trest) ++ (ltoks rest ++ [LTok.eof])) := by
              simpa [ltoks_append] using hrunH
            have hrunT' : parseForest M fuelT ss
                  (ltoks (Tree.yieldForest trest) ++ (ltoks rest ++ [LTok.eof])) =
                  PRes.ok ts'' (ltoks rest ++ [LTok.eof]) := by
              simpa [ltoks_append] using hrunT
            have hH := parseSym_mono hrunH' (Nat.le_max_left fuelH fuelT)
            have hT := parseForest_mono hrunT' (Nat.le_max_right fuelH fuelT)
            refine ⟨max fuelH fuelT + 1, t' :: ts'', ?_, ?_⟩
            · have hinp : ltoks ws ++ ltoks rest ++ [LTok.eof] =
                  ltoks (Tree.yield t) ++ (ltoks (Tree.yieldForest trest) ++
                    (ltoks rest ++ [LTok.eof])) := by
                rw [← hy1]
                simp only [ltoks_append, List.append_assoc]
              rw [parseForest_cons, hinp, hH]
              simp only [pbind]
              rw [hT]
            · rw [Tree.yieldForest_cons, hyH, hyT]
              exact hy1
      exact ⟨symStmt, forestStmt⟩

/-- **Completeness.**  Every symbol list that has a matching forest — equivalently,
every sentential form deriving the remaining input — is accepted by the parser for a
suitable fuel. -/
theorem complete_of_match (hM : M.Correct G) {w : N → Nat} (hw : Table.Progressing G M w)
    {K : Nat} (hK : ∀ A, w A ≤ K) :
    ∀ (syms : List (Sym T N)) (ts : List (Tree T N)) (ws : List T),
      MatchList G syms ts → Tree.yieldForest ts = ws →
        ∃ (fuel : Nat) (ts' : List (Tree T N)),
          Parser.parseForest M fuel syms (ltoks ws ++ [LTok.eof]) =
            PRes.ok ts' [LTok.eof] ∧ Tree.yieldForest ts' = ws := by
  intro syms ts ws hmatch hyield
  obtain ⟨fuel, ts', hrun, hy⟩ :=
    (complete_core hM hw hK (forestCode K w ts + 1)).2 syms ts ws [] hmatch hyield
      (Nat.lt_succ_self _)
  have hrun' : Parser.parseForest M fuel syms (ltoks ws ++ [LTok.eof]) =
      PRes.ok ts' [LTok.eof] := by
    simpa [ltoks_nil] using hrun
  exact ⟨fuel, ts', hrun', hy⟩

end Completeness

section Acceptance

variable {T : Type u} {N : Type v} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N]
  {M : Table T N} {G : Grammar T N}

/-- **Acceptance of every generated token sequence.**  If `ws` is a word of the
language of `G` and `M` is a correct, progressing table for `G`, then the parser
accepts `ws` for some fuel, and the tree it builds is a valid parse tree of `G` with
yield exactly `ws`. -/
theorem language_imp_accepts (hM : M.Correct G) {w : N → Nat}
    (hw : Table.Progressing G M w) {K : Nat} (hK : ∀ A, w A ≤ K) {ws : List T}
    (h : G.language ws) :
    ∃ fuel t, Parser.parse G M fuel (ltoks ws ++ [LTok.eof]) = PRes.ok t [LTok.eof] ∧
      Valid G t ∧ Tree.yield t = ws := by
  obtain ⟨ts, hv, hy⟩ := G.language_iff_tree ws |>.mp h
  obtain ⟨rhs, hp, hm⟩ := hv
  obtain ⟨fuel, ts', hrun, hyield⟩ :=
    complete_of_match hM hw hK [Sym.var G.start] [Tree.node G.start ts] ws
      (MatchList.var hp hm MatchList.nil)
      (by simp [Tree.yieldForest_cons, hy])
  -- Soundness pins down the *shape* of the forest the parser returned: a one-symbol
  -- list is matched only by a one-tree forest.
  obtain ⟨hmatch', _⟩ :=
    parseForest_sound hM.1 fuel [Sym.var G.start] (ltoks ws ++ [LTok.eof]) ts' [LTok.eof] hrun
  obtain ⟨t', rhs', r, ht, hp', hchild', hr⟩ := MatchList.eq_node_cons hmatch'
  have hr' : r = [] := MatchList.eq_nil hr
  subst hr'
  subst ht
  have hparse : Parser.parse G M fuel (ltoks ws ++ [LTok.eof]) =
      PRes.ok (Tree.node G.start t') [LTok.eof] := by
    simp [Parser.parse, hrun]
  refine ⟨fuel, Tree.node G.start t', hparse, Valid.mk hp' hchild', ?_⟩
  simpa [Tree.yield_node, Tree.yieldForest_cons, Tree.yieldForest_nil, List.append_nil]
    using hyield

/-- **Rejection: no false accepts.**  For *any* table, if the parser accepts then the
input is a word of the language.  Only `Table.Sound` is used. -/
theorem parse_ok_imp_language (hM : M.Sound G) {fuel : Nat} {input : List (LTok T)}
    {t : Tree T N} (h : Parser.parse G M fuel input = PRes.ok t [LTok.eof]) :
    G.language (tokensOf input) := by
  obtain ⟨hcall, _⟩ := parse_ok h
  obtain ⟨hmatch, hyield⟩ :=
    parseForest_sound hM fuel [Sym.var G.start] input [t] [LTok.eof] hcall
  obtain ⟨ts', rhs, r, ht, hp, hchild, hr⟩ := MatchList.eq_node_cons hmatch
  obtain ⟨h1, h2⟩ := List.cons.inj ht
  subst h1
  subst h2
  have hvalid : Valid G (Tree.node G.start ts') := Valid.mk hp hchild
  have hy : Tree.yield (Tree.node G.start ts') = tokensOf input := by
    apply Eq.symm
    simpa using hyield
  exact tree_iff_derives.mp ⟨ts', hvalid, hy⟩

/-- A word outside the language is rejected at *every* fuel value. -/
theorem never_accepts_of_not_language (hM : M.Sound G) {ws : List T}
    (h : ¬ G.language ws) :
    ∀ fuel t, Parser.parse G M fuel (ltoks ws ++ [LTok.eof]) ≠ PRes.ok t [LTok.eof] := by
  intro fuel t hok
  have h' : G.language ws := by
    simpa [tokensOf_ltoks] using parse_ok_imp_language hM hok
  exact h h'

/-- Acceptance of a well-formed stream consumes exactly its token word: nothing else
can be accepted. -/
theorem parse_ok_imp_shape (hM : M.Sound G) {fuel : Nat} {input : List (LTok T)}
    {t : Tree T N} (hwf : WellFormedInput input)
    (h : Parser.parse G M fuel input = PRes.ok t [LTok.eof]) :
    Tree.yield t = tokensOf input := (parse_sound hM hwf h).2

/-- **The two-sided characterisation.**  With a correct, progressing table the parser
accepts *exactly* the language of the grammar. -/
theorem language_iff_accepts (hM : M.Correct G) {w : N → Nat}
    (hw : Table.Progressing G M w) {K : Nat} (hK : ∀ A, w A ≤ K) {ws : List T} :
    G.language ws ↔
      ∃ fuel t, Parser.parse G M fuel (ltoks ws ++ [LTok.eof]) = PRes.ok t [LTok.eof] :=
  Iff.intro
    (fun h => by
      obtain ⟨fuel, t, hok, _, _⟩ := language_imp_accepts hM hw hK h
      exact ⟨fuel, t, hok⟩)
    (fun ⟨_, _, hok⟩ => by
      have h' : G.language (tokensOf (ltoks ws ++ [LTok.eof])) := parse_ok_imp_language hM.1 hok
      simpa [tokensOf_ltoks] using h')

end Acceptance

end VerifiedLL1
