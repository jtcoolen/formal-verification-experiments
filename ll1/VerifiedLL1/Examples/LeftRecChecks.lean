/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.LeftRec
import VerifiedLL1.Examples.Toy

/-!
# Phase 5.2 examples — the hypotheses of noLeftRecursion_of_ll1 are necessary,
# and the theorem applied to a real grammar

Three small grammars:

* LeftRecUnreachable — an unreachable left-recursive component  U -> U | ε  beside the
  start production  S -> s.  The LL(1) check passes and the left-recursion check fails:
  Reduced.1 (has a production implies occurs) is what is missing.
* LeftRecUnproductive —  S -> S.  The LL(1) check passes and the left-recursion check
  fails: S occurs but is not productive, so Reduced.2 is what is missing.
* Examples.Toy.G — the worked example of Phase 1/4/5, proved *reduced* here, so that
  its  noLeftRecursion = true  follows from Ll1 through the new theorem instead of by
  decide.
-/

namespace VerifiedLL1.Examples
namespace LeftRecUnreachable

/-- The terminal alphabet of the unreachable-component example. -/
inductive Tok where
  | s
  deriving DecidableEq, Repr

/-- The nonterminal alphabet: a start symbol and an unreachable left-recursive one. -/
inductive Var where
  | S
  | U
  deriving DecidableEq, Repr

open Tok Var Sym

instance : FiniteEnum Tok where
  elems := [s]
  complete := by
    intro x
    cases x <;> simp

instance : FiniteEnum Var where
  elems := [S, U]
  complete := by
    intro x
    cases x <;> simp

/-- The grammar

    S -> s
    U -> U
    U -> ε

The component U is left-recursive but unreachable: no sentential form contains it. -/
def G : Grammar Tok Var where
  productions := [ (S, [tok s]), (U, [var U]), (U, []) ]
  start := S

theorem mem_Ss : (S, [tok s]) ∈ G.productions := List.Mem.head _
theorem mem_UU : (U, [var U]) ∈ G.productions := List.Mem.tail _ (List.Mem.head _)
theorem mem_Ue : (U, []) ∈ G.productions :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- U is a left corner of itself. -/
theorem leftCorner_UU : G.LeftCorner U U := ⟨[], [], mem_UU, derives_refl []⟩

/-- The only sentential forms of G are [var S] and [tok s]. -/
theorem forms : ∀ ys, Derives G [Sym.var S] ys → ys = [Sym.var S] ∨ ys = [Sym.tok s] := by
  intro ys h
  induction h with
  | refl => exact Or.inl rfl
  | @tail mid fin hrec hstep ih =>
      rcases ih with him | him
      · subst him
        obtain ⟨B, rhs, ctxL, ctxR, hp, e1, e2⟩ := derives1_decompose hstep
        have hL : ctxL = [] := by
          cases ctxL with
          | nil => rfl
          | cons a as =>
              have hlen := congrArg List.length e1
              simp at hlen
        subst hL
        rw [List.nil_append] at e1
        obtain ⟨hBS, hR⟩ := List.cons.inj e1
        subst hR
        cases hBS
        have hrhs : rhs = [Sym.tok s] := by
          simpa [G, List.mem_cons, Prod.mk.injEq] using hp
        subst hrhs
        exact Or.inr (by simpa using e2)
      · subst him
        right
        have hnov : ([Sym.tok s] : List (Sym Tok Var)) = fin :=
          derives1_noVar hstep (by
            intro x hx
            rw [List.mem_singleton] at hx
            subst hx
            simp)
        exact hnov.symm

/-- U occurs in no sentential form. -/
theorem not_occurs_U : ¬ G.Occurs U := by
  intro h
  obtain ⟨pre, post, hder⟩ := h
  have hmem : Sym.var U ∈ pre ++ [Sym.var U] ++ post := by simp
  rcases forms _ hder with heq | heq
  · rw [heq] at hmem
    exact absurd hmem (by decide)
  · rw [heq] at hmem
    exact absurd hmem (by decide)

/-- The grammar is LL(1): the conflicted component is unreachable, so it contributes no
lookahead at all. -/
theorem ll1 : G.ll1Check = true := by decide

/-- The grammar is *not* free of left recursion: U is a left corner of itself. -/
theorem leftrec : G.noLeftRecursion = false := by decide

/-- **Reduced.1 fails**, and with it the theorem's conclusion: U has a production but
does not occur. -/
theorem not_reduced_left : ¬ (∀ A, G.hasProduction A → G.Occurs A) :=
  fun h => not_occurs_U (h U ⟨[Sym.var U], mem_UU⟩)

/-- So G is not reduced. -/
theorem not_reduced : ¬ G.Reduced := fun h => not_reduced_left h.1

end LeftRecUnreachable

namespace LeftRecUnproductive

/-- The terminal alphabet of the unproductive example. -/
inductive Tok where
  | s
  deriving DecidableEq, Repr

/-- The nonterminal alphabet: one symbol. -/
inductive Var where
  | S
  deriving DecidableEq, Repr

open Tok Var Sym

instance : FiniteEnum Tok where
  elems := [s]
  complete := by
    intro x
    cases x <;> simp

instance : FiniteEnum Var where
  elems := [S]
  complete := by
    intro x
    cases x <;> simp

/-- The grammar

    S -> S

The start symbol occurs, but derives no terminal word at all. -/
def G : Grammar Tok Var where
  productions := [ (S, [var S]) ]
  start := S

theorem mem_SS : (S, [var S]) ∈ G.productions := List.Mem.head _

/-- S is a left corner of itself. -/
theorem leftCorner_SS : G.LeftCorner S S := ⟨[], [], mem_SS, derives_refl []⟩

/-- The only sentential form of G is [var S]. -/
theorem forms : ∀ ys, Derives G [Sym.var S] ys → ys = [Sym.var S] := by
  intro ys h
  induction h with
  | refl => rfl
  | @tail mid fin hrec hstep ih =>
      subst ih
      obtain ⟨B, rhs, ctxL, ctxR, hp, e1, e2⟩ := derives1_decompose hstep
      have hL : ctxL = [] := by
        cases ctxL with
        | nil => rfl
        | cons a as =>
            have hlen := congrArg List.length e1
            simp at hlen
      subst hL
      rw [List.nil_append] at e1
      obtain ⟨hBS, hR⟩ := List.cons.inj e1
      subst hR
      cases hBS
      have hrhs : rhs = [Sym.var S] := by
        simpa [G, List.mem_cons, Prod.mk.injEq] using hp
      subst hrhs
      simpa using e2

/-- S occurs: it is the start symbol. -/
theorem occurs_S : G.Occurs S := ⟨[], [], derives_refl _⟩

/-- **S is not productive**: no terminal word is derivable from it. -/
theorem not_productive : ¬ G.Productive S := by
  intro h
  obtain ⟨ws, hder⟩ := h
  have heq : toks ws = [Sym.var S] := forms _ hder
  cases ws with
  | nil => exact absurd heq (by simp [toks])
  | cons t rest =>
      simp only [toks, List.map_cons] at heq
      obtain ⟨h1, _⟩ := List.cons.inj heq
      exact Sym.ne_tok_var t S h1

/-- The grammar is LL(1) — vacuously, since no lookahead selects any production. -/
theorem ll1 : G.ll1Check = true := by decide

/-- The grammar is not free of left recursion. -/
theorem leftrec : G.noLeftRecursion = false := by decide

/-- **Reduced.2 fails**: S occurs but is not productive. -/
theorem not_reduced : ¬ G.Reduced := fun h => not_productive (h.2 S occurs_S)

end LeftRecUnproductive

namespace ToyReduced

/-- s is productive: s => a. -/
theorem productive_s : Examples.Toy.G.Productive Examples.Toy.Var.s :=
  ⟨[Examples.Toy.Tok.a], Examples.Toy.derives_a⟩

/-- p is productive: p => a. -/
theorem productive_p : Examples.Toy.G.Productive Examples.Toy.Var.p :=
  ⟨[Examples.Toy.Tok.a],
    derives_production Examples.Toy.Var.p [Sym.tok Examples.Toy.Tok.a] Examples.Toy.mem_pa⟩

/-- q is productive: q => ε. -/
theorem productive_q : Examples.Toy.G.Productive Examples.Toy.Var.q :=
  ⟨[], derives_production Examples.Toy.Var.q [] Examples.Toy.mem_qe⟩

/-- u has no production at all. -/
theorem no_prod_u : ¬ Examples.Toy.G.hasProduction Examples.Toy.Var.u := by
  intro h
  obtain ⟨rhs, hmem⟩ := h
  exact absurd hmem (by simp [Examples.Toy.G, List.mem_cons, Prod.mk.injEq])

/-- **The toy grammar is reduced**: s, p, q occur and are productive, and u — which is
mentioned in the alphabet but has no production — is excluded by the
occurs-from-has-a-production clause. -/
theorem toy_reduced : Examples.Toy.G.Reduced := by
  refine ⟨fun A hprod => ?_, fun A hocc => ?_⟩
  · cases A with
    | s => exact Examples.Toy.occurs_s
    | p => exact Examples.Toy.occurs_p
    | q => exact Examples.Toy.occurs_q
    | u => exact absurd hprod no_prod_u
  · cases A with
    | s => exact productive_s
    | p => exact productive_p
    | q => exact productive_q
    | u => exact absurd hocc Examples.Toy.not_occurs_u

/-- **The toy grammar is LL(1)** — the decidable check, transported to the predicate. -/
theorem toy_ll1_pred : Examples.Toy.G.Ll1 :=
  (Grammar.ll1Check_iff Examples.Toy.G).mp Examples.Toy.toy_ll1

/-- **End-to-end check.**  The toy grammar's left-recursion check now follows *from*
Ll1 and Reduced, rather than by evaluation: a real use of the new theorem. -/
theorem toy_no_left_recursion_from_ll1 : Examples.Toy.G.noLeftRecursion = true :=
  Grammar.noLeftRecursion_of_ll1 Examples.Toy.G toy_reduced toy_ll1_pred

end ToyReduced

end Examples

end VerifiedLL1