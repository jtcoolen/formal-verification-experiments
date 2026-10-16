/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import Init

/-!
# Phase 1.1 — Context-free grammars

This module holds the *algorithm-independent* mathematical specification of a
context-free grammar.  Nothing here knows about parsing, predictive tables,
`FIRST`/`FOLLOW`, or any other implementation concern; the later modules are
always stated *against* the definitions of this module, which is what keeps the
correctness theorems semantic rather than self-referential.

## Design notes

* The terminal alphabet `T` and the nonterminal alphabet `N` are arbitrary
  types.  A grammar carries a **finite list** of productions, so every
  construction in this development inspects only finitely many symbols.  Where a
  phase genuinely needs to enumerate an entire alphabet (the fixed-point
  iterations of Phase 4) we ask for the explicit class `FiniteEnum` and carry the
  enumeration as data.  Keeping `Grammar` free of typeclass fields keeps the
  semantic theorems clean.
* A production is a pair `(A, rhs)` with `rhs : List (Sym T N)`.  An *epsilon
  production* is a production with `rhs = []`; there is no separate syntactic
  `ε` constructor, so no well-formedness side condition is needed to stop `ε`
  from appearing beside other symbols.
* Sentential forms are plain `List (Sym T N)`: no length indices, no quotienting.
-/

universe u v

namespace VerifiedLL1

/-- A grammar symbol: either a terminal token or a nonterminal variable. -/
inductive Sym (T : Type u) (N : Type v) where
  | tok : T → Sym T N
  | var : N → Sym T N
  deriving DecidableEq, Repr

/-- A context-free grammar: a finite list of productions together with a
designated start symbol.  A production `(A, [])` is an epsilon production. -/
structure Grammar (T : Type u) (N : Type v) where
  /-- The productions, as pairs `(left-hand side, right-hand side)`. -/
  productions : List (N × List (Sym T N))
  /-- The start symbol. -/
  start : N

namespace Sym

variable {T : Type u} {N : Type v}

/-- Is the symbol a nonterminal? -/
def isVar : Sym T N → Bool
  | var _ => true
  | tok _ => false

/-- Is the symbol a terminal? -/
def isTok : Sym T N → Bool
  | var _ => false
  | tok _ => true

/-- The nonterminal of a symbol, if it has one. -/
def var? : Sym T N → Option N
  | var A => some A
  | tok _ => none

/-- The terminal of a symbol, if it has one. -/
def tok? : Sym T N → Option T
  | tok t => some t
  | var _ => none

@[simp] theorem isVar_var (A) : (var A : Sym T N).isVar = true := rfl
@[simp] theorem isVar_tok (t) : (tok t : Sym T N).isVar = false := rfl
@[simp] theorem isTok_var (A) : (var A : Sym T N).isTok = false := rfl
@[simp] theorem isTok_tok (t) : (tok t : Sym T N).isTok = true := rfl

theorem isTok_eq_not_isVar (s : Sym T N) : s.isTok = !s.isVar := by
  cases s <;> rfl

theorem ne_tok_var (t : T) (A : N) : Sym.tok t ≠ Sym.var A := by
  intro h
  have := congrArg Sym.isVar h
  simp at this

theorem ne_var_tok (A : N) (t : T) : Sym.var A ≠ Sym.tok t := by
  intro h; exact Sym.ne_tok_var t A h.symm

@[simp] theorem var?_some : (var A : Sym T N).var? = some A := rfl
@[simp] theorem var?_none (t) : (tok t : Sym T N).var? = none := rfl
@[simp] theorem tok?_some : (tok t : Sym T N).tok? = some t := rfl
@[simp] theorem tok?_none (A) : (var A : Sym T N).tok? = none := rfl

end Sym

/-- A terminal word, viewed as a sentential form all of whose symbols are
terminals. -/
def toks {T : Type u} {N : Type v} (ws : List T) : List (Sym T N) := ws.map Sym.tok

/-- `toks` preserves concatenation. -/
@[simp] theorem toks_append {T : Type u} {N : Type v} (ws vs : List T) :
    @toks T N (ws ++ vs) = @toks T N ws ++ @toks T N vs := List.map_append

/-- Terminal words are faithfully embedded into sentential forms. -/
theorem toks_inj {T : Type u} {N : Type v} :
    ∀ {ws vs : List T}, @toks T N ws = @toks T N vs → ws = vs := by
  intro ws
  induction ws with
  | nil =>
      intro vs h
      cases vs with
      | nil => rfl
      | cons v rest => exact absurd h (by simp [toks])
  | cons w rest ih =>
      intro vs h
      cases vs with
      | nil => exact absurd h (by simp [toks])
      | cons v rest' =>
          have hw : w = v := Sym.tok.inj (List.cons.inj h).1
          have hrest : rest = rest' := ih (List.cons.inj h).2
          exact by rw [hw, hrest]

namespace Grammar

variable {T : Type u} {N : Type v}

/-- The right-hand sides of all productions whose left-hand side is `A`. -/
def rhsOf [BEq N] (G : Grammar T N) (A : N) : List (List (Sym T N)) :=
  (G.productions.filter fun p => p.1 == A).map Prod.snd

theorem mem_rhsOf [BEq N] [LawfulBEq N] {G : Grammar T N} {A : N} {rhs : List (Sym T N)} :
    rhs ∈ G.rhsOf A ↔ (A, rhs) ∈ G.productions := by
  constructor
  · intro h
    simp only [rhsOf, List.mem_map, List.mem_filter] at h
    obtain ⟨p, ⟨hp, hbeq⟩, hEq⟩ := h
    obtain ⟨A', rhs'⟩ := p
    have hA : A' = A := eq_of_beq hbeq
    subst hEq; subst hA
    exact hp
  · intro h
    simp only [rhsOf, List.mem_map, List.mem_filter]
    exact ⟨(A, rhs), ⟨h, by simp⟩, rfl⟩

/-- `A` has at least one production. -/
def hasProduction (G : Grammar T N) (A : N) : Prop := ∃ rhs, (A, rhs) ∈ G.productions

/-- `A` is *erasable* — deferred to `Nullable.lean`; this is only the syntactic
predicate "some production of `A` is empty". -/
def hasEpsilonProduction (G : Grammar T N) (A : N) : Prop := (A, []) ∈ G.productions

/-- The nonterminals that occur as some left-hand side, without duplicates. -/
def nonterminals [BEq N] (G : Grammar T N) : List N := (G.productions.map Prod.fst).eraseDups

theorem mem_nonterminals [BEq N] [LawfulBEq N] {G : Grammar T N} {A : N} :
    A ∈ G.nonterminals ↔ G.hasProduction A := by
  simp only [nonterminals, hasProduction, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨p, hp, hEq⟩; exact ⟨p.2, hEq ▸ hp⟩
  · rintro ⟨rhs, h⟩; exact ⟨(A, rhs), h, rfl⟩

/-- The terminals that occur somewhere on a right-hand side, without duplicates. -/
def terminals [BEq T] (G : Grammar T N) : List T :=
  ((G.productions.map Prod.snd).flatMap (·.filterMap Sym.tok?)).eraseDups

/-- Every nonterminal mentioned on a right-hand side has a production, and so
does the start symbol.  This is the standing well-formedness assumption of the
development: it rules out grammars that reference an undefined variable, which
would otherwise make `Valid` unsatisfiable in a way a parser could not
distinguish from a syntax error. -/
def wellFormed (G : Grammar T N) : Prop :=
  G.hasProduction G.start ∧
    ∀ A rhs, (A, rhs) ∈ G.productions →
      ∀ s ∈ rhs, ∀ B, s = Sym.var B → G.hasProduction B

theorem wellFormed.start {G : Grammar T N} (h : G.wellFormed) : G.hasProduction G.start := h.1

theorem wellFormed.ref {G : Grammar T N} (h : G.wellFormed)
    {A rhs} (hp : (A, rhs) ∈ G.productions) {s} (hs : s ∈ rhs) {B} (hB : s = Sym.var B) :
    G.hasProduction B := h.2 A rhs hp s hs B hB

end Grammar

/-- `FiniteEnum α` packages an *explicit* list of all elements of `α`.

This is the finiteness notion used by the executable analyses: a fixed-point
iteration over `α` is only computable if `α` can be enumerated, and we prefer to
carry that enumeration as data rather than let typeclass synthesis build an
exponential search space. -/
class FiniteEnum (α : Type) where
  /-- A list containing every element of `α`. -/
  elems : List α
  /-- `elems` really is exhaustive. -/
  complete : ∀ a : α, a ∈ elems

/-- The symbol type over two finite enumerations is finite. -/
instance (priority := 100) Sym.finiteEnum [FiniteEnum T] [FiniteEnum N] : FiniteEnum (Sym T N) where
  elems := (FiniteEnum.elems (α := T)).map Sym.tok ++ (FiniteEnum.elems (α := N)).map Sym.var
  complete := by
    intro s
    cases s with
    | tok t =>
        refine List.mem_append.mpr (Or.inl ?_)
        exact List.mem_map.mpr ⟨_, FiniteEnum.complete t, rfl⟩
    | var A =>
        refine List.mem_append.mpr (Or.inr ?_)
        exact List.mem_map.mpr ⟨_, FiniteEnum.complete A, rfl⟩

end VerifiedLL1
