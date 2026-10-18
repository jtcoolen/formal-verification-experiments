/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Memo
import VerifiedLL1.Generator

/-!
# Phase 4.0c - the memoized form of every analysis

`Memo.lean` provides the backend, `Follow.lean` *uses* it for FOLLOW, and this module states
the memoized form of the remaining analyses together with the bridge that ties each of them
to the `Fixpoint.iterP` approximant the semantic proofs are written against.  Each bridge is
one line of `Memo.iterMemo_eq_iterP`; nothing here re-proves an analysis.

## Why only FOLLOW is switched on by default

The measurements in `README.md` (reproduce with `./bench5.sh`) are unambiguous about which
loop is worth tabulating:

* FOLLOW is asked at (nearly) every `(nonterminal, lookahead)` pair by `selectTest`, so the
  approximant is re-queried densely: memoizing it is worth 1.9x on the two circuit grammars
  and 3.3-5.3x on the scaled family.
* NULLABLE, REACH and FIRST are asked at few carrier points per decision, and the kernel's
  whnf cache already shares the closed terms `iterP P k`.  Tabulating their whole carrier at
  every round then costs more than it saves: on the scaled circuit family the fully memoized
  pipeline is about 2.3x *slower* than the shipped one, and FIRST over a 120-element carrier
  went from 0.41s to 2.82s.

So the memoized forms below are the API (proved identical, available to callers that query
densely), while the shipped computations stay on the representation that measures faster.
-/

set_option linter.unusedSectionVars false

universe u v

namespace VerifiedLL1

variable {T : Type u} {N : Type v}

section Nullable

variable [BEq N] [FiniteEnum N]

/-- The memoized form of NULLABLE. -/
def Grammar.nullableMemo (G : Grammar T N) (A : N) : Bool :=
  Memo.iterMemo (FiniteEnum.elems (α := N)) (nullableP G) G.nullableRounds A

end Nullable

section NullableBridges

variable [BEq N] [LawfulBEq N] [FiniteEnum N]

/-- The library's NULLABLE *is* the `iterP` approximant at the bound (definitionally). -/
theorem Grammar.nullable_eq_iterP (G : Grammar T N) (A : N) :
    G.nullable A = Fixpoint.iterP (nullableP G) G.nullableRounds A := rfl

/-- **Bridge:** the computed NULLABLE equals the memoized computation. -/
theorem Grammar.nullable_eq_iterMemo (G : Grammar T N) (A : N) :
    G.nullable A = G.nullableMemo A :=
  (Memo.iterMemo_eq_iterP (FiniteEnum.elems (α := N)) (nullableP G) FiniteEnum.complete
    G.nullableRounds A).symm

end NullableBridges

section Reach

variable [DecidableEq T] [DecidableEq N] [FiniteEnum N]

/-- The memoized form of REACH. -/
def Grammar.occursMemo (G : Grammar T N) (A : N) : Bool :=
  Memo.iterMemo (FiniteEnum.elems (α := N)) (occursP G) G.occursRounds A

theorem Grammar.occurs_eq_iterP (G : Grammar T N) (A : N) :
    G.occurs A = Fixpoint.iterP (occursP G) G.occursRounds A := rfl

end Reach

section ReachBridges

variable [DecidableEq T] [DecidableEq N] [LawfulBEq N] [FiniteEnum N]

/-- **Bridge:** the computed REACH equals the memoized computation. -/
theorem Grammar.occurs_eq_iterMemo (G : Grammar T N) (A : N) : G.occurs A = G.occursMemo A :=
  (Memo.iterMemo_eq_iterP (FiniteEnum.elems (α := N)) (occursP G) FiniteEnum.complete
    G.occursRounds A).symm

end ReachBridges

section First

variable [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- The memoized form of FIRST (over the library's NULLABLE). -/
def Grammar.firstMemo (G : Grammar T N) (s : Sym T N) (x : LTok T) : Bool :=
  Memo.iterMemo (FiniteEnum.elems (α := Sym T N × LTok T))
    (firstP G (firstNul G)) G.firstRounds (s, x)

theorem Grammar.first_eq_iterP (G : Grammar T N) (s : Sym T N) (x : LTok T) :
    G.first s x = Fixpoint.iterP (firstP G (firstNul G)) G.firstRounds (s, x) := rfl

end First

section FirstBridges

variable [DecidableEq T] [DecidableEq N] [LawfulBEq T] [LawfulBEq N]
  [FiniteEnum T] [FiniteEnum N]

/-- **Bridge:** the computed FIRST equals the memoized computation. -/
theorem Grammar.first_eq_iterMemo (G : Grammar T N) (s : Sym T N) (x : LTok T) :
    G.first s x = G.firstMemo s x :=
  (Memo.iterMemo_eq_iterP (FiniteEnum.elems (α := Sym T N × LTok T))
    (firstP G (firstNul G)) FiniteEnum.complete G.firstRounds (s, x)).symm

end FirstBridges

-- The left-corner closure (Grammar.lcReach) is *already* the memoized computation: the
-- definition, the bridge Grammar.lcReach_eq_iterP and the closure transfer all live in
-- Generator.lean next to the analysis they belong to.

end VerifiedLL1
