/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Memo
import VerifiedLL1.Generator
import VerifiedLL1.Examples.Toy
import VerifiedLL1.Examples.QCircuits

/-!
# Phase 4.0c - validation suite for the memoized backend

Every test here is discharged by the kernel ('decide', or a proof from the bridge
theorems), and each one is checked *against* 'Fixpoint.iterP' semantics rather than
against a hand-computed answer alone.

* zero rounds          - the all-false start, for an arbitrary transformer.
* immediate fixed point - a transformer that is already stable after one round; the early
  stop fires and the remaining fuel is ignored.
* duplicates           - a carrier with duplicate entries ('FiniteEnum' only promises
  exhaustiveness), including a duplicated carrier over the real Toy grammar.
* cycle                - a NULLABLE-shaped propagation cycle: a fact needs two rounds to
  travel around it.
* nonmonotone toggle   - 'P f x = !f x' on a one-element carrier, checked for several n:
  the memoized loop must reproduce the *exact* approximant, not a least fixed point.
* off-carrier          - the counterexample showing that 'hall' cannot be dropped.
* Toy bridges          - the bridge instantiated at the library's own analyses, plus
  'decide' smoke tests on the Toy grammar.
-/

set_option linter.unusedSectionVars false

namespace VerifiedLL1.MemoTest

open VerifiedLL1 VerifiedLL1.Memo

section Abstract

inductive V : Type where
  | x | y | z
  deriving DecidableEq, Repr

open V

/-- An exhaustive carrier without duplicates. -/
def carrier : List V := [x, y, z]

theorem hall_carrier : ∀ v, v ∈ carrier := by
  intro v; cases v <;> decide

/-- An exhaustive carrier *with* duplicates: 'FiniteEnum' only promises exhaustiveness. -/
def dupCarrier : List V := [x, y, x, z, y]

theorem hall_dup : ∀ v, v ∈ dupCarrier := by
  intro v; cases v <;> decide

/-- A one-element type, for the toggling test. -/
inductive One : Type where
  | star
  deriving DecidableEq, Repr

def oneCarrier : List One := [One.star]

theorem hall_one : ∀ v, v ∈ oneCarrier := by
  intro v; cases v; decide

section ZeroRounds

/-- **Zero rounds**, for an arbitrary transformer: the memoized list is all-false and the
memoized predicate is constantly false. -/
theorem iterBits_zero (P : (V → Bool) → V → Bool) :
    iterBits carrier P 0 = [false, false, false] := by
  rw [iterBits_eq_map_iterP carrier P hall_carrier]
  rfl

theorem iterMemo_zero (P : (V → Bool) → V → Bool) (v : V) :
    iterMemo carrier P 0 v = false := by
  rw [iterMemo_eq_iterP carrier P hall_carrier]
  exact Fixpoint.iterP_zero ..

/-- The same, decided by the kernel rather than transferred through the bridge. -/
example : iterBits carrier (fun _ _ => true) 0 = [false, false, false] := by decide
example : iterMemo carrier (fun _ _ => true) 0 y = false := by decide
example : iterBits dupCarrier (fun _ _ => true) 0 = [false, false, false, false, false] := by decide

end ZeroRounds

section ImmediateFixedPoint

/-- A transformer that ignores its input: the iteration is stable after one round. -/
def constP : (V → Bool) → V → Bool := fun _ v => v == y

/-- One round already gives the limit. -/
example : iterBits carrier constP 1 = [false, true, false] := by decide

/-- The early stop fires after round 2, so the huge fuel is ignored: the answer is the
same as with fuel 1. -/
example : iterBits carrier constP 100 = [false, true, false] := by decide
example : iterMemo carrier constP 100 y = true := by decide
example : iterMemo carrier constP 100 z = false := by decide
example : iterMemo dupCarrier constP 100 y = true := by decide
example : iterBits dupCarrier constP 100 = [false, true, false, false, true] := by decide

/-- With zero fuel nothing has been computed yet, even though the transformer is
immediately stable. -/
example : iterMemo carrier constP 0 y = false := by decide

end ImmediateFixedPoint

section Duplicates

/-- Duplicated carrier entries are tabulated with the same value, in carrier order. -/
example : iterBits dupCarrier constP 3 = [false, true, false, false, true] := by decide

/-- The bridge itself is duplicate-insensitive: 'iterMemo' on a duplicated carrier still
computes the approximant. -/
theorem dup_bridge (n : Nat) (v : V) :
    iterMemo dupCarrier constP n v = Fixpoint.iterP constP n v :=
  iterMemo_eq_iterP dupCarrier constP hall_dup n v

/-- A duplicated carrier and a plain carrier agree pointwise. -/
theorem dup_eq_plain (n : Nat) (v : V) :
    iterMemo dupCarrier constP n v = iterMemo carrier constP n v := by
  rw [dup_bridge, iterMemo_eq_iterP carrier constP hall_carrier]

end Duplicates

section Cycle

/-- A NULLABLE-shaped propagation cycle: 'z' has an epsilon rule, 'y' needs 'z', and 'x'
needs 'y'.  The fact needs two rounds to travel from 'z' to 'x'. -/
def chainP : (V → Bool) → V → Bool
  | _, z => true
  | f, y => f z
  | f, x => f y

/-- 'chainP' is monotone, so the library's termination theorem applies to it. -/
theorem chainP_mono : Fixpoint.PMono chainP := by
  intro f g hle v h
  cases v with
  | z => rfl
  | y => exact hle z h
  | x => exact hle y h

example : iterBits carrier chainP 1 = [false, false, true] := by decide
example : iterBits carrier chainP 2 = [false, true, true] := by decide
example : iterBits carrier chainP 3 = [true, true, true] := by decide
example : iterBits carrier chainP 4 = [true, true, true] := by decide
example : iterBits carrier chainP 50 = [true, true, true] := by decide
example : iterMemo carrier chainP 1 x = false := by decide
example : iterMemo carrier chainP 2 x = false := by decide
example : iterMemo carrier chainP 3 x = true := by decide

/-- The limit is closed under the transformer: 'carrier.length' rounds suffice, and the
transferred 'iterMemo_closed' says so. -/
theorem chain_closed (v : V) :
    iterMemo carrier chainP carrier.length v = true ↔
      chainP (iterMemo carrier chainP carrier.length) v = true :=
  iterMemo_closed carrier chainP chainP_mono hall_carrier v

/-- One more round beyond the bound adds nothing ('iterMemo_stable' through the bridge). -/
theorem chain_stable (v : V) :
    iterMemo carrier chainP (carrier.length + 1) v = iterMemo carrier chainP carrier.length v :=
  iterMemo_stable carrier chainP chainP_mono hall_carrier v

/-- The cycle needs exactly two rounds: the limit is not reached earlier, which is what
'maximum-length' bounds like 'carrier.length' are for. -/
example : iterMemo carrier chainP 2 x = false := by decide
example : iterMemo carrier chainP 3 x = true := by decide

end Cycle

section Nonmonotone

/-- **A nonmonotone transformer**: it *toggles* the bit it reads.  The least fixed point
of a toggling transformer does not exist (it is not monotone), and the approximants
alternate; the memoized loop has to reproduce the alternation exactly. -/
def toggleP (f : One → Bool) (v : One) : Bool := !f v

/-- On a one-element carrier: exact alternation, checked round by round. -/
example : iterBits oneCarrier toggleP 0 = [false] := by decide
example : iterBits oneCarrier toggleP 1 = [true] := by decide
example : iterBits oneCarrier toggleP 2 = [false] := by decide
example : iterBits oneCarrier toggleP 3 = [true] := by decide
example : iterBits oneCarrier toggleP 4 = [false] := by decide
example : iterBits oneCarrier toggleP 5 = [true] := by decide
example : iterBits oneCarrier toggleP 6 = [false] := by decide
example : iterBits oneCarrier toggleP 7 = [true] := by decide

/-- The bridge holds for *every* number of rounds, monotone or not.  Here the loop never
stops early - no two consecutive bit lists are equal - so it really performs n rounds. -/
theorem toggle_bridge (n : Nat) (v : One) :
    iterMemo oneCarrier toggleP n v = Fixpoint.iterP toggleP n v :=
  iterMemo_eq_iterP oneCarrier toggleP hall_one n v

/-- The unfolded iteration alternates too: this is the *semantics* being tested, not a
least-fixed-point property. -/
example : Fixpoint.iterP toggleP 6 One.star = false := by decide
example : Fixpoint.iterP toggleP 7 One.star = true := by decide
example : iterMemo oneCarrier toggleP 6 One.star = false := by decide
example : iterMemo oneCarrier toggleP 7 One.star = true := by decide

/-- A nonmonotone transformer on a three-element carrier, and on a carrier with
duplicates. -/
def toggleP3 (f : V → Bool) (v : V) : Bool := !f v

theorem toggle_bridge3 (n : Nat) (v : V) :
    iterMemo carrier toggleP3 n v = Fixpoint.iterP toggleP3 n v :=
  iterMemo_eq_iterP carrier toggleP3 hall_carrier n v

theorem toggle_bridge_dup (n : Nat) (v : V) :
    iterMemo dupCarrier toggleP3 n v = Fixpoint.iterP toggleP3 n v :=
  iterMemo_eq_iterP dupCarrier toggleP3 hall_dup n v

example : iterBits carrier toggleP3 7 = [true, true, true] := by decide
example : iterBits carrier toggleP3 8 = [false, false, false] := by decide
example : iterBits dupCarrier toggleP3 7 = [true, true, true, true, true] := by decide
example : iterMemo dupCarrier toggleP3 8 z = false := by decide

end Nonmonotone

section OffCarrier

/-- **Why 'hall' is load-bearing.**  'badP' reads a point outside the carrier
'false ∉ [true]' and feeds it back on-carrier, so the memoized lookup - which must
answer 'false' off-carrier - computes something different from 'iterP'. -/
def badP (f : Bool → Bool) (x : Bool) : Bool := if x then f false else true

/-- The unfolded iteration picks up the off-carrier fact after two rounds... -/
example : Fixpoint.iterP badP 2 true = true := by decide

/-- ... while the memoized path never sees it: 'lookup [true] bits false = false' for
every bit list, so the loop stops after the first round and stays false forever. -/
example : iterBits [true] badP 2 = [false] := by decide
example : iterMemo [true] badP 2 true = false := by decide
example : iterMemo [true] badP 5 true = false := by decide

/-- So the bridge statement is false without 'hall': the two sides disagree at n = 2. -/
example : ¬ (iterMemo [true] badP 2 true = Fixpoint.iterP badP 2 true) := by decide

/-- **For every number of rounds**, not just the ones sampled above: the memoized loop
reaches its (wrong) fixed point after the first round and never moves again, while 'iterP'
keeps growing. -/
theorem bad_iterBits_all (n : Nat) : iterBits [true] badP n = [false] := by
  have hstep : step [true] badP [false] = [false] := rfl
  have key : ∀ k : Nat, loop [true] badP k [false] = [false] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [loop_succ, hstep, ite_eq_left (by rfl : ([false] == [false]) = true)]
  exact key n

/-- ... whereas the unfolded iteration is 'true' at round 2 and stays 'true'. -/
example : Fixpoint.iterP badP 3 true = true := by decide

/-- Adding the missing element repairs it, exactly as 'hall' requires. -/
example : iterMemo [true, false] badP 2 true = true := by decide

end OffCarrier

end Abstract

section ToyBridge

open VerifiedLL1 Examples.Toy Examples.Toy.Tok Examples.Toy.Var

/-- **NULLABLE via the memoized backend.**  'G.nullable' is definitionally
'Fixpoint.iterP (nullableP G) G.nullableRounds', so this is one line from the bridge. -/
theorem nullable_eq_iterMemo (G : Grammar T N) [BEq N] [LawfulBEq N] [FiniteEnum N] (A : N) :
    G.nullable A =
      iterMemo (FiniteEnum.elems (α := N)) (nullableP G) G.nullableRounds A :=
  (iterMemo_eq_iterP (FiniteEnum.elems (α := N)) (nullableP G) FiniteEnum.complete
    G.nullableRounds A).symm

/-- **REACH via the memoized backend.** -/
theorem occurs_eq_iterMemo (G : Grammar T N) [DecidableEq T] [DecidableEq N] [FiniteEnum N]
    (A : N) :
    G.occurs A = iterMemo (FiniteEnum.elems (α := N)) (occursP G) G.occursRounds A :=
  (iterMemo_eq_iterP (FiniteEnum.elems (α := N)) (occursP G) FiniteEnum.complete
    G.occursRounds A).symm

/-- **FIRST via the memoized backend.** -/
theorem first_eq_iterMemo (G : Grammar T N) [DecidableEq T] [DecidableEq N]
    [FiniteEnum T] [FiniteEnum N] (s : Sym T N) (x : LTok T) :
    G.first s x =
      iterMemo (FiniteEnum.elems (α := Sym T N × LTok T))
        (firstP G (firstNul G)) G.firstRounds (s, x) :=
  (iterMemo_eq_iterP (FiniteEnum.elems (α := Sym T N × LTok T))
    (firstP G (firstNul G)) FiniteEnum.complete G.firstRounds (s, x)).symm

/-- **FOLLOW via the memoized backend.**  The library's `G.follow` *is* this computation
now; the bridge back to the `iterP` chain the semantic proofs use is `Grammar.follow_eq_iterP`
in `Follow.lean`. -/
theorem follow_eq_iterMemo (G : Grammar T N) [DecidableEq T] [DecidableEq N]
    [FiniteEnum T] [FiniteEnum N] (A : N) (x : LTok T) :
    G.follow A x =
      iterMemo (FiniteEnum.elems (α := N × LTok T))
        (followP G G.first (firstNul G) G.occurs) G.followRounds (A, x) := rfl

/-- The closure and stability facts of the library, restated for the memoized backend. -/
theorem toy_nullable_closed (A : Var) :
    iterMemo (FiniteEnum.elems (α := Var)) (nullableP G) G.nullableRounds A = true ↔
      nullableP G
        (iterMemo (FiniteEnum.elems (α := Var)) (nullableP G) G.nullableRounds) A = true :=
  iterMemo_closed (FiniteEnum.elems (α := Var)) (nullableP G) (nullableP_mono G)
    FiniteEnum.complete A

theorem toy_nullable_stable (A : Var) :
    iterMemo (FiniteEnum.elems (α := Var)) (nullableP G) (G.nullableRounds + 1) A =
      iterMemo (FiniteEnum.elems (α := Var)) (nullableP G) G.nullableRounds A :=
  iterMemo_stable (FiniteEnum.elems (α := Var)) (nullableP G) (nullableP_mono G)
    FiniteEnum.complete A

/-- **Smoke tests.**  The memoized bit list of the Toy grammar, decided by the kernel:
s, p, q are nullable and u is not. -/
example :
    iterBits (FiniteEnum.elems (α := Var)) (nullableP G) G.nullableRounds =
      [true, true, true, false] := by decide

/-- The memoized predicate agrees with the library's 'G.nullable' on every nonterminal. -/
example : G.nullable s && G.nullable p && G.nullable q && ! (G.nullable u) = true := by decide

/-- The memoized FOLLOW bit list over the 16 (nonterminal, lookahead) pairs. -/
example :
    iterBits (FiniteEnum.elems (α := Var × LTok Tok))
      (followP G G.first (firstNul G) G.occurs) G.followRounds =
      [false, false, false, true, false, true, false, true,
       false, false, false, true, false, false, false, false] := by decide

/-- **A duplicated carrier over the real grammar.**  'FiniteEnum' does not promise
duplicate-freeness, and the analysis does not care: repeating 's' and 'q' repeats their
bits. -/
def dupVars : List Var := [s, p, q, u, s, q]

theorem hall_dupVars : ∀ A, A ∈ dupVars := by
  intro A; cases A <;> simp [dupVars]

example : iterBits dupVars (nullableP G) G.nullableRounds = [true, true, true, false, true, true] := by
  decide

theorem dup_nullable_eq (A : Var) :
    G.nullable A = iterMemo dupVars (nullableP G) G.nullableRounds A :=
  (iterMemo_eq_iterP dupVars (nullableP G) hall_dupVars G.nullableRounds A).symm

/-- The duplicated carrier and the library enumeration agree pointwise. -/
theorem dup_agrees (A : Var) :
    iterMemo dupVars (nullableP G) G.nullableRounds A =
      iterMemo (FiniteEnum.elems (α := Var)) (nullableP G) G.nullableRounds A := by
  rw [← dup_nullable_eq, nullable_eq_iterMemo]

end ToyBridge


section QCPipeline

open Examples.QCircuits Examples.QCircuits.Tok Examples.QCircuits.Var

/-- The whole analysis pipeline, memoized: NULLABLE, REACH, then FIRST reading the
memoized NULLABLE, then FOLLOW reading the three memoized analyses, then SELECT and the
LL(1) check. -/
def qNull : Var → Bool := iterMemo (FiniteEnum.elems (α := Var)) (nullableP Q) Q.nullableRounds

def qOcc : Var → Bool := iterMemo (FiniteEnum.elems (α := Var)) (occursP Q) Q.occursRounds

def qFirst : Sym Tok Var → LTok Tok → Bool :=
  fun s x => iterMemo (FiniteEnum.elems (α := Sym Tok Var × LTok Tok))
    (firstP Q (symNull qNull)) Q.firstRounds (s, x)

def qFollow : Var → LTok Tok → Bool :=
  fun A x => iterMemo (FiniteEnum.elems (α := Var × LTok Tok))
    (followP Q qFirst (symNull qNull) qOcc) Q.followRounds (A, x)

def qSelectTest (A : Var) (rhs : List (Sym Tok Var)) (x : LTok Tok) : Bool :=
  ((!isEof x && firstListTest qFirst (symNull qNull) rhs x) ||
    (rhs.all (symNull qNull) && qFollow A x))

def qSelectRhs (A : Var) (x : LTok Tok) : List (List (Sym Tok Var)) :=
  (Q.productions.filter fun pr => (pr.1 == A && qSelectTest A pr.2 x)).map Prod.snd

def qll1Check : Bool :=
  (FiniteEnum.elems (α := Var × LTok Tok)).all fun p =>
    (qSelectRhs p.1 p.2).all fun a => (qSelectRhs p.1 p.2).all fun b => (a == b)

/-- Each memoized analysis is the library's analysis: one line of the bridge each. -/
theorem qNull_eq (A : Var) : qNull A = Q.nullable A :=
  iterMemo_eq_iterP (FiniteEnum.elems (α := Var)) (nullableP Q) FiniteEnum.complete
    Q.nullableRounds A

theorem qOcc_eq (A : Var) : qOcc A = Q.occurs A :=
  iterMemo_eq_iterP (FiniteEnum.elems (α := Var)) (occursP Q) FiniteEnum.complete
    Q.occursRounds A

theorem qFirst_eq (s : Sym Tok Var) (x : LTok Tok) : qFirst s x = Q.first s x :=
  iterMemo_eq_iterP (FiniteEnum.elems (α := Sym Tok Var × LTok Tok))
    (firstP Q (symNull qNull)) FiniteEnum.complete Q.firstRounds (s, x)

/-- The three input functions of the FOLLOW transformer agree pointwise, so the memoized
transformer *is* the library's transformer. -/
theorem qFollow_fun_eq :
    followP Q qFirst (symNull qNull) qOcc = followP Q Q.first (firstNul Q) Q.occurs := by
  have h1 : qFirst = Q.first := funext fun s => funext fun x => qFirst_eq s x
  have h2 : qNull = Q.nullable := funext qNull_eq
  have h3 : qOcc = Q.occurs := funext qOcc_eq
  show followP Q qFirst (symNull qNull) qOcc = followP Q Q.first (symNull Q.nullable) Q.occurs
  rw [h1, h2, h3]

theorem qFollow_eq (A : Var) (x : LTok Tok) : qFollow A x = Q.follow A x := by
  show iterMemo (FiniteEnum.elems (α := Var × LTok Tok))
      (followP Q qFirst (symNull qNull) qOcc) Q.followRounds (A, x) = Q.follow A x
  rw [qFollow_fun_eq]
  rfl

theorem qSelectTest_eq (A : Var) (rhs : List (Sym Tok Var)) (x : LTok Tok) :
    qSelectTest A rhs x = Q.selectTest A rhs x := by
  have h1 : qFirst = Q.first := funext fun s => funext fun x => qFirst_eq s x
  have h2 : symNull qNull = firstNul Q := congrArg symNull (funext qNull_eq)
  have h3 : qFollow = Q.follow := funext fun A => funext fun x => qFollow_eq A x
  show ((!isEof x && firstListTest qFirst (symNull qNull) rhs x) ||
          (rhs.all (symNull qNull) && qFollow A x)) = _
  rw [h1, h2, h3]
  rfl

theorem qSelectRhs_eq (A : Var) (x : LTok Tok) : qSelectRhs A x = Q.selectRhs A x := by
  unfold qSelectRhs Grammar.selectRhs
  simp only [qSelectTest_eq]

/-- **The memoized LL(1) check is the library's LL(1) check.** -/
theorem qll1Check_eq : qll1Check = Q.ll1Check := by
  unfold qll1Check Grammar.ll1Check
  simp only [qSelectRhs_eq]

/-- The circuit grammar passes the memoized check - transported from the library's own
'decide', so no fresh kernel work is needed here at all. -/
theorem qll1Check_true : qll1Check = true := by
  rw [qll1Check_eq]; exact qc_ll1

end QCPipeline

end VerifiedLL1.MemoTest