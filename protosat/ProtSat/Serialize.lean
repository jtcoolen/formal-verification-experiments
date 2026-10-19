/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Resolution

/-!
# ProtSat: serializing refutation evidence (roadmap stage 6, second installment)

## Why this module exists

`Resolution.lean` checks a refutation that is already in memory. Roadmap stage 6 asks for more:

> Bind evidence to actual query data and CNF contents. Prove serialization round-trips and
> frontend semantic preservation.

Evidence has to leave the process that produced it - written to a file, sent over a socket, cached
on disk - and come back. That boundary is where proofs are usually lost: a parser that panics, a
format that identifies a line only up to reordering, a decoder that silently drops a step. This
module gives the format and proves the properties that make it safe:

    proofOfCode_proofCode : proofOfCode (p.length + 1) (proofCode p) = some p
    proofCode_inj         : proofCode p = proofCode q -> p = q
    checkCode_sound       : checkCode f k c = true -> ProtSat.Unsat f
    checkCode_iff_checkProof : checkCode f (p.length + 1) (proofCode p) = checkProof f p

The first is the round trip: nothing is lost. The second is injectivity: nothing is conflated, so a
decoded code identifies the refutation it came from - which is what lets a digest of a code name a
cached artifact without the digest standing in for the proof itself. The third and fourth say the
whole path from a raw code to a formula fact goes through the checker and nothing else: no solver,
no search, no partial function.

## The format

A refutation is a flat list of integers. Each line is a four-number header, then its clause
literals, then a 0 terminator:

    line := tag i1 i2 pivot lit* 0
    tag  := 0  an original clause of the formula, indexed by i1
           | 1  a resolvent of lines i1 and i2, pivoting on i3
    lit  := k+1      the positive literal on variable k  (DIMACS, counted from 1)
           | -(k+1)  the negated literal on variable k

Literals are coded DIMACS-style with the sign in the integer, so every literal code is nonzero and
`0` is free to terminate a clause. Two consequences make the decoder cheap to reason about: every
nonzero integer is the code of exactly one literal, so decoding a literal never fails and never
needs arithmetic; and the tag is a constructor test, not a comparison.

The decoder is *total*: input that is not a well-formed code yields `none`, never a panic and never
a partial function. Fuel is one unit per line, plus one.

## What this does not do

This is the format and its invariants, not a file I/O layer: reading bytes is the frontend's job,
and `Correspondence.boundedSafe_of_refutation` is where a checked refutation becomes a security
statement.
-/

namespace ProtSat.Serialize

open ProtSat ProtSat.Resolution

/-! ## Literals -/

/-- The code of a literal, DIMACS-style: counted from 1 with the sign in the integer, so `0` never
codes a literal and can terminate a clause. -/
def litCode (l : Lit) : Int := if l.neg then -((l.var : Int) + 1) else (l.var : Int) + 1

/-- Decode a literal code. `0` is the terminator and decodes to nothing; every other integer decodes
to exactly one literal. -/ 
def litOfCode : Int -> Option Lit
  | Int.ofNat 0 => none
  | Int.ofNat (k + 1) => some { var := k, neg := false }
  | Int.negSucc k => some { var := k, neg := true }

/-- No literal codes to `0`, so the terminator is never ambiguous. -/
theorem litCode_ne_zero (l : Lit) : litCode l ≠ 0 := by
  cases l with
  | mk v neg =>
      cases neg with
      | false => show ((v : Int) + 1) ≠ 0; omega
      | true => show -((v : Int) + 1) ≠ 0; omega

/-- **Decode inverts code**, by a constructor test and nothing else. -/
theorem litOfCode_litCode (l : Lit) : litOfCode (litCode l) = some l := by
  cases l with
  | mk v neg => cases neg <;> rfl

/-- **Code inverts decode** on every code that decodes at all. -/
theorem litCode_litOfCode : ∀ (c : Int), c ≠ 0 -> litCode ((litOfCode c).getD (pos 0)) = c
  | Int.ofNat 0, h => absurd rfl h
  | Int.ofNat (k + 1), _ => rfl
  | Int.negSucc k, _ => rfl

/-- A code determines its literal: the coding is injective. -/
theorem litCode_inj {l₁ l₂ : Lit} (h : litCode l₁ = litCode l₂) : l₁ = l₂ := by
  have h₁ := congrArg litOfCode h
  rw [litOfCode_litCode, litOfCode_litCode] at h₁
  exact Option.some.inj h₁

/-! ## Clauses and lines -/

/-- Read clause literals up to the terminating `0`, returning them and the unconsumed remainder.
Because every nonzero integer decodes, the terminator is the only thing that can end a clause. -/
def readLits : List Int -> Option (Clause × List Int)
  | [] => none
  | n :: tl =>
      match litOfCode n with
      | none => some ([], tl)
      | some x =>
          match readLits tl with
          | none => none
          | some (cl, tl2) => some (x :: cl, tl2)

/-- `readLits` reads exactly the literals of `cl` and stops at the terminator. -/
theorem readLits_map {cl : Clause} : ∀ (c : List Int),
    readLits (cl.map litCode ++ (0 :: c)) = some (cl, c) := by
  induction cl with
  | nil => intro c; rfl
  | cons x xs ih =>
      intro c
      show readLits (litCode x :: (xs.map litCode ++ (0 :: c))) = some (x :: xs, c)
      rw [readLits, litOfCode_litCode, ih]

/-- One line: a tag, two indices and a pivot, then the literals and the terminator. Tag `0` is an
original clause of the formula (first index); tag `1` is a resolvent of the two indexed lines,
pivoting on the third. -/
def lineCode (l : Line) : List Int :=
  (match l.why with
   | Just.orig n => [0, (n : Int), 0, 0]
   | Just.res i j v => [1, (i : Int), (j : Int), (v : Int)]) ++ l.cl.map litCode ++ [0]

/-- The body of the line decoder: read the tag, then the clause. Keeping the tag test here rather
than in a list pattern makes it a decidable equality on `Int`, which reduces without arithmetic. -/
def lineBody (h a b v : Int) (tl : List Int) : Option (Line × List Int) :=
  if h = 0 then
    match readLits tl with
    | some (cl, tl2) => some ({ cl := cl, why := Just.orig a.toNat }, tl2)
    | none => none
  else if h = 1 then
    match readLits tl with
    | some (cl, tl2) => some ({ cl := cl, why := Just.res a.toNat b.toNat v.toNat }, tl2)
    | none => none
  else none

/-- Decode one line, returning it and the unconsumed remainder. A tag that is neither `0` nor `1`,
or a header that runs off the end of the code, decodes to nothing. -/
def lineOfCode : List Int -> Option (Line × List Int)
  | h :: a :: b :: v :: tl => lineBody h a b v tl
  | _ => none

/-- **Line decoding inverts line coding**, whatever follows the line. -/
theorem lineOfCode_lineCode (l : Line) : ∀ (c : List Int),
    lineOfCode (lineCode l ++ c) = some (l, c) := by
  cases l with
  | mk cl why =>
      cases why with
      | orig n =>
          intro c
          show lineOfCode (0 :: (n : Int) :: 0 :: 0 :: (cl.map litCode ++ [0] ++ c))
              = some (⟨cl, Just.orig n⟩, c)
          simp [lineOfCode, lineBody, readLits_map]
      | res i j v =>
          intro c
          show lineOfCode (1 :: (i : Int) :: (j : Int) :: (v : Int)
              :: (cl.map litCode ++ [0] ++ c)) = some (⟨cl, Just.res i j v⟩, c)
          simp [lineOfCode, lineBody, readLits_map]

/-- A line code begins with its tag, so it is never empty and a decoder always makes progress. -/
theorem lineCode_cons (l : Line) : ∃ hd tl, lineCode l = hd :: tl := by
  cases l with
  | mk cl why =>
      cases why with
      | orig n => exact ⟨0, ((n : Int) :: [0, 0] ++ cl.map litCode ++ [0]), rfl⟩
      | res i j v => exact ⟨1, ((i : Int) :: [j, v] ++ cl.map litCode ++ [0]), rfl⟩

/-! ## Whole refutations -/

/-- The code of a whole refutation. -/
def proofCode (p : List Line) : List Int := p.flatMap lineCode

/-- A nonempty proof has a nonempty code. -/
theorem proofCode_cons_ne (l : Line) (rest : List Line) : proofCode (l :: rest) ≠ [] := by
  obtain ⟨hd, tl, h⟩ := lineCode_cons l
  have h3 : proofCode (l :: rest) = hd :: (tl ++ proofCode rest) := by
    show lineCode l ++ proofCode rest = hd :: (tl ++ proofCode rest)
    rw [h, List.cons_append]
  intro h2
  rw [h3] at h2
  exact absurd h2 (by simp)

/-- A nonempty proof has a nonempty code, in the form the fuel lemmas want. -/
theorem proofCode_ne : ∀ {p : List Line}, p ≠ [] -> proofCode p ≠ []
  | l :: rest, _ => proofCode_cons_ne l rest
  | [], h => absurd rfl h

/-- Decode a refutation. Fuel keeps the definition structurally decreasing; one unit per line, plus
one, is enough. -/
def proofOfCode : Nat -> List Int -> Option (List Line)
  | _, [] => some []
  | 0, _ => none
  | k + 1, c =>
      match lineOfCode c with
      | some (l, tl) => (proofOfCode k tl).map (l :: ·)
      | none => none

/-- One decoding step on a nonempty code: read a line, then decode the rest with one less fuel. -/
theorem proofOfCode_step (k : Nat) {c : List Int} (hc : c ≠ []) :
    proofOfCode (k + 1) c =
      match lineOfCode c with
      | some (l, tl) => (proofOfCode k tl).map (l :: ·)
      | none => none := by
  cases c
  · exact absurd rfl hc
  · simp [proofOfCode]

/-- With no fuel and a nonempty code, nothing decodes. -/
theorem proofOfCode_zero {c : List Int} (hc : c ≠ []) : proofOfCode 0 c = none := by
  cases c
  · exact absurd rfl hc
  · simp [proofOfCode]

/-- **The round trip.** Coding and decoding a refutation returns it exactly, given one unit of fuel
per line plus one. -/
theorem proofOfCode_proofCode : ∀ (p : List Line) (k : Nat), k >= p.length ->
    proofOfCode k (proofCode p) = some p := by
  intro p
  induction p with
  | nil => intro k _; simp [proofCode, proofOfCode]
  | cons l rest ih =>
      intro k hk
      cases k with
      | zero =>
          have hpos : (l :: rest).length > 0 := by simp
          omega
      | succ j =>
          have hn : lineCode l ++ proofCode rest ≠ [] := by
            intro h
            obtain ⟨hd, tl, hc⟩ := lineCode_cons l
            rw [hc, List.cons_append] at h
            exact absurd h (by simp)
          have hlen : j >= rest.length := by
            have h2 : (l :: rest).length = rest.length + 1 := rfl
            rw [h2] at hk
            omega
          show proofOfCode (j + 1) (lineCode l ++ proofCode rest) = some (l :: rest)
          rw [proofOfCode_step j hn, lineOfCode_lineCode l]
          simp [ih j hlen]

/-- **The round trip at the natural fuel.** -/
theorem proofOfCode_proofCode' (p : List Line) :
    proofOfCode (p.length + 1) (proofCode p) = some p :=
  proofOfCode_proofCode p (p.length + 1) (by omega)

/-- **Distinct proofs, distinct codes.** The serialization loses nothing and collides nowhere, so a
decoded code identifies the refutation it came from. -/
theorem proofCode_inj : ∀ {p q : List Line}, proofCode p = proofCode q -> p = q := by
  intro p
  induction p with
  | nil =>
      intro q h
      cases q with
      | nil => rfl
      | cons l rest => exact absurd h.symm (proofCode_cons_ne l rest)
  | cons l₁ rest₁ ih =>
      intro q h
      cases q with
      | nil => exact absurd h (proofCode_cons_ne l₁ rest₁)
      | cons l₂ rest₂ =>
          have h2 : lineCode l₁ ++ proofCode rest₁ = lineCode l₂ ++ proofCode rest₂ := h
          have e₁ := lineOfCode_lineCode l₁ (proofCode rest₁)
          have e₂ := lineOfCode_lineCode l₂ (proofCode rest₂)
          rw [← h2] at e₂
          rw [e₁] at e₂
          have h₁₂ : (l₁, proofCode rest₁) = (l₂, proofCode rest₂) := Option.some.inj e₂
          have hl : l₁ = l₂ := by simpa using congrArg Prod.fst h₁₂
          have hrest : proofCode rest₁ = proofCode rest₂ := by
            simpa using congrArg Prod.snd h₁₂
          subst hl
          exact congrArg (l₁ :: ·) (ih hrest)

/-! ## Checking a code -/

/-- Check a decoded line list against the formula it claims to refute. -/
def checkCodeMatch (f : CNF) : Option (List Line) -> Bool
  | some p => checkProof f p
  | none => false

/-- **Decode a code and check the refutation it carries.** This is the whole path from bytes to a
formula fact: no solver, no search, and a total decoder. -/
def checkCode (f : CNF) (k : Nat) (c : List Int) : Bool := checkCodeMatch f (proofOfCode k c)

theorem checkCode_of {f : CNF} {k : Nat} {c : List Int} {p : List Line}
    (h : proofOfCode k c = some p) : checkCode f k c = checkProof f p := by
  simp [checkCode, checkCodeMatch, h]

/-- **Serialized evidence is evidence.** A code that passes `checkCode` refutes the formula. -/
theorem checkCode_sound {f : CNF} {k : Nat} {c : List Int} (h : checkCode f k c = true) :
    ProtSat.Unsat f := by
  cases h₂ : proofOfCode k c with
  | some p => rw [checkCode_of h₂] at h; exact checkProof_sound h
  | none => simp [checkCode, checkCodeMatch, h₂] at h

/-- **Evidence is evidence in either direction.** A refutation and its code are interchangeable for
the checker: the code is accepted exactly when the proof is. -/
theorem checkCode_iff_checkProof {f : CNF} {p : List Line} :
    checkCode f (p.length + 1) (proofCode p) = checkProof f p :=
  checkCode_of (proofOfCode_proofCode' p)

/-- The demo refutation round-trips through the code and is still accepted. -/
theorem checkCode_demo : checkCode demoF (demoP.length + 1) (proofCode demoP) = true := by
  rw [checkCode_iff_checkProof]
  exact accepts_demo

/-- A code that does not decode is rejected, whatever the formula: an unknown tag. -/
theorem checkCode_rejects_garbage : checkCode demoF 4 [7, 0, 0, 0, 0] = false := by decide

/-- A truncated code - a line with no terminator - is rejected. -/
theorem checkCode_rejects_truncated_code : checkCode demoF 4 [0, 0, 0, 0, 3] = false := by decide

/-- No fuel, no decode, so no verdict: the decoder declines rather than guessing. -/
theorem checkCode_rejects_no_fuel : checkCode demoF 0 (proofCode demoP) = false := by
  rw [checkCode, proofOfCode_zero (proofCode_ne (by simp [demoP])), checkCodeMatch]

/-- A code that decodes to a well-formed but unjustified line is rejected by the checker, not by
the decoder: the two roles stay separate and neither is trusted for the other. -/
theorem checkCode_rejects_unjustified : checkCode demoF 1 [0, 0, 0, 0, 9, 0] = false := by decide

/-- So a corrupted proof is rejected in its serialized form too. -/
theorem checkCode_rejects_corrupted :
    checkCode demoF (demoP_bad.length + 1) (proofCode demoP_bad) = false := by
  rw [checkCode_iff_checkProof]
  exact rejects_corrupted

end ProtSat.Serialize
