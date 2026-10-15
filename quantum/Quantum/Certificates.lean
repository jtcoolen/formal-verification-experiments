/-
Independent executable proof certificates.

A certificate is a concrete finite derivation: a list of steps, each naming a rule id, its
instantiation arguments, the circuit context in which the rewrite is applied, and the
orientation.  The checker *recomputes* the left-hand side and the right-hand side of every
step from the rule library (Quantum/Rewrites.lean) and compares the recomputed left-hand side
with the circuit it is supposed to transform; it never trusts a proposed replacement.

The checker depends only on syntax, semantics, the verified rewrite library and proved
contextual congruence.  It does not import the optimizer, the e-graph, or extraction.

The central theorem is 'checkCertificate_sound': a certificate accepted by this executable
checker implies PhaseEquivalent, i.e. equality of the two matrix denotations up to a complex
scalar of unit modulus.
-/
import Quantum.Rewrites

namespace Quantum

/-! ### Certificates -/

/-- One derivation step: rewrite with rule 'ruleId' instantiated at 'args', inside context
'ctx'.  'backward = false' replaces lhs by rhs; 'backward = true' replaces rhs by lhs. -/
structure Step (n : Nat) where
  ruleId : String
  args : List (Arg n)
  ctx : Ctx n
  backward : Bool
deriving DecidableEq

/-- A certificate is a concrete finite derivation. -/
abbrev Certificate (n : Nat) : Type := List (Step n)

/-- Flip the orientation of a step. -/
def Step.flip {n : Nat} (s : Step n) : Step n := { s with backward := !s.backward }

/-- The pattern and the replacement of a step, recomputed from the rule library. -/
def stepTerms {n : Nat} (s : Step n) (r : Rule n) : Circuit n × Circuit n :=
  (if s.backward then r.rhs s.args else r.lhs s.args,
   if s.backward then r.lhs s.args else r.rhs s.args)

theorem stepTerms_bwd {n : Nat} (s : Step n) (r : Rule n) (hb : s.backward = true) :
    stepTerms s r = (r.rhs s.args, r.lhs s.args) := by
  classical
  simp [stepTerms, hb]

theorem stepTerms_fwd {n : Nat} (s : Step n) (r : Rule n) (hb : s.backward = false) :
    stepTerms s r = (r.lhs s.args, r.rhs s.args) := by
  classical
  simp [stepTerms, hb]

theorem stepTerms_flip {n : Nat} (s : Step n) (r : Rule n) :
    stepTerms (Step.flip s) r = ((stepTerms s r).2, (stepTerms s r).1) := by
  classical
  by_cases hb : s.backward <;> simp [Step.flip, stepTerms, hb]

/-- Apply one step to a circuit: the step applies exactly when the rule id is known, its side
condition holds, and the context filled with the recomputed left-hand side is *syntactically*
the current circuit. -/
def applyStep {n : Nat} (c : Circuit n) (s : Step n) : Option (Circuit n) :=
  (findRule n s.ruleId).bind fun r =>
    if r.side s.args then
      if Ctx.fill s.ctx (stepTerms s r).1 = c then
        some (Ctx.fill s.ctx (stepTerms s r).2)
      else none
    else none

/-- Characterization of when a step applies. -/
theorem applyStep_iff {n : Nat} {c c' : Circuit n} (s : Step n) (r : Rule n)
    (hfind : findRule n s.ruleId = some r) (hs : r.side s.args = true) :
    applyStep c s = some c' <->
      c = Ctx.fill s.ctx (stepTerms s r).1 /\ c' = Ctx.fill s.ctx (stepTerms s r).2 := by
  classical
  constructor
  · intro h
    unfold applyStep at h
    rw [hfind, Option.bind_some, if_pos hs] at h
    by_cases hm : Ctx.fill s.ctx (stepTerms s r).1 = c
    · rw [if_pos hm] at h
      exact ⟨hm.symm, Option.some.inj h.symm⟩
    · rw [if_neg hm] at h
      exact absurd h (by simp)
  · rintro ⟨hc, hc'⟩
    unfold applyStep
    rw [hfind, Option.bind_some, if_pos hs, hc, if_pos rfl, hc']

/-- A step that applies is sound, in either orientation. -/
theorem applyStep_sound {n : Nat} {c c' : Circuit n} (s : Step n)
    (h : applyStep c s = some c') : PhaseEquivalent c c' := by
  classical
  rcases hfind : findRule n s.ruleId with _ | r
  · unfold applyStep at h
    rw [hfind] at h
    exact absurd h (by simp)
  · have hside : r.side s.args = true := by
      by_contra hh
      unfold applyStep at h
      rw [hfind, Option.bind_some, if_neg hh] at h
      exact absurd h (by simp)
    obtain ⟨hc, hc'⟩ := (applyStep_iff s r hfind hside).mp h
    have hsound : PhaseEquivalent (stepTerms s r).1 (stepTerms s r).2 := by
      by_cases hb : s.backward = true
      · rw [stepTerms_bwd s r hb]
        exact (r.sound s.args hside).symm
      · rw [stepTerms_fwd s r (by simp_all)]
        exact r.sound s.args hside
    rw [hc, hc']
    exact Ctx.congr s.ctx hsound

/-- Reversing a step reverses the transformation it performs. -/
theorem applyStep_flip {n : Nat} {c c' : Circuit n} (s : Step n)
    (h : applyStep c s = some c') : applyStep c' (Step.flip s) = some c := by
  classical
  rcases hfind : findRule n s.ruleId with _ | r
  · unfold applyStep at h
    rw [hfind] at h
    exact absurd h (by simp)
  · have hside : r.side s.args = true := by
      by_contra hh
      unfold applyStep at h
      rw [hfind, Option.bind_some, if_neg hh] at h
      exact absurd h (by simp)
    obtain ⟨hc, hc'⟩ := (applyStep_iff s r hfind hside).mp h
    have hfind' : findRule n (Step.flip s).ruleId = some r := hfind
    have hside' : r.side (Step.flip s).args = true := hside
    rw [applyStep_iff (Step.flip s) r hfind' hside', stepTerms_flip]
    exact ⟨hc', hc⟩

/-- Run a derivation from a starting circuit. -/
def walk {n : Nat} (a : Circuit n) : Certificate n -> Option (Circuit n) :=
  List.foldlM (fun c s => applyStep c s) a

/-- The independent certificate checker: the derivation must start at 'a', every step must
apply, consecutive steps must connect, and the final circuit must be exactly 'b'. -/
def checkCertificate {n : Nat} (a b : Circuit n) (cert : Certificate n) : Bool :=
  match walk a cert with
  | some b' => decide (b' = b)
  | none => false

/-! ### Soundness of a checked derivation -/

theorem walk_nil {n : Nat} (a : Circuit n) : walk a [] = some a := by
  classical
  rfl

theorem walk_cons {n : Nat} (a : Circuit n) (s : Step n) (ss : Certificate n) :
    walk a (s :: ss) = (applyStep a s).bind fun a' => walk a' ss := by
  classical
  rfl

theorem walk_some {n : Nat} : ∀ (a : Circuit n) (cert : Certificate n) (b : Circuit n),
    walk a cert = some b -> PhaseEquivalent a b
  | a, [], b, h => by
      rw [walk_nil] at h
      have hab : a = b := Option.some.inj h
      subst hab
      exact PhaseEquivalent.refl a
  | a, s :: ss, b, h => by
      classical
      rw [walk_cons] at h
      rcases h1 : applyStep a s with none | c''
      · rw [h1] at h
        exact absurd h (by simp)
      · rw [h1, Option.bind_some] at h
        exact PhaseEquivalent.trans (applyStep_sound s h1) (walk_some c'' ss b h)

/-- THE CENTRAL THEOREM: every certificate accepted by the independent checker relates
phase-equivalent circuits. -/
theorem checkCertificate_sound {n : Nat} (a b : Circuit n) (cert : Certificate n)
    (h : checkCertificate a b cert = true) : PhaseEquivalent a b := by
  classical
  unfold checkCertificate at h
  rcases hw : walk a cert with none | b'
  · exact absurd h (by simp [hw])
  · rw [hw] at h
    have hb : b' = b := by simpa using h
    subst hb
    exact walk_some a cert b' hw

/-- The recomputed terms of a flipped step are swapped. -/
theorem applyStep_flip' {n : Nat} {c c' : Circuit n} (s : Step n)
    (h : applyStep c s = some c') : applyStep c' (Step.flip s) = some c := applyStep_flip s h

end Quantum