/-
Exact symbolic angles.

All angle arithmetic in this project is *exact*: an angle is a pair of rational numbers
interpreted as the real number

    val a = a.rat + a.piQ * pi

computed with arbitrary-precision rational arithmetic.  There is no floating point anywhere
in the correctness-critical path.  Because the representation uses arbitrary-precision
rationals, large coefficients such as 10^17 are handled without overflow or rounding.

Angle equality used by the rewrite rules and by the certificate checker is *syntactic*
equality of the two rational components.  This is a sound (possibly conservative) test:
'Angle.val_congr' shows equal angles denote equal reals, so a rewrite that requires equal
angles is always semantically justified; angles that merely happen to denote the same real
(for instance through a rational relation with pi) are simply not identified.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Quantum

/-- An exact angle: 'rat' radians plus 'piQ' rational multiples of pi. -/
structure Angle where
  rat : ℚ
  piQ : ℚ
deriving DecidableEq, Inhabited, Repr

namespace Angle

/-- The real number denoted by an angle. -/
noncomputable def val (a : Angle) : ℝ := (a.rat : ℝ) + (a.piQ : ℝ) * Real.pi

def add (a b : Angle) : Angle := ⟨a.rat + b.rat, a.piQ + b.piQ⟩
def neg (a : Angle) : Angle := ⟨-a.rat, -a.piQ⟩
def sub (a b : Angle) : Angle := ⟨a.rat - b.rat, a.piQ - b.piQ⟩
def smulRat (q : ℚ) (a : Angle) : Angle := ⟨q * a.rat, q * a.piQ⟩

instance : Zero Angle := ⟨⟨0, 0⟩⟩
instance : Add Angle := ⟨add⟩
instance : Neg Angle := ⟨neg⟩
instance : Sub Angle := ⟨sub⟩
instance : SMul ℚ Angle := ⟨smulRat⟩

@[simp] theorem zero_rat : (0 : Angle).rat = 0 := rfl
@[simp] theorem zero_piQ : (0 : Angle).piQ = 0 := rfl
@[simp] theorem add_rat (a b : Angle) : (a + b).rat = a.rat + b.rat := rfl
@[simp] theorem add_piQ (a b : Angle) : (a + b).piQ = a.piQ + b.piQ := rfl
@[simp] theorem sub_rat (a b : Angle) : (a - b).rat = a.rat - b.rat := rfl
@[simp] theorem sub_piQ (a b : Angle) : (a - b).piQ = a.piQ - b.piQ := rfl
@[simp] theorem neg_rat (a : Angle) : (-a).rat = -a.rat := rfl
@[simp] theorem neg_piQ (a : Angle) : (-a).piQ = -a.piQ := rfl
@[simp] theorem smul_rat (q : ℚ) (a : Angle) : (q • a).rat = q * a.rat := rfl
@[simp] theorem smul_piQ (q : ℚ) (a : Angle) : (q • a).piQ = q * a.piQ := rfl

/-- Negation is an involution: exact angles have no rounding, so a double negation is
literally the same pair of rationals. -/
theorem neg_neg (a : Angle) : -(-a) = a := by
  cases a with
  | mk r p => show Angle.neg (Angle.neg ⟨r, p⟩) = ⟨r, p⟩; simp [Angle.neg]

/-- Exact angle of a rational number of radians (e.g. a decimal literal parsed as ℚ). -/
def ofRat (q : ℚ) : Angle := ⟨q, 0⟩
/-- Exact rational multiple of pi. -/
def piMul (q : ℚ) : Angle := ⟨0, q⟩
/-- Two pi, exactly. -/
def twoPi : Angle := piMul 2
/-- Pi, exactly. -/
def pi : Angle := piMul 1

@[simp] theorem val_zero : val 0 = 0 := by simp [val]

theorem val_congr {a b : Angle} (h : a = b) : val a = val b := congrArg val h

theorem val_add (a b : Angle) : val (a + b) = val a + val b := by
  simp only [val, add_rat, add_piQ, Rat.cast_add]
  ring

theorem val_neg (a : Angle) : val (-a) = -val a := by
  simp only [val, neg_rat, neg_piQ, Rat.cast_neg]
  ring

theorem val_sub (a b : Angle) : val (a - b) = val a - val b := by
  simp only [val, sub_rat, sub_piQ, Rat.cast_sub]
  ring

theorem val_smul (q : ℚ) (a : Angle) : val (q • a) = (q : ℝ) * val a := by
  simp only [val, smul_rat, smul_piQ, Rat.cast_mul]
  ring

theorem val_piMul (q : ℚ) : val (piMul q) = (q : ℝ) * Real.pi := by simp [piMul, val]
theorem val_pi : val Angle.pi = Real.pi := by
  show ((0 : ℚ) : ℝ) + ((1 : ℚ) : ℝ) * Real.pi = Real.pi
  norm_num
theorem val_twoPi : val twoPi = 2 * Real.pi := by
  simpa [twoPi] using val_piMul 2

/-- Syntactic (hence sound) test for an angle being zero. -/
def isZero (a : Angle) : Bool := a = 0
theorem isZero.mp {a : Angle} (h : isZero a = true) : val a = 0 := by
  have ha : a = 0 := by simpa [isZero] using h
  subst ha
  exact val_zero

/-- Angle equality reduces to equality of the two exact rational components. -/
theorem eq_iff (a b : Angle) : a = b ↔ a.rat = b.rat ∧ a.piQ = b.piQ := by
  cases a with
  | mk r p => cases b with | mk r' p' => simp [Angle.mk.injEq]

/-- Prove an angle equality by normalizing both rational components. -/
theorem eq_of_components (a b : Angle) (h1 : a.rat = b.rat) (h2 : a.piQ = b.piQ) : a = b :=
  (eq_iff a b).mpr ⟨h1, h2⟩

/-- Decidable equality of angles; it implies equality of the denoted reals. -/
def beq (a b : Angle) : Bool := a = b
theorem beq_eq {a b : Angle} : beq a b = true ↔ a = b := by simpa [beq] using decide_eq_true_eq
theorem beq.mp {a b : Angle} (h : beq a b = true) : val a = val b := val_congr (beq_eq.mp h)

end Angle

end Quantum