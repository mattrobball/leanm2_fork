import SciLean

inductive M2Real
| rat (q : ℚ)
| sqrt (x : M2Real)
| log (arg : M2Real)
| exp (x : M2Real)
| pi : M2Real

instance : Inhabited M2Real where
  default := M2Real.rat 0

noncomputable def M2Real.toReal (r : M2Real)  : ℝ :=
  match r with
  | .rat q => (q : ℝ)
  | .sqrt x => x.toReal.sqrt
  | .log arg => arg.toReal.log
  | .exp x => x.toReal.exp
  | .pi => Real.pi

@[data_synth out m]
structure LiftM2Real (x : ℝ) (m : M2Real) : Prop where
  to_real : m.toReal = x


@[data_synth]
theorem lift_rat (q : ℚ) : LiftM2Real (q : ℝ) (.rat q) where
  to_real := by simp[M2Real.toReal]

@[data_synth]
theorem lift_sqrt (x : ℝ) (hx : LiftM2Real x xe) : LiftM2Real (Real.sqrt x : ℝ) (.sqrt xe) where
  to_real := by simp[M2Real.toReal,hx.to_real]


@[data_synth]
theorem lift_log (x : ℝ) (hx : LiftM2Real x xe) : LiftM2Real (Real.log x : ℝ) (.log xe) where
  to_real := by simp[M2Real.toReal,hx.to_real]

@[data_synth]
theorem lift_exp (x : ℝ) (hx : LiftM2Real x xe) : LiftM2Real (Real.exp x : ℝ) (.exp xe) where
  to_real := by simp[M2Real.toReal,hx.to_real]

@[data_synth]
theorem lift_pi : LiftM2Real (Real.pi : ℝ) (.pi) where
  to_real := by simp[M2Real.toReal]


/-
LiftM2Real (Real.exp ↑2) (M2Real.rat 2).exp : Prop
-/
#check (LiftM2Real (Real.exp (2:ℚ)) _) rewrite_by data_synth


def toM2Real (x : ℝ) {ex} (hx : LiftM2Real x ex := by data_synth) :
  M2Real := ex


/-
M2Real.exp (M2Real.rat 2)
-/
#eval toM2Real (Real.exp (2:ℚ))
#eval toM2Real (2:ℚ)


structure M2Complex where
  re : M2Real
  im : M2Real
  deriving Inhabited


def toM2Complex (x : ℂ) {ex1 ex2} (hx : LiftM2Real x.re ex1 := by data_synth) (hy : LiftM2Real x.im ex2 := by data_synth) :
  M2Complex := ⟨ex1, ex2⟩


#eval toM2Complex (2)
#eval toM2Complex (2:ℚ)


alias M2Rational := Rat
alias M2Integer := Int



inductive M2Ring : Type
| ZZ : M2Ring
| QQ : M2Ring
| RR : M2Ring
| CC : M2Ring

inductive M2Elem : Type
| rat (q : M2Rational)
| int (z : M2Integer)
| real (r : M2Real)
| complex (c : M2Complex)

class ToM2Ring (R : Type) where
  toM2Ring : M2Ring
  toM2Elem : R → M2Elem

instance : ToM2Ring ℤ where
  toM2Ring := M2Ring.ZZ
  toM2Elem := M2Elem.int

instance : ToM2Ring ℚ where
  toM2Ring := M2Ring.QQ
  toM2Elem := M2Elem.rat

instance : ToM2Ring ℝ where
  toM2Ring := M2Ring.RR
  toM2Elem := M2Elem.real ∘ toM2Real

instance : ToM2Ring ℂ where
  toM2Ring := M2Ring.CC
