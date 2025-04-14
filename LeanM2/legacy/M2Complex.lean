import SciLean


namespace ComplexM2

inductive M2Complex
| rat (q : ℚ)
| sqrt (x : M2Complex)
| log (arg : M2Complex)
| exp (x : M2Complex)
| pi : M2Complex
| i : M2Complex
| add (x y : M2Complex) : M2Complex
| mul (x y : M2Complex) : M2Complex
| pow (x y : M2Complex) : M2Complex
| sub (x y : M2Complex) : M2Complex
| div (x y : M2Complex) : M2Complex
  deriving Inhabited, Repr

instance : Inhabited M2Complex where
  default := M2Complex.rat 0

noncomputable def M2Complex.toComplex (r : M2Complex)  : ℂ :=
  match r with
  | .rat q => (q : ℂ)
  | .sqrt x => (x.toComplex)^(1/2)
  | .log arg => arg.toComplex.log
  | .exp x => x.toComplex.exp
  | .pi => (Real.pi : ℂ)
  | .i => Complex.I
  | .add x y => x.toComplex + y.toComplex
  | .mul x y => x.toComplex * y.toComplex
  | .pow x y => x.toComplex ^ y.toComplex
  | .sub x y => x.toComplex - y.toComplex
  | .div x y => x.toComplex / y.toComplex

@[data_synth out m]
structure LiftM2Complex (x : ℂ) (m : M2Complex) : Prop where
  to_complex : m.toComplex = x


@[data_synth]
theorem lift_rat (q : ℚ) : LiftM2Complex (q : ℂ) (.rat q) where
  to_complex := by simp[M2Complex.toComplex]

@[data_synth]
theorem lift_sqrt (x : ℂ) (hx : LiftM2Complex x xe) : LiftM2Complex (x^(1/2) : ℂ) (.sqrt xe) where
  to_complex := by simp[M2Complex.toComplex,hx.to_complex]


@[data_synth]
theorem lift_log (x : ℂ) (hx : LiftM2Complex x xe) : LiftM2Complex (Complex.log x : ℂ) (.log xe) where
  to_complex := by simp[M2Complex.toComplex,hx.to_complex]

@[data_synth]
theorem lift_exp (x : ℂ) (hx : LiftM2Complex x xe) : LiftM2Complex (Complex.exp x : ℂ) (.exp xe) where
  to_complex := by simp[M2Complex.toComplex,hx.to_complex]

@[data_synth]
theorem lift_pi : LiftM2Complex (Real.pi : ℂ) (.pi) where
  to_complex := by simp[M2Complex.toComplex]


@[data_synth]
theorem lift_i : LiftM2Complex (Complex.I : ℂ) (.i) where
  to_complex := by simp[M2Complex.toComplex]

@[data_synth]
theorem lift_add (x y : ℂ) (hx : LiftM2Complex x xe) (hy : LiftM2Complex y ye) :
  LiftM2Complex (x + y : ℂ) (.add xe ye) where
  to_complex := by
    simp [M2Complex.toComplex, hx.to_complex, hy.to_complex]


@[data_synth]
theorem lift_mul (x y : ℂ) (hx : LiftM2Complex x xe) (hy : LiftM2Complex y ye) :
  LiftM2Complex (x * y : ℂ) (.mul xe ye) where
  to_complex := by
    simp [M2Complex.toComplex, hx.to_complex, hy.to_complex]

@[data_synth]
theorem lift_pow (x y : ℂ) (hx : LiftM2Complex x xe) (hy : LiftM2Complex y ye) :
  LiftM2Complex (x ^ y : ℂ) (.pow xe ye) where
  to_complex := by
    simp [M2Complex.toComplex, hx.to_complex, hy.to_complex]

@[data_synth]
theorem lift_sub (x y : ℂ) (hx : LiftM2Complex x xe) (hy : LiftM2Complex y ye) :
  LiftM2Complex (x - y : ℂ) (.sub xe ye) where
  to_complex := by
    simp [M2Complex.toComplex, hx.to_complex, hy.to_complex]

@[data_synth]
theorem lift_div (x y : ℂ) (hx : LiftM2Complex x xe) (hy : LiftM2Complex y ye):
  LiftM2Complex (x / y : ℂ) (.div xe ye) where
  to_complex := by
    simp [M2Complex.toComplex, hx.to_complex, hy.to_complex]



def toM2Complex (x : ℂ) {ex} (hx : LiftM2Complex x ex := by data_synth) :
  M2Complex := ex

end ComplexM2

open ComplexM2
/-
LiftM2Complex (Real.exp ↑2) (M2Complex.rat 2).exp : Prop
-/
#check (LiftM2Complex (Complex.exp (2:ℚ)) _) rewrite_by data_synth




/-
M2Complex.exp (M2Complex.rat 2)
-/
#eval toM2Complex (((1 : ℚ) * Complex.I))
#eval toM2Complex (Complex.exp (1:ℚ) ^  ((Real.pi : ℂ) * Complex.I))
#eval toM2Complex (2:ℚ)
