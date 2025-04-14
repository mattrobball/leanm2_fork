import SciLean


namespace RealM2

inductive M2Real
| rat (q : ℚ)
| sqrt (x : M2Real)
| log (arg : M2Real)
| exp (x : M2Real)
| pi : M2Real
| add (x y : M2Real) : M2Real
| mul (x y : M2Real) : M2Real
| pow (x y : M2Real) : M2Real
| sub (x y : M2Real) : M2Real
| div (x y : M2Real) : M2Real
  deriving Inhabited, Repr

instance : Inhabited M2Real where
  default := M2Real.rat 0

def toString' (r : M2Real) : String :=
  match r with
  | .rat q => toString q
  | .sqrt x => "sqrt(" ++ toString' x ++ ")"
  | .log arg => "log(" ++ toString' arg ++ ")"
  | .exp x => "exp(" ++ toString' x ++ ")"
  | .pi => "π"
  | .add x y => "(" ++ toString' x ++ " + " ++ toString' y ++ ")"
  | .mul x y => "(" ++ toString' x ++ " * " ++ toString' y ++ ")"
  | .pow x y => "(" ++ toString' x ++ "^" ++ toString' y ++ ")"
  | .sub x y => "(" ++ toString' x ++ " - " ++ toString' y ++ ")"
  | .div x y => "(" ++ toString' x ++ "/" ++ toString' y ++ ")"

instance : ToString M2Real where
  toString r :=  toString' r


noncomputable def M2Real.toReal (r : M2Real)  : ℝ :=
  match r with
  | .rat q => (q : ℝ)
  | .sqrt x => x.toReal.sqrt
  | .log arg => arg.toReal.log
  | .exp x => x.toReal.exp
  | .pi => Real.pi
  | .add x y => x.toReal + y.toReal
  | .mul x y => x.toReal * y.toReal
  | .pow x y => x.toReal ^ y.toReal
  | .sub x y => x.toReal - y.toReal
  | .div x y => x.toReal / y.toReal


/--
Some elements of type `T` can be symbolically represented with elements of type `M2T`.
-/
class M2Type (T : Type*) (M2T : outParam Type*) where
  /--
  Convert an element of `M2T` back to Lean type `T`
  -/
  toLean : M2T → T

noncomputable
instance : M2Type ℝ M2Real where
  toLean e := e.toReal


open M2Type in
/--
This effectivelly defines inverse function of `M2Type.toLean`, i.e. for give `x : R` find `m : M2R`
such that `toLean m = x`.
-/
@[data_synth out m]
structure LiftM2 {R M2R} [M2Type R M2R] (x : R) (m : M2R) : Prop where
  to_lean : toLean m = x


@[data_synth]
theorem lift_rat (q : ℚ) : LiftM2 (q : ℝ) (.rat q) where
  to_lean := by simp[M2Real.toReal,M2Type.toLean]

@[data_synth]
theorem lift_sqrt (x : ℝ) (hx : LiftM2 x xe) : LiftM2 (Real.sqrt x : ℝ) (.sqrt xe) where
  to_lean := by have := hx.to_lean; simp_all[M2Real.toReal,hx.to_lean,M2Type.toLean]


@[data_synth]
theorem lift_log (x : ℝ) (hx : LiftM2 x xe) : LiftM2 (Real.log x : ℝ) (.log xe) where
  to_lean := by have := hx.to_lean; simp_all[M2Real.toReal,hx.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_exp (x : ℝ) (hx : LiftM2 x xe) : LiftM2 (Real.exp x : ℝ) (.exp xe) where
  to_lean := by have := hx.to_lean; simp_all[M2Real.toReal,hx.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_pi : LiftM2 (Real.pi : ℝ) (.pi) where
  to_lean := by simp[M2Real.toReal,M2Type.toLean]

@[data_synth]
theorem lift_add (x y : ℝ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x + y : ℝ) (.add xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Real.toReal, hx.to_lean, hy.to_lean,M2Type.toLean]


@[data_synth]
theorem lift_mul (x y : ℝ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x * y : ℝ) (.mul xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Real.toReal, hx.to_lean, hy.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_pow (x y : ℝ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x ^ y : ℝ) (.pow xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Real.toReal, hx.to_lean, hy.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_sub (x y : ℝ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x - y : ℝ) (.sub xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Real.toReal, hx.to_lean, hy.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_div (x y : ℝ) (hx : LiftM2 x xe) (hy : LiftM2 y ye):
  LiftM2 (x / y : ℝ) (.div xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Real.toReal, hx.to_lean, hy.to_lean,M2Type.toLean]





variable {R M2R} [M2Type R M2R] [ToString M2R]
@[inline]
def partialToString (x : R) {m : M2R} (hx : LiftM2 x m := by data_synth) : String := toString m


#eval partialToString ((2:ℚ):ℝ)


#eval partialToString (Real.exp ((3:ℚ)*(2:ℚ) : ℝ))
