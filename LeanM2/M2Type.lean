import SciLean


class M2Type (T : Type*) (M2T : outParam Type*) where
  toLean : M2T → T
  repr : String



namespace IntM2

instance : M2Type ℤ ℤ where
  toLean e := e
  repr := "ZZ"

alias M2Int := Int

end IntM2


namespace RatM2

instance : M2Type ℚ ℚ where
  toLean e := e
  repr := "QQ"

alias M2Rat := Rat

end RatM2


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



noncomputable
instance : M2Type ℝ M2Real where
  toLean e := e.toReal
  repr := "RR"


end RealM2




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



def toString' (r : M2Complex) : String :=
  match r with
  | .rat q => toString q
  | .sqrt x => "sqrt(" ++ toString' x ++ ")"
  | .log arg => "log(" ++ toString' arg ++ ")"
  | .exp x => "exp(" ++ toString' x ++ ")"
  | .pi => "π"
  | .i => "i"
  | .add x y => "(" ++ toString' x ++ " + " ++ toString' y ++ ")"
  | .mul x y => "(" ++ toString' x ++ " * " ++ toString' y ++ ")"
  | .pow x y => "(" ++ toString' x ++ "^" ++ toString' y ++ ")"
  | .sub x y => "(" ++ toString' x ++ " - " ++ toString' y ++ ")"
  | .div x y => "(" ++ toString' x ++ "/" ++ toString' y ++ ")"

instance : ToString M2Complex where
  toString r :=  toString' r



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



noncomputable
instance : M2Type ℂ M2Complex where
  toLean e := e.toComplex
  repr := "CC"


end ComplexM2




open IntM2 RatM2 RealM2 ComplexM2 M2Type


/--
This effectivelly defines inverse function of `M2Type.toLean`, i.e. for give `x : R` find `m : M2R`
such that `toLean m = x`.
-/
@[data_synth out m]
structure LiftM2 {R M2R} [M2Type R M2R] (x : R) (m : M2R) : Prop where
  to_lean : toLean m = x


namespace IntSynthThms

@[data_synth]
theorem lift_int (z:ℤ) : LiftM2 (z:ℤ) (z : ℤ) where
  to_lean := by simp[M2Type.toLean]

end IntSynthThms


namespace RatSynthThms

@[data_synth]
theorem lift_rat (q : ℚ) : LiftM2 (q : ℚ) (q : ℚ) where
  to_lean := by simp[M2Type.toLean]

end RatSynthThms


namespace RealSynthThms

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

end RealSynthThms




namespace ComplexSynthThms


@[data_synth]
theorem lift_rat (q : ℚ) : LiftM2 (q : ℂ) (.rat q) where
  to_lean := by simp[M2Complex.toComplex, M2Type.toLean]

@[data_synth]
theorem lift_sqrt (x : ℂ) (hx : LiftM2 x xe) : LiftM2 (x^(1/2) : ℂ) (.sqrt xe) where
  to_lean := by
    have := hx.to_lean
    simp_all[M2Complex.toComplex,hx.to_lean,M2Type.toLean]


@[data_synth]
theorem lift_log (x : ℂ) (hx : LiftM2 x xe) : LiftM2 (Complex.log x : ℂ) (.log xe) where
  to_lean := by
    have := hx.to_lean
    simp_all[M2Complex.toComplex,hx.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_exp (x : ℂ) (hx : LiftM2 x xe) : LiftM2 (Complex.exp x : ℂ) (.exp xe) where
  to_lean := by
    have := hx.to_lean
    simp_all[M2Complex.toComplex,hx.to_lean,M2Type.toLean]

@[data_synth]
theorem lift_pi : LiftM2 (Real.pi : ℂ) (.pi) where
  to_lean := by simp[M2Complex.toComplex,M2Type.toLean]


@[data_synth]
theorem lift_i : LiftM2 (Complex.I : ℂ) (.i) where
  to_lean := by simp[M2Complex.toComplex,M2Type.toLean]

@[data_synth]
theorem lift_add (x y : ℂ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x + y : ℂ) (.add xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all[M2Complex.toComplex, hx.to_lean, hy.to_lean, M2Type.toLean]


@[data_synth]
theorem lift_mul (x y : ℂ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x * y : ℂ) (.mul xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all[M2Complex.toComplex, hx.to_lean, hy.to_lean, M2Type.toLean]

@[data_synth]
theorem lift_pow (x y : ℂ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x ^ y : ℂ) (.pow xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Complex.toComplex, hx.to_lean, hy.to_lean, M2Type.toLean]

@[data_synth]
theorem lift_sub (x y : ℂ) (hx : LiftM2 x xe) (hy : LiftM2 y ye) :
  LiftM2 (x - y : ℂ) (.sub xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Complex.toComplex, hx.to_lean, hy.to_lean, M2Type.toLean]

@[data_synth]
theorem lift_div (x y : ℂ) (hx : LiftM2 x xe) (hy : LiftM2 y ye):
  LiftM2 (x / y : ℂ) (.div xe ye) where
  to_lean := by
    have := hx.to_lean
    have := hy.to_lean
    simp_all [M2Complex.toComplex, hx.to_lean, hy.to_lean, M2Type.toLean]


end ComplexSynthThms








variable {R M2R} [M2Type R M2R] [ToString M2R]
@[inline]
def partialToString (x : R) {m : M2R} (hx : LiftM2 x m := by data_synth) : String := toString m


#eval partialToString ((2:ℚ):ℝ)


#eval partialToString (Real.exp ((3:ℚ)*(2:ℚ) : ℝ))
