import SciLean

inductive Expr {R : Type} (atoms : List R)
  | num (n : ℕ)
  | add (x y : Expr atoms)
  | mul (x y : Expr atoms)
  | atom (i : ℕ)

def Expr.toRing {R : Type} [Ring R] (atoms : List R) (e : Expr atoms)  : R :=
  match e with
  | .num n => (n:R)
  | .add x y => x.toRing atoms + y.toRing atoms
  | .mul x y => x.toRing atoms * y.toRing atoms
  | .atom i => atoms.getD i 0

@[data_synth out e]
structure LiftExpr {R} [Ring R] (atoms : List R) (x : R) (e : Expr atoms) : Prop where
  to_ring : e.toRing atoms = x


variable {R} [Ring R] (atoms : List R)

@[data_synth]
theorem lift_num (n : Nat) : LiftExpr atoms (n : R) (.num n) where
  to_ring := by simp[Expr.toRing]


@[data_synth]
theorem lift_mul (x y : R) (hx : LiftExpr atoms x xe) (hy : LiftExpr atoms y ye) :
    LiftExpr atoms (x * y) (.mul xe ye) where
  to_ring := by simp[Expr.toRing,hx.to_ring,hy.to_ring]

@[data_synth]
theorem lift_add (x y : R) (hx : LiftExpr atoms x xe) (hy : LiftExpr atoms y ye) :
    LiftExpr atoms (x + y) (.add xe ye) where
  to_ring := by simp[Expr.toRing,hx.to_ring,hy.to_ring]


@[data_synth out n]
structure IsAtomExpr {R} [Ring R] (atoms : List R) (x : R) (n : ℕ) : Prop where
  hn : n < atoms.length
  is_atom : atoms[n] = x


@[data_synth]
theorem isAtom_zero {R} [Ring R] (atoms : List R) (x : R) : IsAtomExpr (x :: atoms) x 0 := by
  constructor <;> simp

@[data_synth]
theorem isAtom_succ {R} [Ring R] (a : R) (atoms : List R) (x : R) (n : ℕ) (hx : IsAtomExpr atoms x n) :
    IsAtomExpr (a :: atoms) x (n+1) := by
  constructor <;> simp[hx.1,hx.2]


open Classical in
@[data_synth]
theorem lift_atom (x : R) {n} (hx : IsAtomExpr atoms x n) :
    LiftExpr atoms (x) (.atom n) where
  to_ring := by simp_all[Expr.toRing,hx.1,hx.2]


variable (n m : ℕ) (x y z : ℝ)

#check (LiftExpr [x,y,z] (x) _) rewrite_by data_synth
#check (LiftExpr [x,y,z] (y) _) rewrite_by data_synth
#check (LiftExpr [x,y,z] (z) _) rewrite_by data_synth
#check (LiftExpr [x,y,z] (x*z) _) rewrite_by data_synth

#check (LiftExpr [x,y,z] (((n:ℝ)+(n:ℝ))*(m:ℝ)*x*x*x*y) _) rewrite_by data_synth


theorem replace_with_expr {R} [Ring R] (atoms : List R) (x : R) {ex} (hx : LiftExpr atoms x ex) :
  x = ex.toRing atoms := by simp[hx.1]

example (x y : ℝ) : x*x*y = (((Expr.atom 0).mul (Expr.atom 0)).mul (Expr.atom 1) : Expr [x,y]).toRing := by
   rw[replace_with_expr [x,y] (x*x*y) (by data_synth)]

def Expr.toString {R : Type} {atoms : List R} (e : Expr atoms) : String :=
  match e with
  | .num n => s!"{n}"
  | .add x y => s!"({x.toString} + {y.toString})"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .atom i => s!"x{i}"


def exprToString {R} [Ring R] (atoms : List R) (x : R) {ex} (hx : LiftExpr atoms x ex := by data_synth) :
  String := ex.toString

def a : ℝ := 34
def b : ℝ := 134
def c : ℝ := 34


#eval exprToString [a,b,c] ((2:ℕ) * a * a + (3:ℕ))
