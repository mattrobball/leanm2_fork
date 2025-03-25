import SciLean
import Mathlib.Tactic.PolyRith

inductive Expr
  | num (n : ℤ)
  | add (x y : Expr )
  | mul (x y : Expr )
  | atom (i : ℕ)

def Expr.toRing {R : Type} [Ring R] (atoms : List R) (e : Expr)  : R :=
  match e with
  | .num n => (n:R)
  | .add x y => x.toRing atoms + y.toRing atoms
  | .mul x y => x.toRing atoms * y.toRing atoms
  | .atom i => atoms.getD i 0

@[data_synth out e]
structure LiftExpr {R} [Ring R] (atoms : List R) (x : R) (e : Expr) : Prop where
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


def Expr.toString (e : Expr) : String :=
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




def indiscernibles : List ℚ := List.range 3 |>.map (λ i => (i:ℚ))


def uh : String := exprToString [a,b,c] ((2:ℕ) * a * a + (3:ℕ))




-- -- idea: X^2 + 1 : Polynomial ℚ should be able to be written as x^2 + 1 : ℚ by rw X ↔ x:ℚ
-- def coer_poly (p : Polynomial ℚ) (x : ℚ) : ℚ := p.eval x

open Finset AddMonoidAlgebra

open Polynomial



/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
-- def eval' (p : ℕ[X]) (x : ℚ) : String :=
--   p.sum fun e a => exprToString ([x]) (a * x)





-- convert a polynomial object into this form, then eval it on some free var x,
-- then use our exprToString to get the string representation of the polynomial

-- #eval a'.eval 2




-- lemma todo (x : Polynomial ℚ): (x*x -1) = (x - 1) • (x + 1) := by polyrith


noncomputable def w : Polynomial ℚ := X


#eval exprToString [w] ((2:ℕ)*w + (1:ℕ))
