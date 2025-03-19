import SciLean
import LeanM2.Basic

namespace M2Elem



instance (R : Type) [ToM2Ring R] : ToM2Elem R R where
  toM2Elem := fun r => ⟨ToM2Ring.toM2Ring R, r.toString⟩




inductive Expr (R : Type) [Ring R] [ToM2Ring R]
  | lift (r : R)
  | add (x y : Expr R)
  | mul (x y : Expr R)
  | pow (x : Expr R) (n : ℕ)
  | atom (i : ℕ)

--todo make R a subring (check if Polynomial R is a superring of R, if so ok. else add a argument for a lifting function from R->S)
def Expr.toRing {R S: Type} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (e : Expr R)  : S :=
  match e with
  | .lift r => f r
  | .add x y => x.toRing f atoms + y.toRing f atoms
  | .mul x y => x.toRing f atoms * y.toRing f atoms
  | .pow x n => (x.toRing f atoms)^n
  | .atom i => atoms.getD i 0

@[data_synth out e]
structure LiftExpr {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) (e : Expr R) : Prop where
  to_ring : e.toRing f atoms = x


variable {R} [Ring R] [ToM2Ring R] {S} [Ring S] [ToM2Ring S] (atoms : List S) (f : RingHom R S)

@[data_synth]
theorem lift_lift (r : R) :
    LiftExpr f atoms (f r) (.lift r) where
  to_ring := by simp[Expr.toRing]

@[data_synth]
theorem lift_mul (x y : S) (hx : LiftExpr f atoms x xe) (hy : LiftExpr f atoms y ye) :
    LiftExpr f atoms (x * y) (.mul xe ye) where
  to_ring := by simp[Expr.toRing,hx.to_ring,hy.to_ring]

@[data_synth]
theorem lift_add (x y : S) (hx : LiftExpr f atoms x xe) (hy : LiftExpr f atoms y ye) :
    LiftExpr f atoms (x + y) (.add xe ye) where
  to_ring := by simp[Expr.toRing,hx.to_ring,hy.to_ring]

@[data_synth]
theorem lift_pow (x : S) (n : ℕ) (hx : LiftExpr f atoms x xe) :
    LiftExpr f atoms (x ^ n) (.pow xe n) where
  to_ring := by simp[Expr.toRing,hx.to_ring]

@[data_synth out n]
structure IsAtomExpr {S} [Ring S] [ToM2Ring S] (atoms : List S) (x : S) (n : ℕ) : Prop where
  hn : n < atoms.length
  is_atom : atoms[n] = x


@[data_synth]
theorem isAtom_zero {S} [Ring S] [ToM2Ring S] (atoms : List S) (x : S) : IsAtomExpr (x :: atoms) x 0 := by
  constructor <;> simp

@[data_synth]
theorem isAtom_succ {S} [Ring S] [ToM2Ring S] (a : S) (atoms : List S) (x : S) (n : ℕ) (hx : IsAtomExpr atoms x n) :
    IsAtomExpr (a :: atoms) x (n+1) := by
  constructor <;> simp[hx.1,hx.2]


open Classical in
@[data_synth]
theorem lift_atom (x : S) {n} (hx : IsAtomExpr atoms x n) :
    LiftExpr f atoms x (.atom n) where
  to_ring := by simp_all[Expr.toRing,hx.1,hx.2]


def Expr.toString {R} [Ring R] [ToM2Ring R] (e : Expr R) : String :=
  match e with
  | .lift r => s!"r" -- todo fix with M2Ring
  | .pow x n => s!"({x.toString}^{n})"
  | .add x y => s!"({x.toString} + {y.toString})"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .atom i => s!"x{i}"


def exprToString {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  String := ex.toString


end M2Elem
