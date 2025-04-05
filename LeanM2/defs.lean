import SciLean

import Lean.Data.Json.Basic
import Mathlib.Data.FP.Basic
import LeanM2.M2Type
open Lean

open RealM2

inductive Expr (R : Type)
  | lift (r : R)
  | add (x y : Expr R)
  | sub (x y : Expr R)
  | mul (x y : Expr R)
  | zero
  | one
  | pow (x : Expr R) (n : ℕ)
  | atom (i : ℕ)
deriving Inhabited, Repr


def Expr.toRing {R S M2R: Type} [M2Type R M2R] [Ring S]  (f : R → S) (atoms : List S) (e : Expr M2R)  : S :=
  match e with
  | .lift r => f (M2Type.toLean r)
  | .add x y => x.toRing f atoms + y.toRing f atoms
  | .sub x y => x.toRing f atoms - y.toRing f atoms
  | .mul x y => x.toRing f atoms * y.toRing f atoms
  | .zero => (0 : S)
  | .one => (1 : S)
  | .pow x n => (x.toRing f atoms)^n
  | .atom i => atoms.getD i 0

@[data_synth out e]
structure LiftExpr {R S M2R} [M2Type R M2R] [Ring S] (f : R→ S) (atoms : List S) (x : S) (e : Expr M2R) : Prop where
  to_ring : e.toRing f atoms = x

variable {R} {S} [M2Type R M2R] [Ring S] (atoms : List S) (f : R → S)

@[data_synth]
theorem lift_lift (r : R)  (hr : LiftM2 r xr):
    LiftExpr f atoms (f r) (.lift xr) where
  to_ring := by
    simp[Expr.toRing, hr.to_lean]

@[data_synth]
theorem lift_mul (x y : S) (hx : LiftExpr f atoms x xe) (hy : LiftExpr f atoms y ye) :
    LiftExpr f atoms (x * y) (.mul xe ye) where
  to_ring := by simp[Expr.toRing,hx.to_ring,hy.to_ring]

@[data_synth]
theorem lift_add (x y : S) (hx : LiftExpr f atoms x xe) (hy : LiftExpr f atoms y ye) :
    LiftExpr f atoms (x + y) (.add xe ye) where
  to_ring := by simp[Expr.toRing,hx.to_ring,hy.to_ring]

@[data_synth]
theorem lift_sub (x y : S) (hx : LiftExpr f atoms x xe) (hy : LiftExpr f atoms y ye) :
    LiftExpr f atoms (x - y) (.sub xe ye) where
  to_ring := by
    simp[Expr.toRing,hx.to_ring,hy.to_ring,Mathlib.Tactic.RingNF.add_neg x y]

@[data_synth]
theorem lift_neg (x : S) (hx : LiftExpr f atoms x xe) :
    LiftExpr f atoms (-x) (.sub .zero xe) where
  to_ring := by
    simp[Expr.toRing,hx.to_ring,Mathlib.Tactic.RingNF.add_neg x]

@[data_synth]
theorem lift_zero :
    LiftExpr f atoms (0 : S) (.zero) where
  to_ring := by simp[Expr.toRing]

@[data_synth]
theorem lift_one :
    LiftExpr f atoms (1 : S) (.one) where
  to_ring := by simp[Expr.toRing]

@[data_synth]
theorem lift_pow (x : S) (n : ℕ) (hx : LiftExpr f atoms x xe) :
    LiftExpr f atoms (x ^ n) (.pow xe n) where
  to_ring := by simp[Expr.toRing,hx.to_ring]

@[data_synth out n]
structure IsAtomExpr {S} [Ring S]  (atoms : List S) (x : S) (n : ℕ) : Prop where
  hn : n < atoms.length
  is_atom : atoms[n] = x

@[data_synth]
theorem isAtom_zero {S} [Ring S]  (atoms : List S) (x : S) : IsAtomExpr (x :: atoms) x 0 := by
  constructor <;> simp

@[data_synth]
theorem isAtom_succ {S} [Ring S]  (a : S) (atoms : List S) (x : S) (n : ℕ) (hx : IsAtomExpr atoms x n) :
    IsAtomExpr (a :: atoms) x (n+1) := by
  constructor <;> simp[hx.1,hx.2]

open Classical in
@[data_synth]
theorem lift_atom (x : S) {n} (hx : IsAtomExpr atoms x n) :
    LiftExpr f atoms x (.atom n) where
  to_ring := by simp_all[Expr.toRing,hx.1,hx.2]

def Expr.toString {R} [ToString R] (e : Expr R) : String :=
  match e with
  | .lift r => s!"{r}"
  | .pow x n => s!"({x.toString})^{n}"
  | .add x y => s!"({x.toString} + {y.toString})"
  | .sub x y =>
    if x.toString == y.toString then
      s!"0"
    else
      s!"({x.toString} - {y.toString})"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .atom i => s!"x{i}"
  | .zero => s!"0"
  | .one => s!"1"




-- class ToM2 (α : Type u) where
--   toM2 (x : α) {ex} (hx : LiftM2 x ex := by data_synth) : M2





instance {R}  [ToString R] : ToString (Expr R) where
  toString := Expr.toString

-- def partialToString (x : ℝ)  {ex} (hx : LiftM2Real x ex := by data_synth) : String :=
--   toString ex






def toExpr {R S M2R} [M2Type R M2R] [Ring S]  (f : R→  S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  Expr M2R := ex

def exprToString {R S M2R} [ToString M2R] [M2Type R M2R] [Ring S]  (f : R→  S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  String := ex.toString

-- def exprToString {R S} [ToString R]  [Ring S]  (f : R → S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
--   String := ex.toString

-- def partialExprToString {R S} [Ring S]  (f : R → S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) (hx : LiftM2Real ex _ := by data_synth):
--   String := ex.toString






structure IdExpr (R : Type)  where
  generators : List (Expr R)

instance : Inhabited (IdExpr R) where
  default := ⟨[]⟩

def IdExpr.toIdeal {R S M2R: Type} [Ring S] [M2Type R M2R] [DecidableEq S] (f : R → S) (atoms : List S) (I : IdExpr M2R)  : Ideal S :=
  Ideal.span ((I.generators.map (fun e => e.toRing f atoms)).toFinset.toSet)

@[data_synth out eI]
structure LiftIdExpr {R S M2R} [Ring S] [M2Type R M2R] [DecidableEq S] (f : R → S) (atoms : List S) (I : Ideal S) (eI : IdExpr M2R) : Prop where
  to_ideal : eI.toIdeal f atoms = I

variable [DecidableEq S]



@[data_synth out generators]
structure IsIdExpr (I : Ideal S) (generators : List (Expr M2R)) : Prop where
  eq : I = Ideal.span (generators.map (fun g => g.toRing f atoms)).toFinset


@[data_synth]
theorem isId_nil : IsIdExpr atoms f (Ideal.span {}) [] := by
  constructor
  congr
  simp



@[data_synth]
theorem isId_singleton (g : S) (hg : LiftExpr f atoms g ge)
  : IsIdExpr atoms f (Ideal.span (Singleton.singleton g)) [ge] := by
  constructor
  congr
  simp
  exact hg.to_ring.symm



@[data_synth]
theorem isId_insert (g : S) (hg : LiftExpr f atoms g ge) (rest : Set S) (hrest : IsIdExpr atoms f (Ideal.span rest) restList)
  : IsIdExpr atoms f (Ideal.span (insert g rest)) (ge :: restList) := by
  constructor
  simp only [List.map_cons, List.toFinset_cons,Finset.coe_insert,Ideal.span_insert,hg.to_ring, hrest.1]



open Classical in
@[data_synth]
theorem lift_ideal (I : Ideal S) {generators} (hI : IsIdExpr atoms f I generators) :
    LiftIdExpr f atoms I ⟨generators⟩ where
  to_ideal := by
    simp_all[IdExpr.toIdeal,hI.1, Expr.toRing]




def IdExpr.toString [ToString M2R] (I : IdExpr M2R) : String :=
  s!"ideal({",".intercalate (I.generators.map (fun e => e.toString))})"

def toIdExpr (I : Ideal S) {eI} (hx : LiftIdExpr f atoms I eI := by data_synth) :
  IdExpr M2R := eI

def IdExprToString [ToString M2R] (I : Ideal S) {eI} (hx : LiftIdExpr f atoms I eI := by data_synth) :
  String := eI.toString






def atoms' :List ℚ := []
def f' := RingHom.id ℚ


#check (IsIdExpr atoms' f' (Ideal.span {}) _) rewrite_by data_synth

set_option trace.Meta.Tactic.data_synth true



#check (IsIdExpr atoms' f' (Ideal.span {f' (1:ℚ)}) _) rewrite_by data_synth

#check (IsIdExpr atoms' f' (Ideal.span {f' (1:ℚ), f' (2:ℚ)}) _) rewrite_by data_synth

#check LiftIdExpr f' atoms' (Ideal.span {f' (1:ℚ), f' (2:ℚ)}) _ rewrite_by data_synth

#eval toExpr f' atoms' (2:ℚ) -- this should work

#check LiftExpr f' atoms' (f' (2:ℚ)) _ rewrite_by data_synth

#check LiftM2 (2:ℚ) _ rewrite_by data_synth -- this should work, since 2 is in the ideal

def atoms'' :List ℝ := []

noncomputable def f'' := RingHom.id ℝ

#check (IsIdExpr atoms'' f'' (Ideal.span {}) _) rewrite_by data_synth

set_option trace.Meta.Tactic.data_synth true

#eval partialToString (Real.sqrt (1:ℚ):ℝ)

#eval toExpr f'' atoms'' (f'' (Real.sqrt (2:ℚ)) * f'' (1:ℚ)) -- this should work

#check LiftExpr f'' atoms'' (f'' (1:ℚ)) _ rewrite_by data_synth

#check (IsIdExpr atoms'' f'' (Ideal.span {f'' (1 : ℚ)}) _) rewrite_by data_synth

#check (IsIdExpr atoms'' f'' (Ideal.span {f'' (1: ℚ) , f'' (2 : ℚ)}) _) rewrite_by data_synth

#check LiftIdExpr f'' atoms'' (Ideal.span {f'' (1:ℚ), f'' (2:ℚ)}) _ rewrite_by data_synth

#eval exprToString f'' atoms'' (f'' (2:ℚ) + f'' (Real.sqrt ((1 : ℚ))))





def atoms''' :List ℂ := []

noncomputable def f''' := RingHom.id ℂ

#check (IsIdExpr atoms''' f''' (Ideal.span {}) _) rewrite_by data_synth

set_option trace.Meta.Tactic.data_synth true

#eval partialToString (((1:ℚ):ℂ)^(1/2))

#eval toExpr f''' atoms''' (f''' ((2:ℚ)^(1/2)) * f''' (1:ℚ)) -- this should work

#check LiftExpr f''' atoms''' (f''' (1:ℚ)) _ rewrite_by data_synth

#check (IsIdExpr atoms''' f''' (Ideal.span {f''' (1 : ℚ)}) _) rewrite_by data_synth

#check (IsIdExpr atoms''' f''' (Ideal.span {f''' (1: ℚ) , f''' (2 : ℚ)}) _) rewrite_by data_synth

#check LiftIdExpr f''' atoms''' (Ideal.span {f''' (1:ℚ), f''' (2:ℚ)}) _ rewrite_by data_synth

#eval exprToString f''' atoms''' (f''' (2:ℚ) + f''' ((1 : ℚ)^(1/2)))




noncomputable def X : Polynomial ℚ:= Polynomial.X
noncomputable def vars :List (Polynomial ℚ) := [X]
noncomputable def lift : RingHom ℚ (Polynomial ℚ):= Polynomial.C

#check (IsIdExpr [X] lift (Ideal.span {X^2}) _) rewrite_by data_synth

#check LiftIdExpr lift [X] (Ideal.span {X^2}) _ rewrite_by data_synth


#eval exprToString lift [X] (lift 2)
#eval IdExprToString [X] lift (Ideal.span {X^2})
