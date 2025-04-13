import LeanM2.defs
-- import LeanM2.parser
import LeanM2.toM2
import LeanM2.M2Type
import Lean.PrettyPrinter.Delaborator.Basic
import Mathlib.Tactic.Use


open Lean Meta
def checkNoFVars (e : Lean.Expr) (errMsg : Array Lean.Expr → MessageData) : MetaM Unit := do
  let fvarIds := (← e.collectFVars.run {}).2.fvarIds
  if ¬fvarIds.isEmpty then
    throwError (errMsg (fvarIds.map Lean.Expr.fvar))

  pure ()



open Lean Meta in
def _root_.SciLean.Tactic.DataSynth.DataSynthM.runInMetaM (e : SciLean.Tactic.DataSynth.DataSynthM α) : MetaM α := do
  e.runInSimpM.run (← Simp.mkDefaultMethods).toMethodsRef (← Simp.mkContext) (← ST.mkRef {})




@[inline] def mem? (p : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
  p.app5? ``Membership.mem

def matchMem? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) :=
  matchHelper? e fun e => return mem? e

open Lean Meta Elab  Tactic Conv Qq in
def getMem : TacticM ((Lean.Expr × Lean.Expr× Lean.Expr) × Lean.Expr) := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let type ← mvarId.getType
    let some (_, ideal, ideal', ideal'', elem) ← matchMem? type | throwError s!"invalid mem goal\n\n{type.dbgToString}"
    return ((ideal,ideal',ideal''), elem)

partial def parseExprList (data : Lean.Expr) (acc : List Lean.Expr := []) : List Lean.Expr :=
  let data' := data.app3? ``List.cons
  match data' with
  | some (_, arg, rest) =>
      parseExprList rest (arg :: acc)
  | none => acc.reverse


partial def parseExprIdealSpan' (data : Lean.Expr) (acc : List Lean.Expr := []) : List Lean.Expr :=
  let isEmpty := data.app2? ``EmptyCollection.emptyCollection
  if isEmpty.isSome then
    acc
  else
    let isSingle := data.app4? ``Singleton.singleton
    if isSingle.isSome then
      let (_, _, _, obj) := isSingle.get!
      obj :: acc
    else
      let data' := data.app5? ``Insert.insert
      if data'.isSome then
        let (_, _, _, obj, rest) := data'.get!
        parseExprIdealSpan' rest (obj :: acc)
      else
        []

partial def parseExprIdealSpan (data : Lean.Expr) : List Lean.Expr :=
  let data' := data.app3? ``Ideal.span
  match data' with
  | some (_, _, body) =>
      parseExprIdealSpan' body |>.reverse
  | none => []

open Qq Rat



class ToLeanExpr (α : Type*) where
  toLeanExpr : α → Lean.Expr → MetaM Lean.Expr


namespace IntM2
open Qq in
def M2Int.toLeanExpr : M2Int → Lean.Expr → MetaM Lean.Expr := fun r => fun f =>
  let r' : ℤ := r
  let num := ToExpr.toExpr r'
  mkAppM' f #[num]

instance : ToLeanExpr M2Int where
  toLeanExpr := M2Int.toLeanExpr

instance : ToLeanExpr ℤ where
  toLeanExpr := M2Int.toLeanExpr

end IntM2

namespace RatM2
open Qq in
def M2Rat.toLeanExpr : M2Rat → Lean.Expr → MetaM Lean.Expr := fun r => fun f =>
  let num :ℤ := r.q.num
  let denom :ℤ := r.q.den
  let r' := q($num /. $denom)
  mkAppM' f #[r']-- ``DFunLike.coe #[f, r']


instance : ToLeanExpr M2Rat where
  toLeanExpr := M2Rat.toLeanExpr

-- instance : ToLeanExpr ℚ where
--   toLeanExpr := fun q ↦ M2Rat.toLeanExpr ⟨q⟩

end RatM2
namespace RealM2
open Qq in
def M2Real.toLeanExpr : M2Real → Lean.Expr → MetaM Lean.Expr := fun r => fun f =>
  match r with
  | .rat r => do
    let num :ℤ := r.num
    let denom :ℤ := r.den
    let r' := q($num /. $denom)
    let coe_r' ← mkAppOptM ``Rat.cast #[q(ℝ), q(Real.instRatCast), r']
    mkAppM' f #[coe_r']
  | .sqrt r => do
    let r' ← M2Real.toLeanExpr r f
    mkAppM ``Real.sqrt #[r']
  | .log r => do
    let r' ← M2Real.toLeanExpr r f
    mkAppM ``Real.log #[r']
  | .exp r => do
    let r' ← M2Real.toLeanExpr r f
    mkAppM ``Real.exp #[r']
  | .pi => do
    mkAppM ``Real.pi #[]
  | .add x y => do
    let x' ← M2Real.toLeanExpr x f
    let y' ← M2Real.toLeanExpr y f
    mkAppM ``HAdd.hAdd #[x', y']
  | .mul x y => do
    let x' ← M2Real.toLeanExpr x f
    let y' ← M2Real.toLeanExpr y f
    mkAppM ``HMul.hMul #[x', y']
  | .pow x y => do
    let x' ← M2Real.toLeanExpr x f
    let y' ← M2Real.toLeanExpr y f
    mkAppM ``HPow.hPow #[x', y']
  | .sub x y => do
    let x' ← M2Real.toLeanExpr x f
    let y' ← M2Real.toLeanExpr y f
    mkAppM ``HSub.hSub #[x', y']
  | .div x y => do
    let x' ← M2Real.toLeanExpr x f
    let y' ← M2Real.toLeanExpr y f
    mkAppM ``HDiv.hDiv #[x', y']


instance : ToLeanExpr M2Real where
  toLeanExpr := M2Real.toLeanExpr


end RealM2

#check (Real.pi : ℂ)

#check ((2 : ℚ ) : ℂ)

namespace ComplexM2
open Qq in
def M2Complex.toLeanExpr : M2Complex → Lean.Expr → MetaM Lean.Expr := fun r => fun f =>
  match r with
  | .rat r => do
    let num :ℤ := r.num
    let denom :ℤ := r.den
    let r' := q($num /. $denom)
    let coe_r' ← mkAppOptM ``Rat.cast #[q(ℂ), q(Complex.instRatCast), r']
    mkAppM' f #[coe_r']
  | .sqrt r => do
    let r' ← M2Complex.toLeanExpr r f
    let exp := q(1 / 2)
    mkAppM ``HPow.hPow #[r',exp]
  | .log r => do
    let r' ← M2Complex.toLeanExpr r f
    mkAppM ``Complex.log #[r']
  | .exp r => do
    let r' ← M2Complex.toLeanExpr r f
    mkAppM ``Complex.exp #[r']
  | .pi => do
    let a ← mkAppM ``Real.pi #[]
    mkAppM ``Complex.ofReal #[a]
  | .i => do
    mkAppM ``Complex.I #[]
  | .add x y => do
    let x' ← M2Complex.toLeanExpr x f
    let y' ← M2Complex.toLeanExpr y f
    mkAppM ``HAdd.hAdd #[x', y']
  | .mul x y => do
    let x' ← M2Complex.toLeanExpr x f
    let y' ← M2Complex.toLeanExpr y f
    mkAppM ``HMul.hMul #[x', y']
  | .pow x y => do
    let x' ← M2Complex.toLeanExpr x f
    let y' ← M2Complex.toLeanExpr y f
    mkAppM ``HPow.hPow #[x', y']
  | .sub x y => do
    let x' ← M2Complex.toLeanExpr x f
    let y' ← M2Complex.toLeanExpr y f
    mkAppM ``HSub.hSub #[x', y']
  | .div x y => do
    let x' ← M2Complex.toLeanExpr x f
    let y' ← M2Complex.toLeanExpr y f
    mkAppM ``HDiv.hDiv #[x', y']


instance : ToLeanExpr M2Complex where
  toLeanExpr := M2Complex.toLeanExpr


end ComplexM2







open Qq Rat in
def Expr.toLeanExpr' (S : Lean.Expr) (f : Lean.Expr) (atoms : List Lean.Expr) {α} [ToLeanExpr α] (e : Expr α)  : MetaM Lean.Expr := do
  let output := match e with
  | .lift r => do
    -- logInfo m!"lifting fn {f}"
    ToLeanExpr.toLeanExpr r f
  | .add x y => do
    let fst ← x.toLeanExpr' S f atoms
    let snd ← y.toLeanExpr' S f atoms
    mkAppM ``HAdd.hAdd #[fst, snd]
  | .sub x y => do
    let fst ← x.toLeanExpr' S f atoms
    let snd ← y.toLeanExpr' S f atoms
    mkAppM ``HSub.hSub #[fst, snd]
  | .zero => do
    let x := mkNumeral S (0)
    x
  | .one => do
    let x := mkNumeral S (0)
    x
  | .mul x y => do
    let fst ← x.toLeanExpr' S f atoms
    let snd ← y.toLeanExpr' S f atoms
    mkAppM ``HMul.hMul #[fst, snd]
  | .pow x n => do
    let base ← x.toLeanExpr' S f atoms
    let n' := mkNatLit n
    mkAppM ``HPow.hPow #[base, n']
  | .atom i =>
    let df := mkNatLit i
    pure <| atoms.getD i df

  output




def getOutputRing (i : Lean.Expr) : Option Lean.Expr :=
  let output := i.app3? (`Ideal.span)
  match output with
  | some (outputRing,_,_) =>
    -- logInfo s!"outputRing: {outputRing.dbgToString}"
    outputRing
  | none => none
