import LeanM2.defs
import LeanM2.parser
import LeanM2.toM2
import LeanM2.M2Type
import Lean.PrettyPrinter.Delaborator.Basic
import Mathlib.Tactic.Use
import Mathlib.Tactic.Polyrith
import LeanM2.Expr2Expr


syntax (name:=leanM2Stx) "lean_m2" term : tactic


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

open Qq Rat



class ToLeanExpr (α : Type*) where
  toLeanExpr : α → Lean.Expr → MetaM Lean.Expr

namespace RatM2
open Qq in
def M2Rat.toLeanExpr : M2Rat → Lean.Expr → MetaM Lean.Expr := fun r => fun f =>
  let num :ℤ := r.num
  let denom :ℤ := r.den
  let r' := q($num /. $denom)
  mkAppM ``DFunLike.coe #[f, r']


instance : ToLeanExpr M2Rat where
  toLeanExpr := M2Rat.toLeanExpr

end RatM2


open Qq Rat in
def Expr.toLeanExpr' (S : Lean.Expr) (f : Lean.Expr) (atoms : List Lean.Expr) {α} [ToLeanExpr α] (e : Expr α)  : MetaM Lean.Expr := do
  let output := match e with
  | .lift r => do
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

def getM2R {M2R} (R : Type) [M2Type R M2R] : Type :=
  M2R

#reduce (types := true) getM2R ℝ



open Lean Meta Elab Tactic Conv Qq RatM2 in
@[tactic leanM2Stx]
unsafe def leanM2Tactic : Tactic
| `(tactic| lean_m2 $lift:term $atoms:term) => do
  let atoms ← elabTerm atoms none
  let lift ← elabTerm lift none
  let (ideal, elem) ← getMem
  let (_,_,i'') := ideal

  let inputM2Type : Lean.Expr × Lean.Expr ← match lift with
    | .lam _ type _ _ => do
        let M2T ← mkFreshExprMVar q(Type)
        let instType ← mkAppM ``M2Type #[type, M2T]
        let _ ← synthInstance instType
        logInfo M2T
        pure (type, M2T)
    | _ =>
      logError "failed to infer the input ring from the provided lift expression"
      default

  let (inputRing, inputM2Type) := inputM2Type



  let outputRing ← match getOutputRing i'' with
    | none => do
      logError "failed to find output ring from ideal expression"
      default
    | some or =>
      pure or

  let mut polynomial : Expr M2Rat := default
  let mut ideal : IdExpr M2Rat := default

  -- elem
  let e ← mkAppM ``LiftExpr #[lift, atoms, elem]
  let (xs,_,_) ← forallMetaTelescope (← inferType e)
  let e := e.beta xs


  let .some goal ← SciLean.Tactic.DataSynth.isDataSynthGoal? e | throwError "invalid goal"
  let .some r ← (SciLean.Tactic.DataSynth.dataSynth goal).runInMetaM
    | throwError m!"failed to lift expression {elem}"

  let result := r.xs[0]!
  checkNoFVars result (fun xs => m!"error: resulting expression contains fvars {xs}")

  try
    let expr ← evalExpr (_root_.Expr M2Rat) q(_root_.Expr M2Rat) result
    polynomial := expr
    logInfo s!"{expr.toString}"
  catch _ =>
    throwError m!"invalid expression {result}"


  -- ideal
  let e ← mkAppM ``LiftIdExpr #[lift, atoms, i'']
  let (xs,_,_) ← forallMetaTelescope (← inferType e)
  let e := e.beta xs

  let .some goal ← SciLean.Tactic.DataSynth.isDataSynthGoal? e | throwError "invalid goal"
  let .some r ← (SciLean.Tactic.DataSynth.dataSynth goal).runInMetaM
    | throwError m!"failed to lift expression {elem}"

  let result := r.xs[0]!
  checkNoFVars result (fun xs => m!"error: resulting expression contains fvars {xs}")


  try

    let expr ← evalExpr (_root_.IdExpr M2Rat) q(_root_.IdExpr M2Rat) result
    ideal := expr
  catch _ =>
    throwError m!"invalid expression {result}"


  let atoms' := parseExprList atoms
  let cmd := s!"R=QQ{if atoms'.length == 0 then "" else s!"{List.range atoms'.length |>.map (fun i => s!"x{i}")}"}\nf={polynomial.toString}\nI={ideal.toString}\nG=gb(I,ChangeMatrix=>true)\nf % G\n(getChangeMatrix G)*(f// groebnerBasis I)"
  -- logInfo s!"{cmd}"
  let res? ← idealMemM2' cmd
  if res?.isNone then
    logError s!"Not in ideal"
  else
    let arr := res?.get!
    logInfo s!"{arr}"


    let idealGenerators : Array (Expr M2Rat) := ideal.generators.toArray

    let mut mappedRes : Array (Expr M2Rat × String) := arr.mapIdx (fun idx coeff => (idealGenerators.get! idx, coeff))

    logInfo s!"{mappedRes}"

    let mappedRes'_opt : Array (Expr M2Rat × Option (Expr M2Rat)) := mappedRes.map (fun (a,b) =>
      let parsed := parsePolynomial M2Rat b |>.toOption
      (a, parsed)
    )

    if not (mappedRes'_opt.all (fun (_, b) => b.isSome)) then
      logError s!"failed to parse polynomial coefficients: {mappedRes'_opt.filter (fun (_, b) => b.isNone)|>.map (fun (a,_) => a.toString)}"

    let mappedRes' : Array (Expr M2Rat × Expr M2Rat) := mappedRes'_opt.map (fun (a,b) => (a, b.get!))
    logInfo s!"{" + ".intercalate <|  mappedRes'.toList.map (fun (a,b) => s!"({b.toString} * {a.toString})")}"

    let mappedRes'' :Array (Lean.Expr × Lean.Expr) ←  mappedRes'.mapM (fun (a,b) => do
      let a' ← a.toLeanExpr' outputRing lift atoms'
      let b' ← b.toLeanExpr' outputRing lift atoms'
      pure (a', b')
    )

    let mappedRes''' : Array Term ←  mappedRes''.mapIdxM (fun i (_, coeff) => do
      let neg ← if i < mappedRes''.size - 1 then
        mkAppM ``Neg.neg #[coeff]
      else
        pure coeff

      let negTerm ← Lean.PrettyPrinter.delab neg
      return negTerm
    )



    -- Run the simp tactic with the specified lemmas
    evalTactic (← `(tactic| simp [Ideal.mem_span_insert', Ideal.mem_span_singleton']))

    Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) (mappedRes'''.toList)

    -- evalTactic (← `(tactic| simp))

    -- Check if there are any goals left, and run ring if needed
    let gs ← getGoals
    if !gs.isEmpty then
      evalTactic (← `(tactic| ring))
    let gs ← getGoals
    if !gs.isEmpty then
      evalTactic (← `(tactic| simp))

  pure ()
| _ =>
  throwUnsupportedSyntax








set_option trace.Meta.Tactic.data_synth false





example (x y : ℚ) : x^2+y^2 ∈ Ideal.span {x,y}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y]



example (x y : ℚ) : x^3+y^3 ∈ Ideal.span {x+y}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y]

example (x y : Polynomial ℚ) : x^3+y^3 ∈ Ideal.span {x+y}  := by
  lean_m2 (fun (t:ℚ) => Polynomial.C t) [x,y]




example (x y z: ℚ) : x^2+y ∈ Ideal.span {x^2,y}  := by
  lean_m2 (RingHom.id ℚ) [x,y,z]


example (x y z : ℚ) : x^2*y+y*x ∈ Ideal.span {x, y, z}  := by
  lean_m2 (RingHom.id ℚ) [x,y,z]




example (a b c d e f : ℚ) : a^3*c+a^2*b*d-a^2*e*f+a*d*e^2-a*c*d*f
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2 (RingHom.id ℚ) [a,b,c,d,e,f]


example (a b c d e f : ℚ) : a^4+a^2*b*c-a^2*d*e+a*b^3+b^2*c*d-b^2*e*f+a*c^3+b*c^2*d-c^2*f^2
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2 (RingHom.id ℚ) [a,b,c,d,e,f]


example (x y : ℚ) (h : x+y = 0) : x^3 + y^3 = 0 := by
  have sufficient : x^3+y^3 ∈ Ideal.span {x+y} := by
    lean_m2 (RingHom.id ℚ) [x,y]
  apply Ideal.mem_span_singleton'.1 at sufficient
  simp [mul_zero,h] at sufficient
  linarith


example (a b c d e f : ℚ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  polyrith



example (a b c d e f : ℚ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  have sufficient : a*b*c*d - a*e*f*d ∈ Ideal.span {b*c-e*f} := by
    lean_m2 (RingHom.id ℚ) [a,b,c,d,e,f]
  apply Ideal.mem_span_singleton'.1 at sufficient
  simp [mul_zero,h] at sufficient
  linarith
