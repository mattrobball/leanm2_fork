import LeanM2.defs
import LeanM2.parser
import LeanM2.toM2
import Lean.PrettyPrinter.Delaborator.Basic
import Mathlib.Tactic.Use

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

open Qq Rat in
def Expr.QtoLeanExpr {S: Q(Type)} {hS:Q(Ring $S)}  (f : Q(RingHom ℚ $S)) (atoms : List Q($S)) (e : Expr ℚ)  : MetaM Lean.Expr := do

  let output := match e with
  | .lift r => do
    let num :ℤ := r.num
    let denom :ℤ := r.den
    let r' := q($num /. $denom)
    mkAppM' f #[r']
  | .add x y => do
    let fst ← x.QtoLeanExpr f atoms
    let snd ← y.QtoLeanExpr f atoms
    mkAppM ``HAdd.hAdd #[fst, snd]
  | .mul x y => do
    let fst ← x.QtoLeanExpr f atoms
    let snd ← y.QtoLeanExpr f atoms
    mkAppM ``HMul.hMul #[fst, snd]
  | .pow x n => do
    let base ← x.QtoLeanExpr f atoms
    let n' := mkNatLit n
    mkAppM ``HPow.hPow #[base, n']
  | .atom i =>
    let df := mkNatLit i
    pure <| atoms.getD i df

  output


open Qq Rat in
def Expr.QtoLeanExpr' (f : Lean.Expr) (atoms : List Lean.Expr) (e : Expr ℚ)  : MetaM Lean.Expr := do

  let output := match e with
  | .lift r => do
    let num :ℤ := r.num
    let denom :ℤ := r.den
    let r' := q($num /. $denom)
    mkAppM ``DFunLike.coe #[f, r']
  | .add x y => do
    let fst ← x.QtoLeanExpr' f atoms
    let snd ← y.QtoLeanExpr' f atoms
    mkAppM ``HAdd.hAdd #[fst, snd]
  | .mul x y => do
    let fst ← x.QtoLeanExpr' f atoms
    let snd ← y.QtoLeanExpr' f atoms
    mkAppM ``HMul.hMul #[fst, snd]
  | .pow x n => do
    let base ← x.QtoLeanExpr' f atoms
    let n' := mkNatLit n
    mkAppM ``HPow.hPow #[base, n']
  | .atom i =>
    let df := mkNatLit i
    pure <| atoms.getD i df

  output


open Lean Meta Elab Tactic Conv Qq in
@[tactic leanM2Stx]
unsafe def leanM2Tactic : Tactic
| `(tactic| lean_m2 $lift:term $atoms:term) => do
  let atoms ← elabTerm atoms none
  let lift ← elabTerm lift none
  -- let rhs ← getRhs
  let (ideal, elem) ← getMem
  let (_,_,i'') := ideal
  -- logInfo s!"{i.dbgToString}\n\n{i'.dbgToString}\n\n{i''.dbgToString}\n\n"
  -- logInfo s!"{elem.dbgToString}\n\n"

  let mut polynomial : Expr ℚ := default
  let mut ideal : IdExpr ℚ := default
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
    let expr ← evalExpr (_root_.Expr Rat) q(_root_.Expr Rat) result
    polynomial := expr
    -- logInfo s!"{expr.toString}"
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

    let expr ← evalExpr (_root_.IdExpr Rat) q(_root_.IdExpr Rat) result
    ideal := expr
  catch _ =>
    throwError m!"invalid expression {result}"


  let atoms' := parseExprList atoms
  let cmd := s!"R=QQ{if atoms'.length == 0 then "" else s!"{List.range atoms'.length |>.map (fun i => s!"x{i}")}"}\nf={polynomial.toString}\nI={ideal.toString}\nG=groebnerBasis I\nf % G\nf//G"
  logInfo s!"{cmd}"
  let res? ← idealMemM2' cmd
  if res?.isNone then
    logError s!"Not in ideal"
  else
    let arr := res?.get!
    -- logInfo s!"{arr}"


    let idealGenerators : Array (Expr ℚ) := ideal.generators.toArray

    let mut mappedRes : Array (Expr ℚ × String) := Array.mkArray idealGenerators.size (Expr.lift 0, "0")
    for (_, (coeff, idx)) in arr do
      let exp := idealGenerators.get! idx
      mappedRes := mappedRes.set! idx (exp, coeff)
    -- logInfo s!"{mappedRes}"

    let mappedRes'_opt : Array (Expr ℚ × Option (Expr ℚ)) := mappedRes.map (fun (a,b) =>
      let parsed := parsePolynomial b |>.toOption
      (a, parsed)
    )

    if not (mappedRes'_opt.all (fun (_, b) => b.isSome)) then
      logError s!"failed to parse polynomial coefficients: {mappedRes'_opt.filter (fun (_, b) => b.isNone)|>.map (fun (a,b) => a.toString)}"

    let mappedRes' : Array (Expr ℚ × Expr ℚ) := mappedRes'_opt.map (fun (a,b) => (a, b.get!))
    logInfo s!"{" + ".intercalate <|  mappedRes'.toList.map (fun (a,b) => s!"({b.toString} * {a.toString})")}"

    let mappedRes'' :Array (Lean.Expr × Lean.Expr) ←  mappedRes'.mapM (fun (a,b) => do
      let a' ← a.QtoLeanExpr' lift atoms' -- TODO: fix this
      let b' ← b.QtoLeanExpr' lift atoms'
      pure (a', b')
    )

    -- logInfo m!"{mappedRes''}"

    let mappedRes''' : Array Term ←  mappedRes''.mapIdxM (fun i (_, coeff) => do
      let neg ← if i < mappedRes''.size - 1 then
        mkAppM ``Neg.neg #[coeff]
      else
        pure coeff

      -- mkAppM ``Exists.intro xs
      let negTerm ← Lean.PrettyPrinter.delab neg
      return negTerm
    )

    -- logInfo m!"{mappedRes'''}"


    -- Run the simp tactic with the specified lemmas
    evalTactic (← `(tactic| simp [Ideal.mem_span_insert', Ideal.mem_span_singleton']))

    Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) (mappedRes'''.toList)

    evalTactic (← `(tactic| simp))

    -- Check if there are any goals left, and run ring if needed
    let gs ← getGoals
    if !gs.isEmpty then
      evalTactic (← `(tactic| ring))







  pure ()
| _ =>
  throwUnsupportedSyntax







set_option trace.Meta.Tactic.data_synth false

example (x y : ℚ) : x^2*y ∈ Ideal.span {x,y}  := by
  lean_m2 (RingHom.id ℚ) [x,y]



example (x y z: ℚ) : x^2+y ∈ Ideal.span {x^2,y}  := by
  lean_m2 (RingHom.id ℚ) [x,y,z]












example (x y z : ℚ) : x^2*y+y*x ∈ Ideal.span {x, y, z}  := by
  lean_m2 (RingHom.id ℚ) [x,y,z]



example (x y z : ℚ) : x^2*y+y*x ∈ Ideal.span {x, y, z}  := by
  simp[Ideal.mem_span_insert',Ideal.mem_span_singleton']
  apply Exists.intro (-y)
  apply Exists.intro (-x^2)
  apply Exists.intro (0)
  ring


example (a b c d e f : ℚ) : a^3*c+a^2*b*d+(RingHom.id ℚ (-1))*a^2*e*f+a*d*e^2+(RingHom.id ℚ (-1))*a*c*d*f ∈ Ideal.span {a^2+b*c+(RingHom.id ℚ (-1))*d*e, a*b+c*d+(RingHom.id ℚ (-1))*e*f, a*c+b*d+(RingHom.id ℚ (-1))*f^2}  := by
  lean_m2 (RingHom.id ℚ) [a,b,c,d,e,f]


example (a b c d e f : ℚ) : a^4+a^2*b*c+(RingHom.id ℚ (-1))*a^2*d*e+a*b^3+b^2*c*d+(RingHom.id ℚ (-1))*b^2*e*f+a*c^3+b*c^2*d+(RingHom.id ℚ (-1))*c^2*f^2 ∈ Ideal.span {a^2+b*c+(RingHom.id ℚ (-1))*d*e, a*b+c*d+(RingHom.id ℚ (-1))*e*f, a*c+b*d+(RingHom.id ℚ (-1))*f^2}  := by
  lean_m2 (RingHom.id ℚ) [a,b,c,d,e,f]
