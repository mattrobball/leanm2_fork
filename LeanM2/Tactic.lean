import LeanM2.defs
import LeanM2.parser
import LeanM2.toM2


syntax (name:=liftLhsStx) "lift_lhs" term: tactic
syntax (name:=liftRhsStx) "lift_rhs" term : tactic


open Lean Meta
def checkNoFVars (e : Lean.Expr) (errMsg : Array Lean.Expr → MessageData) : MetaM Unit := do
  let fvarIds := (← e.collectFVars.run {}).2.fvarIds
  if ¬fvarIds.isEmpty then
    throwError (errMsg (fvarIds.map Lean.Expr.fvar))

  pure ()



open Lean Meta in
def _root_.SciLean.Tactic.DataSynth.DataSynthM.runInMetaM (e : SciLean.Tactic.DataSynth.DataSynthM α) : MetaM α := do
  e.runInSimpM.run (← Simp.mkDefaultMethods).toMethodsRef (← Simp.mkContext) (← ST.mkRef {})


open Lean Meta Elab  Tactic Conv Qq in
@[tactic liftLhsStx]
unsafe def liftLhsTactic : Tactic
| `(tactic| lift_lhs $lift:term $atoms:term) => do
  let atoms ← elabTerm atoms none
  let lift ← elabTerm lift none
  let lhs ← getLhs
  -- logInfo s!"lhs: {lhs.dbgToString}\n\n"
  let e ← mkAppM ``LiftExpr #[lift, atoms, lhs]
  let (xs,_,_) ← forallMetaTelescope (← inferType e)
  let e := e.beta xs

  let .some goal ← SciLean.Tactic.DataSynth.isDataSynthGoal? e | throwError "invalid goal"
  let .some r ← (SciLean.Tactic.DataSynth.dataSynth goal).runInMetaM
    | throwError m!"failed to lift expression {lhs}"

  let result := r.xs[0]!
  checkNoFVars result (fun xs => m!"error: resulting expression contains fvars {xs}")

  try
    let expr ← evalExpr (_root_.Expr Rat) q(_root_.Expr Rat) result

    -- now we have `expr : RingExpr` and we can do what ever we want with it
    logInfo s!"{expr.toString}"
  catch _ =>
    throwError m!"invalid expression {result}"


  pure ()
| _ =>
  throwUnsupportedSyntax




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


open Lean Meta Elab  Tactic Conv Qq in
@[tactic liftRhsStx]
unsafe def liftRhsTactic : Tactic
| `(tactic| lift_rhs $lift:term $atoms:term) => do
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
  logInfo cmd
  let res? ← idealMemM2' cmd
  if res?.isNone then
    logError s!"Not in ideal"
  else
    let arr := res?.get!
    logInfo s!"{arr}"


    let idealGenerators : Array (Expr ℚ) := ideal.generators.toArray
    let mappedRes : Array (Expr ℚ × String) := arr.map (fun (_, (coeff, idx)) =>
      let exp := idealGenerators.get! idx
      (exp, coeff)
    )
    logInfo s!"{mappedRes}"--".map (fun (a,b) => s!"{a.toString}*{b}") |>.toList.toString}"

    let mappedRes'_opt : Array (Expr ℚ × Option (Expr ℚ)) := mappedRes.map (fun (a,b) =>
      let parsed := parsePolynomial b |>.toOption
      (a, parsed)
    )

    if not (mappedRes'_opt.all (fun (_, b) => b.isSome)) then
      logError s!"failed to parse polynomial coefficients: {mappedRes'_opt.filter (fun (_, b) => b.isNone)|>.map (fun (a,b) => a.toString)}"

    let mappedRes' : Array (Expr ℚ × Expr ℚ) := mappedRes'_opt.map (fun (a,b) => (a, b.get!))
    logInfo s!"{mappedRes'}"


  pure ()
| _ =>
  throwUnsupportedSyntax








example (x y : Polynomial ℚ) : (Polynomial.C 2)+x^2*y = y := by
  -- ((x0)^2 * x1)
  lift_lhs (Polynomial.C : RingHom ℚ (Polynomial ℚ)) [x,y]
  sorry
-- example (x y : ℚ) : Ideal.span {x} = Ideal.span {y} := by
--   -- ideal(x1)
--   lift_rhs (RingHom.id ℚ) [x,y]


set_option trace.Meta.Tactic.data_synth false

example (x y : ℚ) : x^2*y ∈ Ideal.span {x,y}  := by
  lift_rhs (RingHom.id ℚ) [x,y]
  sorry

-- example (x y : ℚ) : x^2*y+(RingHom.id ℚ 1) ∈ Ideal.span {x,y}  := by
--   lift_rhs (RingHom.id ℚ) [x,y]


example (x y : ℚ) : x^2*y ∈ Ideal.span {x}  := by
  -- lift_rhs (RingHom.id ℚ) [x,y]
  refine Ideal.mem_span_singleton'.mpr ?_
  use x*y
  ring



example (x y : ℚ) : x^2*y ∈ Ideal.span {x, y}  := by
  -- lift_rhs (RingHom.id ℚ) [x,y]
  refine Ideal.mem_span_pair.mpr ?_
  use x*y; use 0
  ring
