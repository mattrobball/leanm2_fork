import LeanM2.defs
import LeanM2.parser
import LeanM2.toM2
import LeanM2.M2Type
import Lean.PrettyPrinter.Delaborator.Basic
import Mathlib.Tactic.Use
import Mathlib.Tactic.Polyrith
import LeanM2.Expr2Expr
import LeanM2.coolRings


syntax (name:=leanM2Stx) "lean_m2" term : tactic

#eval M2Repr.repr IntM2.M2Int

open Lean Meta Elab Tactic Conv Qq RatM2 RealM2 in
@[tactic leanM2Stx]
unsafe def leanM2Tactic : Tactic
| `(tactic| lean_m2 $lift:term $atoms:term) => do
  let atoms ← elabTerm atoms none
  let lift ← elabTerm lift none
  let (ideal, elem) ← getMem
  let (_,_,i'') := ideal
  -- logInfo m!"ideal: {parseExprIdealSpan i''}"

  let inputM2Type : Lean.Expr× String ← match lift with
    | .lam _ type _ _ => do
        let M2T ← mkFreshExprMVar q(Type)
        let instType ← mkAppM ``M2Type #[type, M2T]
        -- logInfo m!"inputM2Type: {instType}"
        let _ ← synthInstance instType
        -- logInfo M2T
        let reprExpr ← mkAppOptM ``M2Repr.repr #[M2T,none]
        let repr ← evalExpr (String) q(String) reprExpr


        pure (M2T,repr)
    | e =>
      logError s!"failed to infer the input ring from the provided lift expression\n{e.dbgToString}"
      default

  let (M2R,repr) := inputM2Type
  -- logInfo m!"inputM2Type: {inputM2Type}"


  let outputRing ← match getOutputRing i'' with
    | none => do
      logError "failed to find output ring from ideal expression"
      default
    | some or =>
      pure or

  let mut polynomial : String := default
  let mut ideal : String := default

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
    let strExpr ← mkAppM ``toString #[result]
    let expr ← evalExpr (String) q(String) strExpr
    polynomial := expr
    -- logInfo s!"{expr}"
  catch msg =>
    logInfo m!"invalid expression {result}"
    logError msg.toMessageData


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
    let strExpr ← mkAppM ``toString #[result]
    let expr ← evalExpr (String) q(String) strExpr
    ideal := expr
  catch msg =>
    logInfo m!"invalid expression {result}"
    logError msg.toMessageData

  let atoms' := parseExprList atoms
  let cmd := s!"R={repr}{if atoms'.length == 0 then "" else s!"{List.range atoms'.length |>.map (fun i => s!"x{i}")}"}\nf={polynomial}\nI={ideal}\nG=gb(I,ChangeMatrix=>true)\nf % G\n(getChangeMatrix G)*(f// groebnerBasis I)"
  -- logInfo s!"{cmd}"
  let res? ← idealMemM2' cmd
  if res?.isNone then
    logError s!"Not in ideal"
  else
    let arr := res?.get!
    -- logInfo s!"{arr}"


    let idealGenerators : Array (Lean.Expr) := parseExprIdealSpan i'' |>.toArray

    let mut mappedRes : Array (Lean.Expr × String) := arr.mapIdx (fun idx coeff => (idealGenerators.get! idx, coeff))

    logInfo m!"{mappedRes}"

    let mappedRes'_opt : Array (Lean.Expr × Option (Lean.Expr)) ← mappedRes.mapM (fun (a,b) => do
      -- let parsed := parsePolynomial' M2Rat b
      -- logInfo m!"parsing polynomial: {b} in {M2R}"
      let parsedExpr ← mkAppOptM ``parsePolynomial' #[M2R,none,none, q($b)]
      let parsed ← evalExpr (Option (Lean.Expr → Lean.Expr → List Lean.Expr → MetaM Lean.Expr)) q(Option (Lean.Expr → Lean.Expr → List Lean.Expr → MetaM Lean.Expr)) parsedExpr
      let parsed' ← match parsed with
        | some f => do
          let output' ← f outputRing lift atoms'
          pure (some output')
        | none =>
          pure none
      -- logInfo m!"parsed: {parsed'}"
      pure (a, parsed')
    )

    if not (mappedRes'_opt.all (fun (_, b) => b.isSome)) then
      logError m!"failed to parse polynomial coefficients: {mappedRes'_opt.filter (fun (_, b) => b.isNone)|>.map (fun (a,_) => a)}"

    let mappedRes' : Array (Lean.Expr × Lean.Expr) := mappedRes'_opt.map (fun (a,b) => (a, b.get!))
    -- logInfo m!"mappedRes': {mappedRes'}"

    -- let mappedRes'' :Array (Lean.Expr × Lean.Expr) ←  mappedRes'.mapM (fun (a,b) => do
    --   let b' ← b.toLeanExpr' outputRing lift atoms'
    --   pure (a, b')
    -- )

    -- logInfo m!"mappedRes'': {mappedRes''}"

    let mappedRes'' : Array Term ←  mappedRes'.mapIdxM (fun i (_, coeff) => do
      let neg ← if i < mappedRes'.size - 1 then
        mkAppM ``Neg.neg #[coeff]
      else
        pure coeff

      let negTerm ← Lean.PrettyPrinter.delab neg
      return negTerm
    )
    -- logInfo m!"mappedRes'': {mappedRes''}"



    -- Run the simp tactic with the specified lemmas
    evalTactic (← `(tactic| simp [Ideal.mem_span_insert', Ideal.mem_span_singleton']))

    Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) (mappedRes''.toList)

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




-- set_option trace.Meta.Tactic.data_synth false

-- example (x y : ZMod 11) : x^2 + y^2 ∈ Ideal.span {x, y} := by
--   lean_m2 (fun (t : ZMod 11) => t) [x, y]

-- -- def lift : ℚ→ℚ := fun x => x

-- def getM2Type (T : Type*) {M2T} [M2Type T M2T] : Type* :=
--   M2T

-- #reduce (types := true) getM2Type (ZMod 11)


-- -- example (x: ℚ) : ((fun (t:ℚ) => t) 2) + x ∈ Ideal.span {x}  := by
-- --   -- let f := fun (t:ℚ) => t
-- --   lean_m2 (fun (t:ℚ) => t) [x]

-- example (x: ℝ) : ((fun (t:ℝ) => t) (Real.sqrt ((2:ℚ):ℝ))) + x ∈ Ideal.span {((fun (t:ℝ) => t) (Real.sqrt ((2:ℚ):ℝ))) + x}  := by
--   lean_m2 (fun (t:ℝ) => t) [x]

-- example (x y z: ℚ) : x^2+y^2 ∈ Ideal.span {x,y,z}  := by
--   lean_m2 (fun (t:ℚ) => t) [x,y,z]

-- example (x y z: ℂ) : x^2+y^2 ∈ Ideal.span {x,y,z}  := by
--   lean_m2 (fun (t:ℂ) => t) [x,y,z]


-- example (x y : ℚ) : x^2+y^2 ∈ Ideal.span {x,y}  := by
--   lean_m2 (fun (x:ℚ) => x) [x,y]

-- example (x y : ℚ) : x^2+x*y^2 ∈ Ideal.span {x}  := by
--   lean_m2 (fun (x:ℚ) => x) [x,y]

-- -- example (x y : ℚ) : x^2+y^2 ∈ Ideal.span {}  := by
-- --   lean_m2 (fun (x:ℚ) => x) [x,y]



-- example (x y : ℚ) : x^3+y^3 ∈ Ideal.span {x+y}  := by
--   lean_m2 (fun (x:ℚ) => x) [x,y]

-- example (x y : Polynomial ℚ) : x^3+y^3 ∈ Ideal.span {x+y}  := by
--   lean_m2 (fun (t:ℚ) => Polynomial.C t) [x,y]




-- example (x y z: ℚ) : x^2+y ∈ Ideal.span {x^2,y}  := by
--   lean_m2 (fun (x:ℚ) => x) [x,y,z]


-- example (x y z : ℚ) : x^2*y+y*x ∈ Ideal.span {x, y, z}  := by
--   lean_m2 (fun (x:ℚ) => x) [x,y,z]




-- -- example (a b c d e f : ℚ) : a^3*c+a^2*b*d-a^2*e*f+a*d*e^2-a*c*d*f
-- --   ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
-- --   lean_m2 (fun (x:ℚ) => x) [a,b,c,d,e,f]


-- example (a b c d e f : ℚ) : a^4+a^2*b*c-a^2*d*e+a*b^3+b^2*c*d-b^2*e*f+a*c^3+b*c^2*d-c^2*f^2
--   ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
--   lean_m2 (fun (x:ℚ) => x) [a,b,c,d,e,f]


-- example (x y : ℚ) (h : x+y = 0) : x^3 + y^3 = 0 := by
--   have sufficient : x^3+y^3 ∈ Ideal.span {x+y} := by
--     lean_m2 (fun (x:ℚ) => x) [x,y]
--   apply Ideal.mem_span_singleton'.1 at sufficient
--   simp [mul_zero,h] at sufficient
--   linarith


-- example (a b c d e f : ℚ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
--   polyrith



-- example (a b c d e f : ℚ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
--   have sufficient : a*b*c*d - a*e*f*d ∈ Ideal.span {b*c-e*f} := by
--     lean_m2 (fun (x:ℚ) => x) [a,b,c,d,e,f]
--   apply Ideal.mem_span_singleton'.1 at sufficient
--   simp [mul_zero,h] at sufficient
--   linarith


-- -- example (x : ℝ) : Ideal.span {((2:ℚ):ℝ) * x} = Ideal.span {x}  := by
-- --   have a : ((2:ℚ):ℝ) * x ∈ Ideal.span {x} := by sorry
-- --   have b : x ∈ (Ideal.span {((2:ℚ):ℝ) * x}) := by sorry
-- --   apply Ideal.mem_span_singleton'.1 at
-- --   sorry
