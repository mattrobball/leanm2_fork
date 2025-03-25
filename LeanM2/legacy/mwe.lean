import SciLean
import LeanM2.toM2
import Lean.Data.Json.Basic
import Mathlib.Data.FP.Basic

open Lean


inductive Expr (R : Type) [Ring R]
  | lift (r : R)
  | add (x y : Expr R)
  | mul (x y : Expr R)
  | pow (x : Expr R) (n : ℕ)
  | atom (i : ℕ)

instance [Ring R] : Inhabited (Expr R) where
  default := .lift 0

def Expr.toRing {R S: Type} [Ring R]  [Ring S]  (f : RingHom R S) (atoms : List S) (e : Expr R)  : S :=
  match e with
  | .lift r => f r
  | .add x y => x.toRing f atoms + y.toRing f atoms
  | .mul x y => x.toRing f atoms * y.toRing f atoms
  | .pow x n => (x.toRing f atoms)^n
  | .atom i => atoms.getD i 0

@[data_synth out e]
structure LiftExpr {R S} [Ring R]  [Ring S]  (f : RingHom R S) (atoms : List S) (x : S) (e : Expr R) : Prop where
  to_ring : e.toRing f atoms = x

variable {R} [Ring R] {S} [Ring S] (atoms : List S) (f : RingHom R S)
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

def Expr.toString {R} [Ring R]  [ToString R] (e : Expr R) : String :=
  match e with
  | .lift r => s!"{r}"
  | .pow x n => s!"({x.toString})^{n}"
  | .add x y => s!"({x.toString} + {y.toString})"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .atom i => s!"x{i}"

def toExpr {R S} [Ring R]  [Ring S]  (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  Expr R := ex

def exprToString {R S} [Ring R] [ToString R]  [Ring S]  (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  String := ex.toString


def toRatParts (f : Float) : Option (Int × Int) :=
  if f.isFinite then
    let (f', exp) := f.frExp
    let x := (2^53:Nat).toFloat * f'
    let v := if x < 0 then
      (-(-x).floor.toUInt64.toNat : Int)
    else
      (x.floor.toUInt64.toNat : Int)
    some (v, exp - 53)
  else none

def toRat (f : Float) : Option Rat :=
  if let some (v, exp) := toRatParts f then
    if exp ≥ 0 then
      some (v * ((2^exp.toNat:Nat) : Rat))
    else
      some ((v : Rat) / ((2^(-exp).toNat : Nat):Rat))
  else none




def String.toRat?' (s:String) : Option ℚ :=
  let json? : Option Json := (Json.parse s).toOption
  let num? := match json? with
  | some json => json.getNum? |>.toOption
  | none => none

  let flt? := match num? with
  | some num => some num.toFloat
  | none => none

  let fpflt? := match flt? with
  | some flt => if flt.isFinite then toRat flt else none
  | none => none

  fpflt?



def String.toRat? (s:String) : Option ℚ :=
  if let some i := String.toInt? s then
    some i
  else if s.contains '/' then
    let parts := s.splitOn "/"
    if parts.length == 2 then
        match (String.toInt? parts[0]!, String.toInt? parts[1]!) with
        | (some n, some d) => if d ≠ 0 then some ((n:ℚ)/(d:ℚ)) else none
        | _ => none
    else none
  else if s.contains '.' then
    let parts := s.splitOn "."
    if parts.length == 2 then
      match (String.toInt? parts[0]!, String.toInt? parts[1]!) with
      | (some n, some d) =>
        let d' : ℕ := d.natAbs
        let decimalDigits := (Nat.digits 10 d').length
        let denominator : Int := 10^decimalDigits
        some ((n:ℚ) + (d:ℚ) / denominator)
      | _ => none
    else none
  else
    String.toRat?' s


partial def String.toQExpr (s:String) : Option (Expr ℚ) :=
  let s := s.trim
  let s := if s.startsWith "(" && s.endsWith ")" then s.drop 1 |>.dropRight 1 else s

  if s.contains '^' then
    let parts := s.splitOn "^"
    if parts.length >= 2 then
      let base := "^".intercalate (List.range (parts.length) |>.filterMap (fun i=> if i==parts.length-1 then none else parts[i]!))
      match (String.toQExpr base, String.toNat? parts[parts.length-1]!) with
      | (some base, some exp) => some <| .pow base exp
      | _ => none
    else
      none
  else if s.contains '*' then
    let parts := s.splitOn "*"
    if parts.length >= 2 then
      match (String.toQExpr parts[0]!, String.toQExpr <| "*".intercalate
        (List.range (parts.length) |>.filterMap (fun i=> if i==0 then none else parts[i]!)))
          with
      | (some l, some r) => some <| .mul l r
      | _ => none
    else
      none
  else if s.contains '+' then
    let parts := s.splitOn "+"
    if parts.length >= 2 then
      let rhs := "+".intercalate
        (List.range (parts.length) |>.filterMap (fun i=> if i==0 then none else some parts[i]!))
      match (String.toQExpr parts[0]!, String.toQExpr rhs)
          with
      | (some l, some r) => some <| .add l r
      | _ => none
    else
      none
  else if s.startsWith "x" then (
    let n := s.drop 1 |>.toNat?
    match n with
    | some n => some <| .atom n
    | none => none)
  else if let some q := s.toRat? then
    some <| .lift q

  else
    none



partial def String.toQExpr' (s:String) : IO Unit := do
  IO.println s
  let s := s.trim
  let s := if s.startsWith "(" && s.endsWith ")" then s.drop 1 |>.dropRight 1 else s

  if s.contains '^' then
    let parts := s.splitOn "^"
    IO.println parts
    if parts.length >= 2 then
      let base := "^".intercalate (List.range (parts.length) |>.filterMap (fun i=> if i==parts.length-1 then none else parts[i]!))
      String.toQExpr' base
      -- let _:=String.toNat? parts[1]!
      pure ()
    else
      pure ()
  else if s.contains '*' then
    let parts := s.splitOn "*"
    if parts.length >= 2 then
      String.toQExpr' parts[0]!
      String.toQExpr' <| "*".intercalate
        (List.range (parts.length) |>.filterMap (fun i=> if i==0 then none else parts[i]!))

      pure ()
    else
      pure ()
  else if s.contains '+' then
    let parts := s.splitOn "+"
    if parts.length >= 2 then
      let rhs := "+".intercalate
        (List.range (parts.length) |>.filterMap (fun i=> if i==0 then none else some parts[i]!))
      String.toQExpr' parts[0]!
      String.toQExpr' rhs
      pure ()
    else
      pure ()
  else if s.startsWith "x" then (
    let n := s.drop 1 |>.toNat?
    pure ())
  else if let some q := s.toRat? then
    pure ()





  else
    pure ()




#eval String.toQExpr' "(x0^2+1)^3"

#eval String.toQExpr "(x0^2+1)^3" |>.get!



structure IdExpr (R : Type) [Ring R]  where
  generators : List (Expr R)

instance : Inhabited (IdExpr R) where
  default := ⟨[]⟩

def IdExpr.toIdeal {R S: Type} [Ring R]  [Ring S]  [DecidableEq S] (f : RingHom R S) (atoms : List S) (I : IdExpr R)  : Ideal S :=
  Ideal.span ((I.generators.map (fun e => e.toRing f atoms)).toFinset.toSet)

@[data_synth out eI]
structure LiftIdExpr {R S} [Ring R]  [Ring S]  [DecidableEq S] (f : RingHom R S) (atoms : List S) (I : Ideal S) (eI : IdExpr R) : Prop where
  to_ideal : eI.toIdeal f atoms = I

variable [DecidableEq S]





@[data_synth out generators]
structure IsIdExpr (I : Ideal S) (generators : List (Expr R)) : Prop where
  eq : I = Ideal.span (generators.map (fun g => g.toRing f atoms)).toFinset


@[data_synth]
theorem isId_nil : IsIdExpr atoms f (Ideal.span {}) [] := by
  constructor
  congr
  simp


-- noncomputable def Finset.toList' (G : Finset S) : List {x // x ∈ G} := G.attach.toList


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




def IdExpr.toString [ToString R] (I : IdExpr R) : String :=
  s!"ideal({",".intercalate (I.generators.map (fun e => e.toString))})"

def toIdExpr (I : Ideal S) {eI} (hx : LiftIdExpr f atoms I eI := by data_synth) :
  IdExpr R := eI

def IdExprToString [ToString R] (I : Ideal S) {eI} (hx : LiftIdExpr f atoms I eI := by data_synth) :
  String := eI.toString






def atoms' :List ℚ := []
def f' := RingHom.id ℚ

-- IsIdExpr atoms' f' (Ideal.span ∅) [] : Prop
#check (IsIdExpr atoms' f' (Ideal.span {}) _) rewrite_by data_synth

set_option trace.Meta.Tactic.data_synth true


-- IsIdExpr atoms' f' (Ideal.span {f' 1}) [Expr.lift 1] : Prop
#check (IsIdExpr atoms' f' (Ideal.span {f' (1:ℚ)}) _) rewrite_by data_synth
--IsIdExpr atoms' f' (Ideal.span {f' 1, f' 2}) [Expr.lift 1, Expr.lift 2] : Prop
#check (IsIdExpr atoms' f' (Ideal.span {f' (1:ℚ), f' (2:ℚ)}) _) rewrite_by data_synth

#check LiftIdExpr f' atoms' (Ideal.span {f' (1:ℚ), f' (2:ℚ)}) _ rewrite_by data_synth



noncomputable def X : Polynomial ℚ:= Polynomial.X
noncomputable def vars :List (Polynomial ℚ) := [X]
noncomputable def lift : RingHom ℚ (Polynomial ℚ):= Polynomial.C

#check (IsIdExpr [X] lift (Ideal.span {X^2}) _) rewrite_by data_synth

#check LiftIdExpr lift [X] (Ideal.span {X^2}) _ rewrite_by data_synth


#eval exprToString lift [X] (X^2)
#eval IdExprToString [X] lift (Ideal.span {X^2})





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
    -- logInfo s!"{expr.toString}"
  catch _ =>
    throwError m!"invalid expression {result}"


  -- todo get n from atoms.length

  -- checkNoFVars atoms (fun xs => m!"error: resulting expression contains fvars {xs}")

  -- try
  --   let lst ← evalExpr (List Rat) q(List Rat) atoms
  --   logInfo s!"{lst.toString}"
  -- catch e =>
  --   throwError m!"invalid expression {result}: {← e.toMessageData.toString}"
  let atoms' := parseExprList atoms
  let cmd := s!"R=QQ{if atoms'.length == 0 then "" else s!"{List.range atoms'.length |>.map (fun i => s!"x{i}")}"}\nf={polynomial.toString}\nI={ideal.toString}\nG=groebnerBasis I\nf % G\nf//G"
  logInfo cmd
  let res? ← idealMemM2' cmd
  if res?.isNone then
    logError s!"Not in ideal"
  else
    let arr := res?.get!
    logInfo s!"{arr}"

    -- let idealGenStrs := ideal.toString.dropPrefix "ideal(".dropSuffix ")"
    --            |>.split fun c => c == ','
    let idealGenerators : Array (Expr ℚ) := ideal.generators.toArray
    let mappedRes : Array (Expr ℚ × String) := arr.map (fun (_, (coeff, idx)) =>
      let exp := idealGenerators.get! idx
      (exp, coeff)
    )
    logInfo s!"{mappedRes.map (fun (a,b) => s!"{a.toString}*{b}") |>.toList.toString}"
    -- )
    --   let idealGenStr := idx.trim
    --   let mut foundIdx := 0
    --   for i in [:idealGenStrs.size] do
    --   if idealGenStrs[i]!.trim == idealGenStr then
    --     foundIdx := i
    --     break
    --   if foundIdx < ideal.generators.length then
    --   return (ideal.generators[foundIdx]!, coeff)
    --   else
    --   throwError s!"Failed to find generator for {idealGenStr}"
    -- logInfo s!"Result: {mappedRes}"

    -- let mapped_fst : Array (Lean.Expr × String) := arr.map (fun item =>
    --   let idx := item.1.replace "x" "" |>.toNat!
    --   let exp := atoms'.get! idx

    --   (exp, item.2)
    -- )



    -- logInfo s!"{atoms'}\n{mapped_fst}"


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
