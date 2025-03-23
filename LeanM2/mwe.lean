import SciLean
import LeanM2.toM2
import Mathlib.Tactic.PolyRith
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
  let cmd := s!"R=QQ[x0,x1]\nf={polynomial.toString}\nI={ideal.toString}\nG=groebnerBasis I\nf % G"
  -- logInfo cmd

  logInfo s!"{← idealMemM2' cmd}"


  pure ()
| _ =>
  throwUnsupportedSyntax








example (x y : Polynomial ℚ) : (Polynomial.C 2)+x^2*y = y := by
  -- ((x0)^2 * x1)
  lift_lhs (Polynomial.C : RingHom ℚ (Polynomial ℚ)) [x,y]

example (x y : ℚ) : Ideal.span {x} = Ideal.span {y} := by
  -- ideal(x1)
  lift_rhs (RingHom.id ℚ) [x,y]


set_option trace.Meta.Tactic.data_synth false

example (x y : ℚ) : x^2*y ∈ Ideal.span {x,y}  := by
  lift_rhs (RingHom.id ℚ) [x,y]

example (x y : ℚ) : x^2*y+(RingHom.id ℚ (1:ℚ)) ∈ Ideal.span {x,y}  := by
  lift_rhs (RingHom.id ℚ) [x,y]
