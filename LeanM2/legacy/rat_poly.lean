import SciLean
import LeanM2.Basic

-- our DSL for objects in the M2Ring. Here these are constructed (optionally)
-- w.r.t a base M2Ring R. In practice, R = ℚ and this represents polynomials over ℚ
inductive Expr (R : Type) [Ring R] [ToM2Ring R]
  | lift (r : R)
  | add (x y : Expr R)
  | mul (x y : Expr R)
  | pow (x : Expr R) (n : ℕ)
  | atom (i : ℕ)

-- note that Expr ⊆ Polynomial R (in the general case, Expr R corresponds to a ring in
-- and of itself (called S). But in practice might just be an embedding into S. f is what
-- defines our lift and must be homomorphic R → S.
def Expr.toRing {R S: Type} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (e : Expr R)  : S :=
  match e with
  | .lift r => f r
  | .add x y => x.toRing f atoms + y.toRing f atoms
  | .mul x y => x.toRing f atoms * y.toRing f atoms
  | .pow x n => (x.toRing f atoms)^n
  | .atom i => atoms.getD i 0


-- now want to construct a structure representing pairs of (f,atoms, x, e) such that x and e are
-- in correspondence via the relation between S and Expr R. In other words,
-- this is the hard direction: some x: S can be represented as an Expr R, but some can't.
-- our job here is to synthesize those which can.
@[data_synth out e]
structure LiftExpr {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) (e : Expr R) : Prop where
  to_ring : e.toRing f atoms = x

-- section LiftExprDefs
variable {R} [Ring R] [ToM2Ring R] {S} [Ring S] [ToM2Ring S] (atoms : List S) (f : RingHom R S)
--basic theorems for the synthesization of e : Expr R.
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


--Atoms are more tricky. Namely, they are implemented as just a natural number in Expr R,
-- but they are coerced from S by checking against the indices of the atoms : List S.
-- That means there are many values of x : S that may or may not correspond to an atom in Expr R.
-- So, to check if some x:S is actually an atom, we need to check if there exists some n:ℕ
-- such that atoms[n] = x. If so, we can construct the corresponding Expr R as .atom n.
@[data_synth out n]
structure IsAtomExpr {S} [Ring S] [ToM2Ring S] (atoms : List S) (x : S) (n : ℕ) : Prop where
  hn : n < atoms.length
  is_atom : atoms[n] = x

-- as we attempt to synthesize n from the metavars, we need to inductively construct
-- all the possible (atoms: List S, x : S) such that there does exist the n:ℕ that makes everything work.
@[data_synth]
theorem isAtom_zero {S} [Ring S] [ToM2Ring S] (atoms : List S) (x : S) : IsAtomExpr (x :: atoms) x 0 := by
  constructor <;> simp

@[data_synth]
theorem isAtom_succ {S} [Ring S] [ToM2Ring S] (a : S) (atoms : List S) (x : S) (n : ℕ) (hx : IsAtomExpr atoms x n) :
    IsAtomExpr (a :: atoms) x (n+1) := by
  constructor <;> simp[hx.1,hx.2]

--now using this IsAtomExpr, we can certify that x:S is actually an atom when attempting
-- to synthesize in this case.
open Classical in
@[data_synth]
theorem lift_atom (x : S) {n} (hx : IsAtomExpr atoms x n) :
    LiftExpr f atoms x (.atom n) where
  to_ring := by simp_all[Expr.toRing,hx.1,hx.2]



-- basic
def Expr.toString {R} [Ring R] [ToM2Ring R] [ToString R] (e : Expr R) : String :=
  match e with
  | .lift r => s!"{r}"
  | .pow x n => s!"({x.toString}^{n})"
  | .add x y => s!"({x.toString} + {y.toString})"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .atom i => s!"x{i}"


-- now using this, can define functions that use the data_synth tactic to construct what is needed
-- for the coercion (and fail in times when x:S isn't liftable to Expr R)
def toExpr {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  Expr R := ex

def exprToString {R S} [Ring R] [ToString R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
  String := ex.toString


-- end LiftExprDefs



-- now, for ideals in an M2Ring, we represent them as a list of generators (which are Expr R).
structure IdExpr (R : Type) [Ring R] [ToM2Ring R] where
  generators : List (Expr R)


--same easy direction as before
def IdExpr.toIdeal {R S: Type} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] [DecidableEq S] (f : RingHom R S) (atoms : List S) (I : IdExpr R)  : Ideal S :=
  Ideal.span ((I.generators.map (fun e => e.toRing f atoms)).toFinset.toSet)

--similar coercion Ideal -> List[Expr R] now
@[data_synth out eI]
structure LiftIdExpr {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] [DecidableEq S] (f : RingHom R S) (atoms : List S) (I : Ideal S) (eI : IdExpr R) : Prop where
  to_ideal : eI.toIdeal f atoms = I

-- section LiftIdExprDefs
variable [DecidableEq S]-- (atoms : List S) (f : RingHom R S)



--now, we again note that like the atoms case, for a given ideal I, we only want to be able
-- to synthesize it into an M2Ideal if there exists some generators : List S such that
-- I = Ideal.span generators.toFinset.
@[data_synth out generators]
structure IsIdExpr (I : Ideal S) (generators : List (Expr R)) : Prop where
  eq : I = Ideal.span (generators.map (fun g => g.toRing f atoms)).toFinset


@[data_synth]
theorem isId_nil : IsIdExpr atoms f (Ideal.span {}) [] := by
  constructor
  congr
  simp


noncomputable def Finset.toList' (G : Finset S) : List {x // x ∈ G} := G.attach.toList

@[data_synth]
theorem isId_fin (G : Finset S) {ge : G → Expr R}
  {hG : ∀ g : G, LiftExpr f atoms (g) (ge g)}
  : IsIdExpr atoms f (Ideal.span G) (G.toList'.map ge) := by
  constructor
  congr
  simp
  ext a
  constructor
  . intro ha
    simp
    use a
    use ha
    constructor
    . simp[Finset.toList']
    . specialize hG ⟨a,ha⟩
      have h := hG.to_ring
      simp[h]
  . intro ha
    rcases ha with ⟨a',ha',hList',htoRing⟩
    specialize hG ⟨a',ha'⟩
    simp[htoRing] at hG
    have h:= hG.to_ring
    have duh : a = a' := by
      rw [← h,← htoRing]
    simp[duh,ha']



def atoms' :List ℚ := []
def f' := RingHom.id ℚ

-- IsIdExpr atoms' f' (Ideal.span ∅) [] : Prop
#check (IsIdExpr atoms' f' (Ideal.span {}) _) rewrite_by data_synth

set_option trace.Meta.Tactic.data_synth true
-- `data_synth` failed
/-
[Meta.Tactic.data_synth] [❌] [?m.64014], IsIdExpr atoms' f' (Ideal.span {1}) ?m.64014 ▼
  [] keys: IsIdExpr (Rat, *, *, Rat, *, *, atoms', f', *, Ideal.span (Rat, *, Singleton.singleton (*, Set (Rat), *, 1)), *)
  [] candidates []
-/
#check (IsIdExpr atoms' f' (Ideal.span {(1:ℚ)}) _) rewrite_by data_synth


-- end LiftIdExprDefs





noncomputable def x : Polynomial ℚ := Polynomial.X
noncomputable def lift' : RingHom ℚ (Polynomial ℚ) := Polynomial.C

#check (LiftExpr lift [x] ((lift 1)+x) _) rewrite_by data_synth






def polyString (p : Polynomial ℚ) {ep : Expr ℚ} (hp : LiftExpr lift' [x] p ep := by data_synth) :
  String := ep.toString



#eval polyString (x^2 + x + lift' 1)



-- structure IdExpr (R : Type) [Ring R] [ToM2Ring R] where
--   generators : Finset (Expr R)


-- --todo make R a subring (check if Polynomial R is a superring of R, if so ok. else add a argument for a lifting function from R->S)
-- def IdExpr.toIdeal {R S: Type} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] [DecidableEq S] (f : RingHom R S) (atoms : List S) (I : IdExpr R)  : Ideal S :=
--   Ideal.span ((I.generators.toList.map (fun e => e.toRing f atoms)).toFinset.toSet)

-- @[data_synth out eI]
-- structure LiftIdExpr {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] [DecidableEq S] (f : RingHom R S) (atoms : List S) (I : Ideal S) (eI : IdExpr R) : Prop where
--   to_ideal : eI.toIdeal f atoms = I

-- section LiftIdExprDefs
-- variable [Ring R] [ToM2Ring R] {S} [Ring S] [ToM2Ring S] [DecidableEq S] (atoms : List S) (f : RingHom R S)

-- @[data_synth]
-- theorem lift (I : Ideal S) {G : Finset S} {h: I = Ideal.span (G)} {ge : G → _} (hg : ∀ g : G, LiftExpr f atoms g (ge g))  :
--   LiftIdExpr f atoms (I) (⟨G.map (fun g => ge g) |>.toFinset⟩) where
--   to_ideal := by
--     simp_all[IdExpr.toIdeal,Expr.toRing,h,hg]
--     have duh : ∀ g ∈ G, ge.toRing f atoms = g := by sorry
--     congr
--     ext g
--     simp
--     constructor
--     . intro hgI
--       rcases hgI with ⟨_, hg⟩
--       sorry
--     . intro hg
--       constructor
--       . sorry
--       . exact (duh g hg).symm

-- def IdExpr.toString {R} [Ring R] [ToString R] [ToM2Ring R] (I : IdExpr R) : String :=
--   s!"ideal({", ".intercalate (I.generators.map (fun e => Expr.toString e))})"


-- -- def Expr.toString {R} [Ring R] [ToM2Ring R] [ToString R] (e : Expr R) : String :=
-- --   match e with
-- --   | .lift r => s!"{r}"
-- --   | .pow x n => s!"({x.toString}^{n})"
-- --   | .add x y => s!"({x.toString} + {y.toString})"
-- --   | .mul x y => s!"({x.toString} * {y.toString})"
-- --   | .atom i => s!"x{i}"

-- -- def toExpr {R S} [Ring R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
-- --   Expr R := ex

-- -- def exprToString {R S} [Ring R] [ToString R] [ToM2Ring R] [Ring S] [ToM2Ring S] (f : RingHom R S) (atoms : List S) (x : S) {ex} (hx : LiftExpr f atoms x ex := by data_synth) :
-- --   String := ex.toString






-- end LiftIdExprDefs





-- noncomputable def x : Polynomial ℚ := Polynomial.X
-- noncomputable def lift' : RingHom ℚ (Polynomial ℚ) := Polynomial.C

-- #check (LiftExpr lift [x] ((lift 1)+x) _) rewrite_by data_synth






-- def polyString (p : Polynomial ℚ) {ep : Expr ℚ} (hp : LiftExpr lift' [x] p ep := by data_synth) :
--   String := ep.toString



-- #eval polyString (x^2 + x + lift' 1)

-- class M2Poly (p: Polynomial ℚ)  where
--   liftable : ∃ ep, (LiftExpr lift [x] p (ep : Expr ℚ))








-- def polyExpr (p : Polynomial ℚ) [M2Poly p] : Expr ℚ :=
--   let l : ∃ ep, LiftExpr lift [x] p ep := M2Poly.liftable
--   --i think we need a metaprogram to get the ep from the liftable
--   -- if a metavariable is still unresolved, we can return none?

--   .lift 0









noncomputable def p : Polynomial ℚ := Polynomial.X
noncomputable def I : Ideal (Polynomial ℚ) := Ideal.span {Polynomial.X}






syntax (name:=liftLhsStx) "lift_lhs" term : tactic

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
| `(tactic| lift_lhs $atoms:term) => do
  let atoms ← elabTerm atoms none
  let lhs ← getLhs

  let e ← mkAppM ``LiftExpr #[q(lift), atoms, lhs]
  let (xs,_,_) ← forallMetaTelescope (← inferType e)
  let e := e.beta xs

  let .some goal ← SciLean.Tactic.DataSynth.isDataSynthGoal? e | throwError "invalid goal"
  let .some r ← (SciLean.Tactic.DataSynth.dataSynth goal).runInMetaM
    | throwError m!"failed to lift expression {lhs}"

  let result := r.xs[0]!
  checkNoFVars result (fun xs => m!"error: resulting expression contains fvars {xs}")

  try
    let expr ← evalExpr (_root_.Expr ℚ) q(_root_.Expr ℚ) result

    -- now we have `expr : RingExpr` and we can do what ever we want with it
    logInfo s!"{expr.toString}"


  catch _ =>
    throwError m!"invalid expression {result}"


  pure ()
| _ =>
  throwUnsupportedSyntax


open Lean Meta Elab Tactic Conv in
example (x : Polynomial ℚ := Polynomial.X) : x+(lift (1)) ∈ I := by

  -- let a := lhs%


  lift_lhs [x]
