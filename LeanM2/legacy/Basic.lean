import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
-- import LeanM2.test

-- todo make the M2Ideal and Elem dependent on ring
mutual
  inductive M2Ring
  | ZZ : M2Ring
  | QQ : M2Ring
  | RR : M2Ring
  | CC : M2Ring
  | Zmod (p : Nat) : M2Ring
  | GF (p : Nat) (n: Nat) : M2Ring
  | Poly (base : M2Ring) (vars : List M2Elem) : M2Ring
  | Quotient (parent : M2Ring) (ideal : M2Ideal) : M2Ring

  structure M2Ideal where
    (ring : M2Ring)
    (generators : List M2Elem)

  structure M2Elem where
    (ring : M2Ring)

end


open M2Ring M2Elem M2Ideal String

def M2Elem.toString (e : M2Elem) : String := "temp"

def M2Ideal.toString (I : M2Ideal) : String :=
  "ideal(" ++ (String.intercalate ", " (I.generators.map M2Elem.toString)) ++ ")"

def String.toM2Elem (s : String) (R : M2Ring): M2Elem := ⟨R⟩



def M2Ring.toString : M2Ring → String
| ZZ                => "ZZ"
| QQ                => "QQ"
| RR                => "RR"
| CC                => "CC"
| (Zmod p)        => s!"ZZ/{p}"
| (GF p n)          => s!"GF({p},{n})"
| (Poly base vars) =>
    let baseStr := base.toString
    let varsStr := "[" ++ String.intercalate ", " (vars.map M2Elem.toString) ++ "]"
    baseStr ++ varsStr
| (M2Ring.Quotient parent ideal) =>
    let parentStr := parent.toString
    parentStr ++ "/" ++ (ideal.toString)



def testIdealMembership (R : M2Ring) (I : M2Ideal) (elem : M2Elem): IO String := do
  let RStr := R.toString
  let IStr := I.toString
  let elemStr := elem.toString

  let prompt := s!"R={RStr}\nI={IStr}\nG= = groebnerBasis I\nf={elemStr}\nf % G"
  IO.println prompt
  return prompt
  -- IO.FS.withTempFile fun fsHandle fsPath => do

  --   fsHandle.putStr  prompt
  --   fsHandle.flush

  --   let m2 ← try
  --       let output ← IO.Process.output {
  --         cmd := "M2"
  --         args := #["--script", fsPath.toString]
  --       }
  --       pure output.stdout
  --     catch e =>
  --       pure s!"Error executing M2: {e.toString}"

  --   return m2


-- -- /- Example evaluations -/
-- -- #eval m2RingToString QQ                     -- "QQ"
-- -- #eval m2RingToString (Zmod 7)               -- "ZZ/7"
-- -- #eval m2RingToString (GF 7)                 -- "GF(7)"
-- -- #eval m2RingToString (Poly QQ ["x".toM2Elem QQ, "y".toM2Elem QQ])     -- "QQ[x, y]"
-- -- #eval M2Ring.toString (M2Ring.Quotient QQ (⟨QQ,["x".toM2Elem QQ]⟩))
-- -- "QQ[x, y]/ideal(x^2 - y)"



-- Type classes for converting Lean types to M2 representations
class ToM2Ring (R : Type) where
  toM2Ring : M2Ring

class ToM2Elem (α : Type) (R : Type) [ToM2Ring R] where
  toM2Elem : α → M2Elem

class ToM2Ideal (I : Type) (R : Type) [ToM2Ring R] where
  toM2Ideal : I → M2Ideal





namespace ToM2Ring
-- Instances for common Lean types
instance : ToM2Ring Int where
  toM2Ring := M2Ring.ZZ

instance : ToM2Ring Rat where
  toM2Ring := M2Ring.QQ

instance : ToM2Ring Real where
  toM2Ring := M2Ring.RR

instance : ToM2Ring Complex where
  toM2Ring := M2Ring.CC

instance (p : Nat) [Fact (Nat.Prime p)] : ToM2Ring (ZMod p) where
  toM2Ring := M2Ring.Zmod p

instance (p n: Nat) [Fact (Nat.Prime p)] : ToM2Ring (GaloisField p n) where
  toM2Ring := M2Ring.GF p n

instance (R : Type) [Ring R] [ToM2Ring R] : ToM2Ring (Polynomial R) where
  toM2Ring :=
    let baseRing := ToM2Ring.toM2Ring R
    let vars := ["x".toM2Elem baseRing]
    M2Ring.Poly baseRing vars

instance (R : Type) {n:Nat} [CommRing R] [ToM2Ring R] : ToM2Ring (MvPolynomial (Fin n) R) where
  toM2Ring :=
    let baseRing := ToM2Ring.toM2Ring R
    let vars := List.range n |>.map (fun i => s!"x{i}".toM2Elem baseRing)
    M2Ring.Poly baseRing vars


instance (R : Type) {n:Nat} [CommRing R] [ToM2Ring R] : ToM2Ring (MvPolynomial (Fin n) R) where
  toM2Ring :=
    let baseRing := ToM2Ring.toM2Ring R
    let vars := List.range n |>.map (fun i => s!"x{i}".toM2Elem baseRing)
    M2Ring.Poly baseRing vars


#eval ToM2Ring.toM2Ring ℚ

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

#eval ToM2Ring.toM2Ring (ZMod 7)
#eval ToM2Ring.toM2Ring (GaloisField 7 3)
#eval ToM2Ring.toM2Ring (Polynomial ℚ)
#eval ToM2Ring.toM2Ring (MvPolynomial (Fin 2) ℚ)

end ToM2Ring
namespace ToM2Elem







instance (R : Type) [ToM2Ring R] : ToM2Elem R R where
  toM2Elem := fun r => ⟨ToM2Ring.toM2Ring R⟩

end ToM2Elem

-- namespace ToM2Ideal

-- -- something about instancing it for a general ideal with some
-- -- (finite) set of generators (as a Submodule)
-- instance (R : Type) [Ring R] [ToM2Ring R] (I : Ideal R): ToM2Ideal I R where
--   toM2Ideal := fun I => ⟨ToM2Ring.toM2Ring R, I.gens.map (ToM2Elem.toM2Elem R)⟩


-- end ToM2Ideal
