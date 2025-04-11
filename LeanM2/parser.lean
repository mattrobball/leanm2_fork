
-- import SciLean
-- import LeanM2.toM2
import Lean.Data.Json.Basic
import Mathlib.Data.FP.Basic
import Std.Internal.Parsec.String
import Mathlib.Data.Nat.Digits
-- import SciLean
-- import LeanM2.toM2
import LeanM2.Expr2Expr
import LeanM2.M2Type
import LeanM2.defs
import Std.Internal.Parsec.String
import Mathlib.Data.Nat.Digits



open Std.Internal.Parsec Std.Internal.Parsec.String
open Lean

class parseableRepr (repr : String) where
  R : Type
  M2R : outParam Type
  inst_M2Type : M2Type R M2R
  parse : Parser M2R


class Unrepr (α : Type) where
  parse : Parser α
export Unrepr (parse)

instance : Unrepr Nat where
  parse := digits


def parseString (p : Parser α) (s : String) : Except String α :=
  match (p <* eof) s.mkIterator with
  | .success _ res => .ok res
  | .error _ msg => .error msg


def nextCharSatisfies (p : Char → Bool) : Parser Bool := do
  match ← peek? with
  | some c => pure (p c)
  | none => pure false


namespace RatM2


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

open RatM2 in
def M2Rat.parse : Parser M2Rat := do
  let s ← manyChars (satisfy fun c => c.isDigit || c == '/' || c == '.' || c == '-')
  match s.toRat? with
  | some q => pure ⟨q⟩
  | none => fail s!"Could not parse '{s}' as a rational number"

open RatM2 in
instance : Unrepr M2Rat where
  parse := M2Rat.parse

open RatM2 in
def Rat.parse : Parser ℚ := do
  let s ← manyChars (satisfy fun c => c.isDigit || c == '/' || c == '.' || c == '-')
  match s.toRat? with
  | some q => pure q
  | none => fail s!"Could not parse '{s}' as a rational number"


instance : Unrepr ℚ where
  parse := Rat.parse

instance : parseableRepr "QQ" where
  R := ℚ
  M2R := M2Rat
  inst_M2Type := inferInstance
  parse := M2Rat.parse

end RatM2

namespace IntM2

def M2Int.parse : (Parser ℤ) := do
    let s ← manyChars (satisfy fun c => c.isDigit || c == '-')
    match s.toInt? with
    | some i => pure i
    | none => fail s!"Could not parse '{s}' as an integer"


instance : Unrepr M2Int where
  parse := M2Int.parse

instance : parseableRepr "ZZ" where
  R := ℤ
  M2R := M2Int
  inst_M2Type := inferInstance
  parse := M2Int.parse

end IntM2

open IntM2 in
#eval parseString M2Int.parse "123"

namespace RealM2
open RatM2

mutual
  partial def M2Real.parse : Parser M2Real := do
    parseM2RealExpr

  partial def parseM2RealExpr : Parser M2Real := do
    let res ← parseM2RealTerm
    parseM2RealAddSubRest res

  partial def parseM2RealAddSubRest (lhs : M2Real) : Parser M2Real := do
    (do
      skipChar '+'
      ws
      let rhs ← parseM2RealTerm
      parseM2RealAddSubRest (M2Real.add lhs rhs))
    <|>
    (do
      skipChar '-'
      ws
      let rhs ← parseM2RealTerm
      parseM2RealAddSubRest (M2Real.sub lhs rhs))
    <|>
    pure lhs

  partial def parseM2RealTerm : Parser M2Real := do
    let res ← parseM2RealFactor
    parseM2RealMulDivRest res

  partial def parseM2RealMulDivRest (lhs : M2Real) : Parser M2Real := do
    (do
      skipChar '*'
      ws
      let rhs ← parseM2RealFactor
      parseM2RealMulDivRest (M2Real.mul lhs rhs))
    <|>
    (do
      skipChar '/'
      ws
      let rhs ← parseM2RealFactor
      parseM2RealMulDivRest (M2Real.div lhs rhs))
    <|>
    pure lhs

  partial def parseM2RealFactor : Parser M2Real := do
    (do -- Parse pi
      skipString "pi"
      ws
      parseM2RealPowRest M2Real.pi)
    <|>
    (do -- Parse sqrt function
      skipString "sqrt("
      ws
      let x ← parseM2RealExpr
      skipChar ')'
      ws
      parseM2RealPowRest (M2Real.sqrt x))
    <|>
    (do -- Parse log function
      skipString "log("
      ws
      let x ← parseM2RealExpr
      skipChar ')'
      ws
      parseM2RealPowRest (M2Real.log x))
    <|>
    (do -- Parse exp function
      skipString "exp("
      ws
      let x ← parseM2RealExpr
      skipChar ')'
      ws
      parseM2RealPowRest (M2Real.exp x))
    <|>
    (do -- Parse parenthesized expression
      skipChar '('
      ws
      let x ← parseM2RealExpr
      skipChar ')'
      ws
      parseM2RealPowRest x)
    <|>
    (do -- Parse rational number
      let q ← Rat.parse
      parseM2RealPowRest (M2Real.rat q))

  partial def parseM2RealPowRest (base : M2Real) : Parser M2Real := do
    (do
      skipChar '^'
      ws
      let exp ← parseM2RealFactor
      pure (M2Real.pow base exp))
    <|>
    pure base
end


instance : Unrepr M2Real where
  parse := M2Real.parse

noncomputable
instance : parseableRepr "RR" where
  R := ℝ
  M2R := M2Real
  inst_M2Type := inferInstance
  parse := M2Real.parse

end RealM2

open RealM2 in
#eval parseString M2Real.parse "2*(pi^(exp(2)))"


namespace ComplexM2
open RatM2


mutual
  partial def M2Complex.parse : Parser M2Complex := do
    parseM2ComplexExpr

  partial def parseM2ComplexExpr : Parser M2Complex := do
    let res ← parseM2ComplexTerm
    parseM2ComplexAddSubRest res

  partial def parseM2ComplexAddSubRest (lhs : M2Complex) : Parser M2Complex := do
    (do
      skipChar '+'
      ws
      let rhs ← parseM2ComplexTerm
      parseM2ComplexAddSubRest (M2Complex.add lhs rhs))
    <|>
    (do
      skipChar '-'
      ws
      let rhs ← parseM2ComplexTerm
      parseM2ComplexAddSubRest (M2Complex.sub lhs rhs))
    <|>
    pure lhs

  partial def parseM2ComplexTerm : Parser M2Complex := do
    let res ← parseM2ComplexFactor
    parseM2ComplexMulDivRest res

  partial def parseM2ComplexMulDivRest (lhs : M2Complex) : Parser M2Complex := do
    (do
      skipChar '*'
      ws
      let rhs ← parseM2ComplexFactor
      parseM2ComplexMulDivRest (M2Complex.mul lhs rhs))
    <|>
    (do
      skipChar '/'
      ws
      let rhs ← parseM2ComplexFactor
      parseM2ComplexMulDivRest (M2Complex.div lhs rhs))
    <|>
    pure lhs

  partial def parseM2ComplexFactor : Parser M2Complex := do
    (do -- Parse pi
      skipString "pi"
      ws
      parseM2ComplexPowRest M2Complex.pi)
    <|>
    (do -- Parse pi
      skipString "i"
      ws
      parseM2ComplexPowRest M2Complex.i)
    <|>
    (do -- Parse sqrt function
      skipString "sqrt("
      ws
      let x ← parseM2ComplexExpr
      skipChar ')'
      ws
      parseM2ComplexPowRest (M2Complex.sqrt x))
    <|>
    (do -- Parse log function
      skipString "log("
      ws
      let x ← parseM2ComplexExpr
      skipChar ')'
      ws
      parseM2ComplexPowRest (M2Complex.log x))
    <|>
    (do -- Parse exp function
      skipString "exp("
      ws
      let x ← parseM2ComplexExpr
      skipChar ')'
      ws
      parseM2ComplexPowRest (M2Complex.exp x))
    <|>
    (do -- Parse parenthesized expression
      skipChar '('
      ws
      let x ← parseM2ComplexExpr
      skipChar ')'
      ws
      parseM2ComplexPowRest x)
    <|>
    (do -- Parse rational number
      let q ← Rat.parse
      parseM2ComplexPowRest (M2Complex.rat q))

  partial def parseM2ComplexPowRest (base : M2Complex) : Parser M2Complex := do
    (do
      skipChar '^'
      ws
      let exp ← parseM2ComplexFactor
      pure (M2Complex.pow base exp))
    <|>
    pure base
end


instance : Unrepr M2Complex where
  parse := M2Complex.parse


noncomputable
instance : parseableRepr "CC" where
  R := ℂ
  M2R := M2Complex
  inst_M2Type := inferInstance
  parse := M2Complex.parse

end ComplexM2

open ComplexM2 in
#eval parseString M2Complex.parse "exp(pi*i)"




section Parser

variable {R : Type} [Unrepr R]

mutual
  partial def parseExpr : Parser (Expr R) := do
    let res ← parseTerm
    let res ← parseSumRest res
    return res

  partial def parseSumRest (lhs : Expr R) : Parser (Expr R) := do
    (do
      skipChar '+'
      ws
      let rhs ← parseTerm
      parseSumRest (Expr.add lhs rhs))
    <|>
    (do
      skipChar '-'
      ws
      let rhs ← parseTerm
      parseSumRest (Expr.sub lhs rhs))

    <|>
    pure lhs

  partial def parseTerm : Parser (Expr R) := do
    let res ← parseFactor
    let res ← parseProductRest res
    return res

  partial def parseProductRest (lhs : Expr R) : Parser (Expr R) := do
    (do
      skipChar '*'
      ws
      let rhs ← parseFactor
      parseProductRest (Expr.mul lhs rhs))
    <|>
    (do -- Implicit multiplication
      -- No operator between factors, but check if next char is an operator first
      if ← nextCharSatisfies (fun c => c != '+' && c != '-') then
        attempt (do
          let rhs ← parseFactor
          parseProductRest (Expr.mul lhs rhs))
        <|> pure lhs
      else
        pure lhs)
    <|>
    pure lhs

  partial def parseFactor : Parser (Expr R) := do
    (do -- Parenthesized expression
      skipChar '('
      ws
      let e ← parseExpr
      skipChar ')'
      ws
      parsePowerRest e)
    <|>
    (do -- Atom
      skipString "x"
      let idx ← parse
      ws
      let atom := Expr.atom idx
      parsePowerRest atom)
    <|>
    (do -- Constant
      let r ← parse
      ws
      parsePowerRest (Expr.lift r))

  partial def parsePowerRest (base : Expr R) : Parser (Expr R) := do
    (do
      skipChar '^'
      ws
      let n ← parse
      ws
      pure (Expr.pow base n))
    <|>
    pure base
end





def ws : Parser Unit := do
  let _ ← many (satisfy Char.isWhitespace)

def parsePolynomial (target : Type) [Unrepr target] (s : String) : Except String (Expr target) :=
  parseString parseExpr s

open Qq in
def parsePolynomial' (M2R : Type)
[liftInst : ToLeanExpr M2R] [inst : Unrepr M2R] (s : String)
: Option (Lean.Expr → Lean.Expr → List Lean.Expr → MetaM Lean.Expr) :=
  let parsed := parseString (@parseExpr M2R inst) s
  match parsed with
  | Except.ok e => do

    let e' := fun S f atoms => Expr.toLeanExpr' S f atoms e
    some (e')

  | Except.error _ =>
    none

-- def parsePolynomial' {R S M2R} [mInst : M2Type R M2R] [uInst : Unrepr M2R] (s : String) (lift : R → S) (atoms : List S) : Except String (S) :=
--   let output' := parseString (@parseExpr M2R uInst) s
--   match output' with
--   | .ok expr =>
--     let r := exprToString lift atoms expr
--     match String.toRat? r with
--     | some q => .ok q
--     | none =>
--       -- fallback to just returning the expression itself
--       .ok (lift (expr.to_lean : R))
--   | .error msg =>
--     .error msg



-- open IO RatM2 IntM2 RealM2 ComplexM2
-- def parsePolynomial' := parsePolynomial M2Real
-- #eval parsePolynomial' "x1^2 + 2*x1 + 3/4" |>.toOption|>.get!
-- #eval parsePolynomial' "((x1 + x2)^2)^3" |>.toOption|>.get!
-- #eval parsePolynomial' "3.5*x1 + 2*x2^3"|>.toOption|>.get!
-- #eval parsePolynomial' "x0-2"|>.toOption|>.get!
-- #eval parsePolynomial' "x0^2-x0x1+x1^2"|>.toOption|>.get!
-- #eval parsePolynomial' "(372)-2"|>.toOption|>.get!
-- #eval parsePolynomial' "372-2"|>.toOption|>.get!




end Parser
