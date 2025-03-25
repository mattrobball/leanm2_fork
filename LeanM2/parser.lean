
-- import SciLean
-- import LeanM2.toM2
import Lean.Data.Json.Basic
import Mathlib.Data.FP.Basic
import Std.Internal.Parsec.String
import Mathlib.Data.Nat.Digits
-- import SciLean
-- import LeanM2.toM2
-- import LeanM2.mwe
import LeanM2.defs
import Std.Internal.Parsec.String
import Mathlib.Data.Nat.Digits



open Std.Internal.Parsec Std.Internal.Parsec.String
open Lean




class Unrepr (α : Type) where
  parse : Parser α
export Unrepr (parse)

instance : Unrepr Nat where
  parse := digits


def parseString (p : Parser α) (s : String) : Except String α :=
  match (p <* eof) s.mkIterator with
  | .success _ res => .ok res
  | .error _ msg => .error msg



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




section Parser

-- Parser for Expr ℚ
instance : Unrepr ℚ where
  parse := do
    let s ← manyChars (satisfy fun c => c.isDigit || c == '/' || c == '.' || c == '-')
    match s.toRat? with
    | some q => pure q
    | none => fail s!"Could not parse '{s}' as a rational number"

mutual
  partial def parseExpr : Parser (Expr ℚ) := do
    let res ← parseTerm
    let res ← parseSumRest res
    return res

  partial def parseSumRest (lhs : Expr ℚ) : Parser (Expr ℚ) := do
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
      parseSumRest (Expr.add lhs (Expr.mul (Expr.lift (-1)) rhs)))
    <|>
    pure lhs

  partial def parseTerm : Parser (Expr ℚ) := do
    let res ← parseFactor
    let res ← parseProductRest res
    return res

  partial def parseProductRest (lhs : Expr ℚ) : Parser (Expr ℚ) := do
    (do
      skipChar '*'
      ws
      let rhs ← parseFactor
      parseProductRest (Expr.mul lhs rhs))
    <|>
    pure lhs

  partial def parseFactor : Parser (Expr ℚ) := do
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

  partial def parsePowerRest (base : Expr ℚ) : Parser (Expr ℚ) := do
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

def parsePolynomial (s : String) : Except String (Expr ℚ) :=
  parseString parseExpr s

open IO
#eval parsePolynomial "x_1^2 + 2*x_1 + 3/4" |>.toOption|>.get!
#eval parsePolynomial "((x_1 + x_2)^2)^3" |>.toOption|>.get!
#eval parsePolynomial "3.5*x_1 + 2*x_2^3"|>.toOption|>.get!
#eval parsePolynomial "x0^2"|>.toOption|>.get!

end Parser
