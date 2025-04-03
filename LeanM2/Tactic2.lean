import LeanM2.defs
import LeanM2.parser
import LeanM2.toM2
import Lean.PrettyPrinter.Delaborator.Basic
import Mathlib.Tactic.Use

-- variable {x0 x1 x2 x3 : ℚ}

-- -- twisted cubic curve
-- def twistedCubic : Ideal ℚ := Ideal.span {-x1^2-x0*x2, -x1*x2+x0*x3, -x2^2+x1*x3}
-- --projection center: [1:0:0:1]
-- def p : Ideal ℚ := Ideal.span {x0-x3,x1,x2}



def x0 := (1 : ℚ)
def x1 := (0 : ℚ)
def x2 := (0 : ℚ)
def x3 := (1 : ℚ)

def twistedCubic : Ideal ℚ := Ideal.span {-x1^2+x0*x2, -x1*x2+x0*x3, -x2^2+x1*x3}

def p : Ideal ℚ := Ideal.span {x0-x3,x1,x2}
--allow unfolding???
-- #eval IdExprToString [x0,x1,x2,x3] (RingHom.id ℚ) (Ideal.span {-x1^2+x0*x2, -x1*x2+x0*x3, -x2^2+x1*x3})


def projection_defining_eq : ℚ := 
  let cmd := s!"R=QQ[x0,x1,x2,x3]\n"



-- def project {R} [Ring R] (S : Ideal R) (x : R)