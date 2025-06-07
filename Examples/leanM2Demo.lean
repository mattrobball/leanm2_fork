import LeanM2.Tactic


def z := (fun (t:ℤ) => t)
def q := (fun (t:ℚ) => t)
def r := (fun (t:ℝ) => t)
def c := (fun (t:ℂ) => t)

noncomputable def pz := (fun (t:ℤ) => Polynomial.C t)
noncomputable def pq := (fun (t:ℚ) => Polynomial.C t)
noncomputable def pr := (fun (t:ℝ) => Polynomial.C t)
noncomputable def pc := (fun (t:ℂ) => Polynomial.C t)



section Basic

example (x y : ℤ) : 2 * x + 3 * y ∈ Ideal.span {x, y} := by
  lean_m2 z [x, y]

example (x : ℤ) : 10 * x ∈ Ideal.span {5 * x} := by
  lean_m2 z [x]

example (x y z : ℤ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 (fun (t:ℤ) => t) [x, y, z]

example (x y z : ℚ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 q [x, y, z]

example (x y : ℚ) : 3 * x^2 + 2 * y^2 ∈ Ideal.span {x^2, y^2} := by
  lean_m2 q [x, y]

example (x : ℤ) : 6 * x ∈ Ideal.span {2 * x, 3 * x} := by
  lean_m2 z [x]

example (x : ℤ) : x ∈ Ideal.span {x * x} := by
  lean_m2 z [x]

example (x : ℤ) : 1 ∈ Ideal.span {x * x} := by
  lean_m2 z [x]

example (a b c : ℚ) : a * b^2 * c^3 ∈ Ideal.span {a, b, c} := by
  lean_m2 q [a, b, c]



example (a b c d e f : ℚ) : a^3*c+a^2*b*d-a^2*e*f+a*d*e^2-a*c*d*f
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2 q [a,b,c,d,e,f]



example (a b c d e f : ℚ) : a^4+a^2*b*c-a^2*d*e+a*b^3+b^2*c*d-b^2*e*f+a*c^3+b*c^2*d-c^2*f^2
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2 q [a,b,c,d,e,f]


end Basic



section Noncomputable


example (x y : ℝ) : (r (3:ℚ)) * x + (r (5:ℚ)) * y ∈ Ideal.span {x, y} := by
  lean_m2 r [x, y]


example (x : ℝ) : (r Real.pi) * x ∈ Ideal.span {x} := by
  lean_m2 r [x]


example (x y z : ℝ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 r [x, y, z]


example (z : ℂ) :  z ∈ Ideal.span {(-Complex.I)* z}  := by
  lean_m2 (fun (t:ℂ) => t) [z]

example (x y : ℂ) : x^2 + y^2 ∈ Ideal.span {x-Complex.I*y} := by
  lean_m2 (fun (t:ℂ) => t) [x,y]

example (z w : ℂ) : z^2 * w^3 + z * w ∈ Ideal.span {z, w} := by
  lean_m2 c [z, w]



end Noncomputable



section DependentlyTyped


example (x y : Polynomial ℤ) : x^2 * y + y^3 ∈ Ideal.span {x, y} := by
  lean_m2 pz [x, y]

example (p q : Polynomial ℚ) : 3 * p^2 + 2 * q^3 ∈ Ideal.span {p, q} := by
  lean_m2 pq [p, q]


example (f g h : Polynomial ℝ) : f * g^2 + h^3 ∈ Ideal.span {f, g, h} := by
  lean_m2 pr [f, g, h]

example (p q : Polynomial ℂ) : p^2 * q + p * q^2 ∈ Ideal.span {p * q} := by
  lean_m2 pc [p, q]

example (r s : Polynomial ℚ) : r^3 + s^3 ∈ Ideal.span {r + s, r * s} := by
  lean_m2 pq [r, s]

#check GaloisField

end DependentlyTyped



section FiniteFields


example (x y : ZMod 11) : x^2 + y^2 ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t : ZMod 11) => t) [x, y]

example (x y z : ZMod 3) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 (fun (t : ZMod 3) => t) [x, y, z]

example (x y : ZMod 5) : x^3 + y^3 ∈ Ideal.span {x + y} := by
  lean_m2 (fun (t : ZMod 5) => t) [x, y]

example (x y z : ZMod 7) : x^2*y^2 + z^4 ∈ Ideal.span {x*y, z^2} := by
  lean_m2 (fun (t : ZMod 7) => t) [x, y, z]

end FiniteFields



section Quotients
open Polynomial

-- #check DecidableEq
instance {R} [CommRing R] {I : Ideal R}: DecidableEq (R ⧸ I) := by
  sorry


noncomputable def qq := (fun (t : ℚ) => (Ideal.Quotient.mk (Ideal.span {(X:ℚ[X])^2})) (Polynomial.C t))

example (x y : ℚ[X] ⧸ (Ideal.span {(X:ℚ[X])^2})) : x + y ∈ Ideal.span {x, y} := by
  lean_m2 qq [x, y]

noncomputable def qp := (fun (t : ℚ[X]) => (Ideal.Quotient.mk (Ideal.span {(X:ℚ[X])^2})) t)

example (x y : ℚ[X] ⧸ (Ideal.span {(X:ℚ[X])^2})) : x * y ∈ Ideal.span {x^3, y} := by
  lean_m2 qq [x, y]

end Quotients






section Applications


-- extends polyrith

example (a b c d e f : ℚ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  polyrith



example (a b c d e f : ℚ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  have sufficient : a*b*c*d - a*e*f*d ∈ Ideal.span {b*c-e*f} := by
    lean_m2 (fun (x:ℚ) => x) [a,b,c,d,e,f]
  apply Ideal.mem_span_singleton'.1 at sufficient
  simp [mul_zero,h] at sufficient
  linarith



-- Polynomial conditions

example (x y : ℚ) (h : x+y = 0) : x^3 + y^3 = 0 := by
  have sufficient : x^3+y^3 ∈ Ideal.span {x+y} := by
    lean_m2 (fun (x:ℚ) => x) [x,y]
  apply Ideal.mem_span_singleton'.1 at sufficient
  simp [mul_zero,h] at sufficient
  linarith



-- Generalized proof on polynomial conditions


-- Ideal Equality



lemma useful (a b x : ℝ) : a * x + b * x^2 ∈ Ideal.span {x} := by
  lean_m2 (fun (t:ℝ) => t) [x, a, b]

lemma useful' (a x : ℝ) : a * x ∈ Ideal.span {x, x^2} := by
  lean_m2 (fun (t:ℝ) => t) [x, a]

example (x : ℝ) : Ideal.span {x,x^2} = Ideal.span {x}  := by
  ext t
  constructor
  . intro h
    rw [Ideal.mem_span_pair] at h
    rcases h with ⟨a, b, rfl⟩
    exact useful a b x
  . intro h
    rw [Ideal.mem_span_singleton'] at h
    rcases h with ⟨a, rfl⟩
    exact useful' a x





end Applications
