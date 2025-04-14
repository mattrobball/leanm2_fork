import LeanM2.Tactic


section Basic


example (x y : ℤ) : ((fun (t:ℤ) => t) 2) * x + ((fun (t:ℤ) => t) 3) * y ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t:ℤ) => t) [x, y]

example (x : ℤ) : 10 * x ∈ Ideal.span {5 * x} := by
  lean_m2 (fun (t:ℤ) => t) [x]

example (x y z : ℤ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 (fun (t:ℤ) => t) [x, y, z]

example (x y z : ℚ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 (fun (t:ℚ) => t) [x, y, z]

example (x y : ℚ) : 3 * x^2 + 2 * y^2 ∈ Ideal.span {x^2, y^2} := by
  lean_m2 (fun (t:ℚ) => t) [x, y]
  ring

example (x : ℤ) : 6 * x ∈ Ideal.span {2 * x, 3 * x} := by
  lean_m2 (fun (t:ℤ) => t) [x]

example (a b c : ℚ) : a * b^2 * c^3 ∈ Ideal.span {a, b, c} := by
  lean_m2 (fun (t:ℚ) => t) [a, b, c]


end Basic



section Noncomputable



example (x y : ℝ) : 3 * x + 5 * y ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t:ℝ) => t) [x, y]

example (x y z : ℝ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 (fun (t:ℝ) => t) [x, y, z]

example (x : ℝ) : Real.sin x * Real.cos x ∈ Ideal.span {Real.sin x, Real.cos x} := by
  lean_m2 (fun (t:ℝ) => t) [x]

example (z w : ℂ) : 2 * z + 3 * w ∈ Ideal.span {z, w} := by
  lean_m2 (fun (t:ℂ) => t) [z, w]

example (z : ℂ) : z * Complex.conj z ∈ Ideal.span {z} := by
  lean_m2 (fun (t:ℂ) => t) [z]

example (z w : ℂ) : z^2 * w^3 + z * w ∈ Ideal.span {z, w} := by
  lean_m2 (fun (t:ℂ) => t) [z, w]



end Noncomputable



section DependentlyTyped


example (x y : Polynomial ℤ) : x^2 * y + y^3 ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t:ℤ) => Polynomial.C t) [x, y]

example (p q : Polynomial ℚ) : 3 * p^2 + 2 * q^3 ∈ Ideal.span {p, q} := by
  lean_m2 (fun (t:ℚ) => Polynomial.C t) [p, q]

example (f g h : Polynomial ℝ) : f * g^2 + h^3 ∈ Ideal.span {f, g, h} := by
  lean_m2 (fun (t:ℝ) => Polynomial.C t) [f, g, h]

example (p q : Polynomial ℂ) : p^2 * q + p * q^2 ∈ Ideal.span {p * q} := by
  lean_m2 (fun (t:ℂ) => Polynomial.C t) [p, q]

example (r s : Polynomial ℚ) : r^3 + s^3 ∈ Ideal.span {r + s, r * s} := by
  lean_m2 (fun (t:ℚ) => Polynomial.C t) [r, s]



end DependentlyTyped



section FiniteFields

example (x y : ZMod 5) : 3 * x + 4 * y ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t : ZMod 5) => t) [x, y]

example (x : ZMod 7) : 3 * x ∈ Ideal.span {2 * x} := by
  lean_m2 (fun (t : ZMod 7) => t) [x]

example (x y : ZMod 11) : x^2 + y^2 ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t : ZMod 11) => t) [x, y]

example (x y z : ZMod 3) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by
  lean_m2 (fun (t : ZMod 3) => t) [x, y, z]

example (x : ZMod 13) : 4 * x^3 ∈ Ideal.span {2 * x} := by
  lean_m2 (fun (t : ZMod 13) => t) [x]


end FiniteFields



section Quotients

example (x y : QM2 (Ideal.span {(X : Polynomial ℚ)^2 - 2})) : 3 * x + 5 * y ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t : ℚ) => QM2.mk t) [x, y]

example (x : QM2 (Ideal.span {(X : Polynomial ℚ)^2 - 2})) : x^2 ∈ Ideal.span {2} := by
  lean_m2 (fun (t : ℚ) => QM2.mk t) [x]

example (x y : QM2 (Ideal.span {(X : Polynomial ℚ)^2 - 3})) : x^2 * y + x * y^2 ∈ Ideal.span {x, y} := by
  lean_m2 (fun (t : ℚ) => QM2.mk t) [x, y]

example (x : QM2 (Ideal.span {(X : Polynomial ℚ)^3 + (X : Polynomial ℚ) + 1})) :
  x^3 + x + 1 ∈ Ideal.span {0} := by
  lean_m2 (fun (t : ℚ) => QM2.mk t) [x]

example (x y : QM2 (Ideal.span {(X : Polynomial ℚ)^2 + (Y : Polynomial ℚ)^2 - 1})) :
  x^2 + y^2 ∈ Ideal.span {1} := by
  lean_m2 (fun (t : ℚ) => QM2.mk t) [x, y]


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


example (x : ℝ) : Ideal.span {((2:ℚ):ℝ) * x} = Ideal.span {x}  := by
  ext t
  sorry


-- Radical Ideals? using nullstellensatz




end Applications


example (x: ℚ) : ((fun (t:ℚ) => t) 2) + x ∈ Ideal.span {x}  := by
  -- let f := fun (t:ℚ) => t
  lean_m2 (fun (t:ℚ) => t) [x]

example (x: ℝ) : ((fun (t:ℝ) => t) (Real.sqrt ((2:ℚ):ℝ))) + x ∈ Ideal.span {((fun (t:ℝ) => t) (Real.sqrt ((2:ℚ):ℝ))) + x}  := by
  lean_m2 (fun (t:ℝ) => t) [x]

example (x y z: ℚ) : x^2+y^2 ∈ Ideal.span {x,y,z}  := by
  lean_m2 (fun (t:ℚ) => t) [x,y,z]

example (x y z: ℂ) : x^2+y^2 ∈ Ideal.span {x,y,z}  := by
  lean_m2 (fun (t:ℂ) => t) [x,y,z]


example (x y : ℚ) : x^2+y^2 ∈ Ideal.span {x,y}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y]

example (x y : ℚ) : x^2+x*y^2 ∈ Ideal.span {x}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y]

example (x y : ℚ) : x^2+y^2 ∈ Ideal.span {}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y]



example (x y : ℚ) : x^3+y^3 ∈ Ideal.span {x+y}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y]

example (x y : Polynomial ℚ) : x^3+y^3 ∈ Ideal.span {x+y}  := by
  lean_m2 (fun (t:ℚ) => Polynomial.C t) [x,y]




example (x y z: ℚ) : x^2+y ∈ Ideal.span {x^2,y}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y,z]


example (x y z : ℚ) : x^2*y+y*x ∈ Ideal.span {x, y, z}  := by
  lean_m2 (fun (x:ℚ) => x) [x,y,z]




example (a b c d e f : ℚ) : a^3*c+a^2*b*d-a^2*e*f+a*d*e^2-a*c*d*f
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2 (fun (x:ℚ) => x) [a,b,c,d,e,f]


example (a b c d e f : ℚ) : a^4+a^2*b*c-a^2*d*e+a*b^3+b^2*c*d-b^2*e*f+a*c^3+b*c^2*d-c^2*f^2
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2 (fun (x:ℚ) => x) [a,b,c,d,e,f]



example (x : ℝ) : Ideal.span {((2:ℚ):ℝ) * x} = Ideal.span {x}  := by
  ext t
