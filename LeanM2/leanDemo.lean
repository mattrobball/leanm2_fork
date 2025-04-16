import Mathlib.Algebra.Ring.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Ring
open Polynomial



theorem and_comm' {p q : Prop} : p ∧ q ↔ q ∧ p := by
  constructor
  . intro h
    constructor
    . exact h.2
    . exact h.1
  . intro h
    constructor
    . exact h.2
    . exact h.1

theorem and_comm'' {p q : Prop} : p ∧ q ↔ q ∧ p := by
  tauto


theorem square_binomial {R : Type} [CommRing R] (a b : R) :
    (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

theorem even_square_is_even : ∀ n : ℕ, Even n → Even (n^2) := by
  intro n hn
  rcases hn with ⟨k, rfl⟩
  use 2*k^2
  ring

theorem degree_mul [CommRing R] [NoZeroDivisors R] {p q : R[X]}
: degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)


theorem sum_of_primes_gt_3_is_even (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : p > 3) (hq3 : q > 3) : Even (p + q) := by

  have x_odd (x : Nat) (hx : Nat.Prime x) (hx3 : x>3): Odd x := by
    have duh : x ≠ 2 := by
      intro contra
      linarith
    exact Nat.Prime.odd_of_ne_two hx duh

  have p_odd : Odd p := x_odd p hp hp3
  have q_odd : Odd q := x_odd q hq hq3

  exact Odd.add_odd (x_odd p hp hp3) (x_odd q hq hq3)
