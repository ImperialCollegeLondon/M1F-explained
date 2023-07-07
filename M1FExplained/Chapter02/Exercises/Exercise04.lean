import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

namespace Chapter02.Exercise04

def Rational (x : ℝ) :=
  ∃ a b : ℤ, x = a / b

/-- For a, b rational and x irrational, if (x+a)/(x+b) is rational, then a = b. -/
theorem part_a (a : ℚ) (b : ℚ) (x : ℝ) (hx : Irrational x) : Rational ((x + a) / (x + b)) → a = b :=
  by sorry

/--
For x, y rational such that (x^2 + x + √2)/(y^2 + y + √2) is rational, either x = y or x + y = -1. -/
theorem part_b (x : ℚ) (y : ℚ)
    (h : Rational (((x : ℝ) ^ 2 + x + Real.sqrt 2) / ((y : ℝ) ^ 2 + y + Real.sqrt 2))) : x = y ∨ x + y = -1 :=
  by sorry

end Chapter02.Exercise04

