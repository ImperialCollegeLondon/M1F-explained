import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

namespace Chapter02.Exercise02

def Rational (x : ℝ) :=
  ∃ a b : ℤ, x = a / b

theorem part_a : Irrational (Real.sqrt 2 + Real.sqrt (3 / 2)) := by sorry

theorem part_b : Irrational (1 + Real.sqrt 2 + Real.sqrt (3 / 2)) := by sorry

theorem part_c : Rational (2 * Real.sqrt 18 - 3 * Real.sqrt 8 + Real.sqrt 4) := by sorry

theorem part_d : Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) := by sorry

theorem part_e : Rational (Real.sqrt 2 + Real.sqrt 3 - Real.sqrt (5 + 2 * Real.sqrt 6)) := by sorry

end Chapter02.Exercise02

