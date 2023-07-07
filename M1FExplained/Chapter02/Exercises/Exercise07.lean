import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

namespace Chapter02.Exercise07

def PositiveInteger (x : ℝ) :=
  x ∈ Set.range (fun a ↦ a : ℕ → ℝ) ∧ x > 0

/-- There is a positive integer n such that √(n - 2) + √(n + 2) is also a positive integer. -/
theorem exercise : ∃ n : ℕ, n > 0 ∧ PositiveInteger (Real.sqrt (n - 2) + Real.sqrt (n + 2)) := by
  sorry

end Chapter02.Exercise07

