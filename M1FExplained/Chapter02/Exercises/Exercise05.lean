import Mathbin.Tactic.Default
import Mathbin.Data.Real.Irrational

namespace Chapter02.Exercise05

/-- If n is any positive integer, then √n + √2 is irrational. -/
theorem exercise (n : ℕ) (n_pos : n > 0) : Irrational (Real.sqrt n + Real.sqrt 2) := by sorry

end Chapter02.Exercise05

