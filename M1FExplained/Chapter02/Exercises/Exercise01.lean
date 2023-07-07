import Mathbin.Tactic.Default
import Mathbin.Data.Real.Irrational

namespace Chapter02.Exercise01

/-- √3 is irrational. -/
theorem part_a : Irrational (Real.sqrt 3) := by sorry

/-- There are no rationals r,s such that √3 = r + s √2. -/
theorem part_b : ¬∃ r s : ℚ, Real.sqrt 3 = r + s * Real.sqrt 2 := by sorry

end Chapter02.Exercise01

