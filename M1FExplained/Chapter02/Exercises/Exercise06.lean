import Mathbin.Tactic.Default
import Mathbin.Data.Real.Irrational

namespace Chapter02.Exercise06

/-- Between any two different real numbers there is a rational
number and an irrational number. -/
theorem exercise :
    ∀ {a b : ℝ} (hab : a < b),
      (∃ x : ℚ, a < x ∧ ↑x < b) ∧ ∃ (y : ℝ) (hy : Irrational y), a < y ∧ y < b :=
  by sorry

end Chapter02.Exercise06

