import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic
import Mathlib.Data.Int.Parity
import Mathlib.Data.ZMod.Basic

-- even and odd
-- even and odd
namespace Chapter01.Exercise06

theorem part_a : Real.sqrt 6 - Real.sqrt 2 > 1 :=
  by
  have a := Real.sqrt_nonneg (6 : Real)
  have b := Real.sqrt_nonneg (2 : Real)
  have _ : 2 * Real.sqrt 2 ≥ 0 := by linarith
  suffices Real.sqrt 6 > 1 + Real.sqrt 2 by linarith
  suffices Real.sqrt 6 ^ 2 > (1 + Real.sqrt 2) ^ 2 by exact lt_of_pow_lt_pow 2 a this
  rw [Real.sq_sqrt, add_sq 1 (Real.sqrt 2), Real.sq_sqrt]
  suffices 2 * Real.sqrt 2 < 3 by linarith
  suffices (2 * Real.sqrt 2) ^ 2 < 3 ^ 2 by
    refine' lt_of_pow_lt_pow 2 _ this
    norm_num
  · rw [mul_pow, Real.sq_sqrt]
    · norm_num
    · norm_num
  norm_num
  norm_num
theorem part_b_n (n : ℕ) : Even (n ^ 2) → Even n :=
  by
  contrapose
  repeat' rw [Nat.not_even_iff]
  intro h
  rw [sq]
  exact Nat.odd_mul_odd h h

theorem part_c (n : ℤ) (h : ∃ m : ℤ, n = m ^ 3 - m) : 6 ∣ n :=
  by
  rcases h with ⟨m, rfl⟩
  rw [← Int.modEq_zero_iff_dvd]
  have := ZMod.int_cast_eq_int_cast_iff (m ^ 3 - m) 0 6
  norm_cast at this 
  rw [← this]
  rw [Int.cast_sub, Int.cast_pow]
  generalize (↑m : ZMod 6) = m6
  revert m6
  decide

end Chapter01.Exercise06

