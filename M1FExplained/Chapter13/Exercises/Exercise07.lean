import Mathlib.Data.Int.ModEq

namespace Chapter13.Exercise07

/-
Show that every square is congruent to 0, 1, or -1 modulo 5, and is congruent to 0, 1, or 4 modulo 8.

Suppose n is a positive integer such that 2n + 1 and 3n + 1 are squares. Prove that n is divisible by 40.

Find a value of n such that 2n + 1 and 3n + 1 are squares. Can you find another value? (Calculators allowed!)
-/
theorem sq_mod_five (n : ℤ) : n ^ 2 ≡ 0 [ZMOD 5] ∨ n ^ 2 ≡ 1 [ZMOD 5] ∨ n ^ 2 ≡ -1 [ZMOD 5] := by
  sorry

theorem sq_mod_eight (n : ℤ) : n ^ 2 ≡ 0 [ZMOD 8] ∨ n ^ 2 ≡ 1 [ZMOD 8] ∨ n ^ 2 ≡ 4 [ZMOD 8] := by
  sorry

theorem div_by_forty (n : ℤ) (hn : n > 0) (h₁ : ∃ k : ℤ, k ^ 2 = 2 * n + 1)
    (h₂ : ∃ l : ℤ, l ^ 2 = 3 * n + 1) : 40 ∣ n := by sorry

theorem exist_sq : ∃ n : ℤ, n > 0 ∧ (∃ k : ℤ, k ^ 2 = 2 * n + 1) ∧ ∃ l : ℤ, l ^ 2 = 3 * n + 1 := by
  sorry

end Chapter13.Exercise07

