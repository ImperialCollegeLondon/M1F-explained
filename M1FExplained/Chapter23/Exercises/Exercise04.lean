import Mathlib

namespace Chapter23.Exercise04

open Filter Real

open scoped Topology

theorem part_i_a : ∃ b : ℝ, ∀ n, abs (n ^ 3 / (n ^ 3 - 1) : ℝ) ≤ b := by sorry

theorem part_i_c (n : ℕ) : (n : ℝ) ^ 3 / (n ^ 3 - 1) ≥ (n + 1) ^ 3 / ((n + 1) ^ 3 - 1) := by sorry

theorem part_i_d (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = n ^ 3 / (n ^ 3 - 1)) :
    ∃ l : ℝ, Tendsto a atTop (𝓝 l) := by sorry

theorem part_ii_a : ∃ M : ℝ, ∀ m : ℕ, abs ((2 : ℝ) ^ (1 / (m : ℝ))) ≤ M := by sorry

theorem part_ii_c (n : ℕ) : 2 ^ (1 / n) ≥ 2 ^ (1 / (n + 1)) := by sorry

theorem part_ii_d (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = 2 ^ (1 / n)) : ∃ l : ℝ, Tendsto a atTop (𝓝 l) :=
  by sorry

theorem part_iii_a : ∃ b : ℝ, ∀ n : ℕ, abs (1 - (-1 : ℤ) ^ n / ↑n) ≤ b := by sorry

theorem part_iii_b (n : ℕ) : ¬∀ n : ℕ, (1 : ℝ) - (-1) ^ n / n ≤ 1 - (-1) ^ (n + 1) / (n + 1) := by
  sorry

theorem part_iii_c (n : ℕ) :
    ¬∀ m : ℕ, (1 - (-1) ^ n / n.cast : ℝ) ≥ (1 - (-1) ^ (n + m) / (n + m).cast : ℝ) := by sorry

theorem part_iii_d (f : ℕ → ℝ) (hf : ∀ n : ℕ, f n = 1 - (-1) ^ n / n) :
    ∃ r : ℝ, Tendsto f atTop (𝓝 r) := by sorry

theorem part_iv_a : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, abs (5 * n - n ^ 2 : ℝ) ≥ m := by sorry

theorem part_iv_b : ¬∀ n : ℕ, abs (5 * n - n ^ 2 : ℝ) ≤ abs (5 * (n + 1) - (n + 1) ^ 2 : ℝ) := by
  sorry

theorem part_iv_c : ¬∀ n : ℕ, abs (5 * n - n ^ 2 : ℝ) ≥ abs (5 * (n + 1) - (n + 1) ^ 2 : ℝ) := by
  sorry

theorem part_iv_d : Tendsto (fun n : ℕ => abs (5 * n - n ^ 2 : ℝ)) atTop atTop := by sorry

end Chapter23.Exercise04

