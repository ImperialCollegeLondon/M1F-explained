import Mathbin.Data.Real.Sqrt
import Mathbin.Data.Complex.Exponential

namespace Chapter23.Exercise01

open Filter Real

open scoped Topology

theorem part_i : Tendsto (fun n : ℕ => n / (n + 5) : ℕ → ℝ) atTop (𝓝 1) :=
  by
  rw [tendsto]
  sorry

theorem part_ii : Tendsto (fun n : ℕ => 1 / sqrt (n + 5)) atTop (𝓝 0) := by sorry

theorem part_iii : Tendsto (fun n : ℕ => ↑n * sqrt n / (n + 5)) atTop atTop := by sorry

theorem part_iv : Tendsto (fun n : ℕ => (-1) ^ n * sin n / sqrt n) atTop (𝓝 0) := by sorry

theorem part_v :
    Tendsto (fun n : ℕ => (↑n ^ 3 - 2 * sqrt n + 7) / (2 - n ^ 2 - 5 * n ^ 3)) atTop (𝓝 (-1 / 5)) :=
  by sorry

theorem part_vi (n : ℕ) : ¬∃ l : ℝ, Tendsto (fun n => (1 - (-1) ^ n * n) / n : ℕ → ℝ) atTop (𝓝 l) :=
  by sorry

theorem part_vii : Tendsto (fun n : ℕ => sqrt (n + 1) - sqrt n) atTop (𝓝 0) := by sorry

end Chapter23.Exercise01

