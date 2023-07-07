import Mathbin.Topology.Instances.Real

namespace Chapter23.Exercise07

open Filter Real

open scoped Topology

theorem part_i_a (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : ∀ n : ℕ, a (n + 1) = (a n ^ 2 + 2) / (2 * a n)) :
    ∃ M : ℝ, ∀ n : ℕ, abs (a n) ≤ M := by sorry

theorem part_i_b (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : ∀ n, a (n + 1) = (a n ^ 2 + 2) / (2 * a n)) :
    ∀ n, n ≥ 2 → a n ≥ a (n + 1) := by sorry

theorem part_ii (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : ∀ n, a (n + 1) = (a n ^ 2 + 2) / (2 * a n)) :
    Tendsto a atTop (𝓝 2) := by sorry

end Chapter23.Exercise07

