import Mathbin.Topology.Instances.Real

namespace Chapter23.Exercise09

open Filter Real

open scoped Topology

variable (a : ℕ → ℝ)

theorem part_a : (¬∀ l : ℝ, Tendsto a atTop (𝓝 l)) ↔ Tendsto a atTop atTop := by sorry

theorem part_c : (∀ R > 0, ∃ N : ℕ, ∀ n ≥ N, a n > R) ↔ Tendsto a atTop atTop := by sorry

theorem part_d : (¬∀ L : ℝ, ∀ ε : ℝ, ∃ N : ℕ, ∀ n ≥ N, abs (a n - L) > ε) ↔ Tendsto a atTop atTop :=
  by sorry

theorem part_e : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, a n > 1 / ε) ↔ Tendsto a atTop atTop := by sorry

theorem part_f : (¬∀ n : ℕ, a (n + 1) > a n) ↔ Tendsto a atTop atTop := by sorry

theorem part_g : (¬∃ N : ℕ, ∀ R > 0, ∀ n ≥ N, a n > R) ↔ Tendsto a atTop atTop := by sorry

theorem part_h : (¬∀ R : ℝ, ∃ n : ℕ, a n > R) ↔ Tendsto a atTop atTop := by sorry

end Chapter23.Exercise09

