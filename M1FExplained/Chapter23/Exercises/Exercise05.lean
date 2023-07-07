import Mathbin.Topology.Instances.Real

namespace Chapter23.Exercise05

open Filter Real

open scoped Topology

theorem problem_5 (a : ℝ) (f : ℕ → ℝ) :
    (∃ N, ∀ ε > 0, ∀ n ≥ N, abs (f n - a) < ε) ↔ ∃ N, ∀ n ≥ N, f n = a := by sorry

end Chapter23.Exercise05

