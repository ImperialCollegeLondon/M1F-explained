import Mathlib.Topology.Instances.Real

namespace Chapter23.Exercise06

open Filter Real

open scoped Topology

theorem problem_6 (f : ℕ → ℝ) (hf : ∀ n, f (n + 1) ≤ f n) (hf_bdd : ∃ a, ∀ n, f n ≤ a) :
    ∃ a, Tendsto f atTop (𝓝 a) := by sorry

end Chapter23.Exercise06

