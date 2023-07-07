import Mathbin.Topology.Instances.Real

namespace Chapter23.Exercise03

open Filter Real

open scoped Topology

theorem leibeck_23_3 (S : Set ℝ) (c : ℝ) (hc : IsLUB S c) :
    ∃ f : ℕ → ℝ, (∀ n, f n ∈ S) ∧ Tendsto f atTop (𝓝 c) := by sorry

end Chapter23.Exercise03

