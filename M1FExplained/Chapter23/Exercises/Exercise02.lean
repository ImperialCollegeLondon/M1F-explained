import Mathbin.Topology.Instances.Real

namespace Chapter23.Exercise02

open Filter Real

open scoped Topology

theorem problem_2 (X : Type _) [TopologicalSpace X] (a : ℕ → X) (l₁ l₂ : X)
    (h₁ : Tendsto a atTop (𝓝 l₁)) (h₂ : Tendsto a atTop (𝓝 l₂)) : l₁ = l₂ := by sorry

end Chapter23.Exercise02

