import Mathbin.Topology.Instances.Real
import Mathbin.Data.Complex.Exponential
import Mathbin.Data.Real.Irrational

namespace Chapter23.Exercise08

open Filter Real

open scoped Topology

open scoped BigOperators

noncomputable def e : ℕ → ℝ := fun n => ∑ i in Finset.range (n + 1), 1 / Nat.factorial i

theorem part_a (n : ℕ) : ∃ p : ℕ, e n = p / Nat.factorial n := by sorry

theorem part_b (n : ℕ) : 0 < exp 1 - e n ∧ exp 1 - e n < 1 / (n * Nat.factorial n) := by sorry

theorem part_c :
    ∃ p : ℕ → ℝ,
      ∀ n : ℕ,
        0 < exp 1 * Nat.factorial n - e n ∧
          exp 1 * Nat.factorial n - e n < 1 / (n * Nat.factorial n) :=
  by sorry

-- Assume e is rational, then show n!e ∈ ℤ for some n.
theorem part_d : Irrational (exp 1) := by sorry

end Chapter23.Exercise08

