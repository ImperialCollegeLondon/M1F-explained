import Mathlib.Algebra.Associated
import Mathlib.Algebra.Parity
import Mathlib.Tactic

namespace Chapter01.Exercise09

theorem part_a : ¬ ∀ n : ℤ, (Prime n) → ¬ (Even n) := by
  push_neg
  use 2
  constructor
  . exact Int.prime_two
  . exact even_two

theorem part_b : ∀ n : ℤ, ∃a b c d e f g h : ℤ,
                n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 +
                    e ^ 3 + f ^ 3 + g ^ 3 + h ^ 3 := by
  sorry

theorem part_c : ∃ x : ℤ, ∀ n : ℤ, x ≠ n^2 + 2 := by sorry

theorem part_d : ¬ ∃ x : ℤ, ∀ n : ℤ, x ≠ n + 2 := by
  push_neg
  intro x
  use (x - 2)
  simp

theorem part_e : ¬ ∀ y : ℤ, y ≥ 1 →  Prime (5 * y ^ 2 + 5 * y + 1) := by
  sorry

theorem part_f : ∀ y : ℤ, y^2 < 0 → Prime (5 * y ^ 2 + 5 * y + 1) := by
  sorry