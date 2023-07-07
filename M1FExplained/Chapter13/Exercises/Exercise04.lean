import Mathbin.Data.Nat.Digits

open Nat

open Int

namespace Chapter13.Exercise04

/-
(a) Prove the "rule of 9": an integer is divisible by 9 if and only if the sum of its digits is divisible by 9.
(b) Prove the "rule of 11" stated in Example 13.6. Use this rule to decide in your head whether the number 82918073579 is divisible by 11.
-/
theorem part_a (n : ℤ) : 9 ∣ n ↔ 9 ∣ (digits 10 n.natAbs).Sum := by sorry

theorem part_b (n : ℤ) :
    11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n.natAbs).map fun n : ℕ => ↑n).alternatingSum := by sorry

end Chapter13.Exercise04

