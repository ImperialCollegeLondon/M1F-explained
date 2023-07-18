import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.ModEq

namespace Chapter13.Exercise06

/-
Let p be a prime number, and let a be an integer that is not divisible by p.
Prove that the congruence equation ax ≡ 1 mod p has a solution x ∈ ℤ.
-/
theorem mod_inv_exists (p : ℕ) (hp : Prime p) (a : ℤ) (ha : ¬↑p ∣ a) :
    ∃ x : ℤ, a * x ≡ 1 [ZMOD p] := by sorry

end Chapter13.Exercise06

