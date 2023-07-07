import Mathbin.Data.Int.Modeq
import Mathbin.Data.Nat.Prime

namespace Chapter13.Exercise02

/-
Let p be a prime number and k a positive integer.
(a) Show that if x is an integer such that x^2 ≡ x mod p, then x ≡ 0 or 1 mod p.
(b) Show that if x is an integer such that x^2 ≡ x mod p^k, then x ≡ 0 or 1 mod p^k.
-/
open Nat

theorem part_a (p : ℤ) (hp : Prime p) (x : ℤ) :
    x ^ 2 ≡ x [ZMOD p] → x ≡ 0 [ZMOD p] ∨ x ≡ 1 [ZMOD p] := by sorry

theorem part_b (p : ℤ) (hp : Prime p) (k : ℕ) (hk : k > 0) (x : ℤ) :
    x ^ 2 ≡ x [ZMOD p ^ k] → x ≡ 0 [ZMOD p ^ k] ∨ x ≡ 1 [ZMOD p ^ k] := by sorry

end Chapter13.Exercise02

