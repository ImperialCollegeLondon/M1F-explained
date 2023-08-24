import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.ModEq

/-
a) Use Proposition 26.7 to find the remainder when 3798 is divided by 24.
(b) True or false: if a, n are coprime positive integers and a^2 ≡ 1 mod n, then a ≡ ±1 mod n.
(c) True or false: if a, m, n are positive integers such that hcf(a, n) = hcf(m,φ (n)) = 1, then
                            a^m ≡ 1 mod n ⇒ a ≡ 1 mod n.
-/

--- part a)
example :  37^98 ≡ 1 [MOD 24] := by norm_num 

--- part b)
example : ¬ ∀ (a b n : ℕ), a > 0 ∧  b > 0 ∧  a.coprime n ∧ (a^2 ≡ 1 [MOD n] → (a ≡  1 [MOD n])
∨ (a ≡ n-1 [MOD n])) := sorry

