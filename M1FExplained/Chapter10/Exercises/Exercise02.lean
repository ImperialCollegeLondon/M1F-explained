import Mathlib.Tactic

namespace Chapter10.Exercise02

/-
Part a asks us to prove that for natural numbers a, b, ∃ s t : ℕ such that gcd(a, b) = s * a - t * b
-/

lemma part_a (a b d : ℕ) (hd : d = Nat.gcd a b) : ∃ (s t : ℕ),  d = s * a - t * b := by sorry

/-
Part b asks us to find such s and t for the examples in exercise 01, Lean provides us with these: 
-/

-- a = 17, b = 29

#eval Nat.gcd 17 29 -- 1
#eval Nat.gcdA 17 29 -- 12
#eval Nat.gcdB 17 29 -- -7
-- So 1 = 12 * 17 - 7 * 29, giving s = 12 and t = 7

-- a = 552, b = 713

#eval Nat.gcd 713 552 -- 23
#eval Nat.gcdA 713 552 -- 7
#eval Nat.gcdB 713 552 -- -9
-- So 23 = 7 * 713 - 9 * 552, giving s = 7, t = 9

-- a = 299, b = 345

#eval Nat.gcd 299 345  -- 23
#eval Nat.gcdA 299 345 -- 7
#eval Nat.gcdB 299 345 -- -6
-- So 23 = 7 * 299 - 6 * 345, giving s = 7, t = 6






end Chapter10.Exercise02