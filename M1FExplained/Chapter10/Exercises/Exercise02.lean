import Mathlib.Tactic

namespace Chapter10.Exercise02

-- part a

/-
Show that if a, b are positive integers and d = gcd(a, b), there exists positive integers s, t such
that d = s * a - t * b
-/

lemma part_a (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : 
  ∃ (s t : ℤ), 0 < s ∧ 0 < t ∧ Int.gcd a b = s * a - t * b := by 
  have := Int.gcd_eq_gcd_ab a b
  set s' := Int.gcdA a b with rfl
  set t' := Int.gcdB a b with rfl
  set p := max ((b - s') / b) ((a + t') / a)
  use s' + p * b, t' - p * a
  repeat (any_goals constructor)
  ·sorry
  ·sorry
  ·

-- part b

/-
Find such positive integers s, t for each of the cases (i) - (iii) in Exercise 1.
-/

/-
These are exatly the integers we found in Exercise 1, and lean finds them for us easily.
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