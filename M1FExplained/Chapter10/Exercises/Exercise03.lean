import Mathlib.Tactic

namespace Chapter10.Exercise03


-- part a

/- 
A train leaves for St. Petersburg from Moscow every 7 hours. 
Show that some days it is possible to catch this train at 9:00 am
-/

/- 
Given that the train leaves at x o'clock on some day, we wish 
to show that it is possible for it to leave at 9:00 am eventually.
i.e there is some multiple of 7 we can add to x so that it is 
congrueng to 9 modulo 24. 

(Since the train leaves every 7 hours and we are using 24 hour time) 
-/

-- Useful result for the proof of part a
def Int.modEq_sub_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a - n * c ≡ b [ZMOD n] := by
  convert Int.modEq_add_fac (-c) ha using 1
  ring

lemma part_a (x : ℕ) (hx : 24 > x) : ∃ (m : ℕ), x + 7 * m ≡ 9 [MOD 24] := by
  use 7 * (33 - x)
  rw [← Int.coe_nat_modEq_iff]
  push_cast
  rw [Nat.cast_sub (show x ≤ 33 by linarith)]
  ring_nf
  rw [show (48 : ℤ) = 2 * 24 by norm_num, ← mul_assoc, mul_comm]
  apply Int.modEq_sub_fac
  norm_num


-- part b 

/- 
Whenever there is a 9:00 am train, Ivan akes it to visit his aunt Olga.
How often does Olga see her nephew?
-/

/-
Given the train leaves at 9:00 am, we are looking for the minimum amount of 
time that passes before the train leaves at 9:00 am again. Hence, we are 
looking for the first such n so that 24 * n is a multiple of 7, since the train
leaves every 7 hours. Clearly this is 7, so Olga sees her nephew once a week.
-/


lemma part_b : Nat.lcm 24 7 = 24 * 7 := by norm_num

-- part c

/-
Discuss the corresponding problem involving he train to Vladivostok, which leaves 
Moscow once every 14 hours.
-/

/-
gcd(24, 14) = 2, hence if a train leaves 12 for Vladivostock, then it is possible to catch a train
at any even hour on some day. Similarly if a train leaves at 11, it is possible to catch a train
at any odd hour.
-/

lemma part_c_i (t y : ℕ) (h : 24 > t ∧ 24 > y) (hpara : Even t ∧ Even y) : ∃ (m : ℕ), t + 14 * m ≡ y [MOD 24] := by sorry


lemma part_c_ii (t y : ℕ) (h : 24 > y ∧ 24 > t) (hpara : Odd t ∧ Even y) : ¬∃ (m : ℕ), t + 14 * m ≡ y [MOD 24] := by sorry






end Chapter10.Exercise03