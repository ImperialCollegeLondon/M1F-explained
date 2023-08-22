import Mathlib.Tactic

namespace Chapter10.Exercise02

-- part a

/-
Show that if a, b are positive integers and d = gcd(a, b), there exists positive integers s, t such
that d = s * a - t * b
-/

/-
The key to the solution to the question is the following trick:

s * a + t * b = (s + p * b) * a + (t - p * a) * b for any positive integer p.

Thus we can make the coefficients of a, b as positive/negative as we like.
-/

/-
First of all, a few helper lemmas are proven. The first two deal with the nuances of integer division
in Lean. The last two solve the bulk of the question, leaving only a small amount of work to be done 
in the actual question statment.
-/

lemma Int.sub_ediv_of_dvd_right {a b c : ℤ} (H : c ∣ b) : (a - b) / c = a / c - b / c := by
  simp only [sub_eq_add_neg, Int.add_ediv_of_dvd_right <| Int.dvd_neg.2 H, Int.neg_ediv_of_dvd H]

lemma Int.sub_lt_div_mul_self (a : ℤ) {b : ℤ} (hb : 0 < b) : a - b < a / b * b := by
  by_contra h
  push_neg at h
  have := Int.le_ediv_of_mul_le hb h
  rw [Int.sub_ediv_of_dvd_right <| dvd_rfl, Int.ediv_self hb.ne'] at this
  linarith

/- 
helper_1 says that given s * a + t * b = n, we can find new coefficients s', t' for a, b 
with 0 < s' so the same equality holds.
-/

lemma helper_1 (a b n : ℤ) (hb : 0 < b) (hab : ∃ (s t : ℤ), s * a + t * b = n) : 
    ∃ (s' t' : ℤ), 0 < s' ∧ s' * a + t' * b = n := by 
  rcases hab with ⟨s, t, hst⟩
  set p := (b - s) / b with hp
  use s + p * b, t - p * a
  constructor
  · rw [hp, ← neg_lt_iff_pos_add']
    calc
      -s = (b - s) - b := by simp
      _ < (b - s) / b * b := by exact Int.sub_lt_div_mul_self _ hb
  · linear_combination hst

/-
helper_2 builds on helper_1 but now adds the restriction that the new coefficient t' satisfies t' < 0.
This effectively solves the question, save for some changes of sign and the assumption that we can 
initially find any s, t such that s * a + t * b = gcd(a, b).
-/

lemma helper_2 (a b n : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : ∃ (s t : ℤ), s * a + t * b = n) : 
    ∃ (s' t' : ℤ), 0 < s' ∧ t' < 0 ∧ s' * a + t' * b = n := by 
    match helper_1 a b n hb hab with
    |⟨s, t, ⟨h1, h2⟩⟩ => 
    rcases lt_or_le t 0 with (ht | ht)
    · use s, t
    · set p := (t + a) / a with hp
      have hpos : 0 ≤ p := by 
        · rw [hp, Int.le_ediv_iff_mul_le ha, zero_mul]
          exact Int.add_nonneg ht ha.le
      use (s + p * b), (t - p * a)
      repeat (any_goals constructor)
      · exact add_pos_of_pos_of_nonneg h1 (Iff.mpr (zero_le_mul_right hb) hpos)
      · rw [sub_neg, hp]
        have := Int.sub_lt_div_mul_self (t + a) ha
        simpa
      · linear_combination h2 

/-
The final statment of the question consistient with that in the book. helper_2 states
the equality s' * a + t' * b = n with 0 < s' and t' < 0. 

However, we want s' * a - t' * b = n with 0 < s' and 0 < t'. These are of course equivalent,
and part_a deals with this. 
-/

lemma part_a (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : 
  ∃ (s t : ℤ), 0 < s ∧ 0 < t ∧ Int.gcd a b = s * a - t * b := by 
  have := helper_2 a b (Int.gcd a b) ha hb (by 
    use Int.gcdA a b, Int.gcdB a b
    simp [mul_comm, Int.gcd_eq_gcd_ab])
  match this with
  |⟨s, t, ⟨hs, ht, hst⟩⟩ => 
  use s, -t
  repeat (any_goals constructor)
  · assumption
  · exact Int.neg_pos_of_neg ht
  · rw [Int.neg_mul]
    simp [hst]

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