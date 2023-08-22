import Mathlib.Tactic

namespace Chapter10.Exercise09

/-
Let a, b be coprime positive integers. Prove that for any integer n there exists
integers s, t with s > 0 such that s * a + t * b = n.
-/

/-
The proof of this statment would be simple if it weren't for the restriction s > 0. 
Since a, b are coprime, we han find s', t' so that s' * a + t' * b = 1, multiplying 
through by n gives the result with s = n * s', although we don't know anything about 
its sign. 

However, we can alter the Bézout coeficients using a trick:

(s + p * b) * a + (t - p * a) * b = s * a + t * b = n, for any p ∈ ℤ 

This allows us to satisfy the s > 0 constraint.
-/

/-
First of all a couple of lemmas dealing with integer division are needed.
-/

lemma Int.sub_ediv_of_dvd_right {a b c : ℤ} (H : c ∣ b) : (a - b) / c = a / c - b / c := by
  simp only [sub_eq_add_neg, Int.add_ediv_of_dvd_right <| Int.dvd_neg.2 H, Int.neg_ediv_of_dvd H]

lemma Int.sub_lt_div_mul_self {a b : ℤ} (hb : 0 < b) : a - b < a / b * b := by
  by_contra h
  push_neg at h
  have := Int.le_ediv_of_mul_le hb h
  rw [Int.sub_ediv_of_dvd_right <| dvd_rfl, Int.ediv_self hb.ne'] at this
  linarith

/-
The helper implements the trick as described above.
-/

lemma helper (a b n : ℤ) (hb : 0 < b) (hab : ∃ (s t : ℤ), s * a + t * b = n) : 
    ∃ (s' t' : ℤ), 0 < s' ∧ s' * a + t' * b = n := by 
  rcases hab with ⟨s, t, hst⟩
  set p := (b - s) / b with hp
  use s + p * b, t - p * a
  constructor
  · rw [hp, ← neg_lt_iff_pos_add']
    calc
      -s = (b - s) - b := by simp
      _ < (b - s) / b * b := by exact Int.sub_lt_div_mul_self hb
  · linear_combination hst

/-
Next the actual question is proven, the restraint that a is positive
has been removed as it is not necessary.
-/

lemma exercise09 (a b : ℤ) (hb : b > 0) (hab : IsCoprime a b) : 
  ∀ (n : ℤ), ∃ (s t : ℤ), 0 < s ∧ s * a + t * b = n := by
  rcases hab with ⟨s', t', hst⟩
  intro n
  have hab : ∃ (s t : ℤ), s * a + t * b = n := by
    · use n * s', n * t'
      calc
        _ = n * (s' * a + t' * b) := by ring
        _ = n := by rw [hst]; simp
  exact helper a b n hb hab

end Chapter10.Exercise09