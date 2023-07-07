/-
6. (a) Find an onto function from ℕ to ℤ.
(b) Find a 1-1 function from ℤ to ℕ.

! This file was ported from Lean 3 source module chapter19.exercises.exercise06
-/
import Mathbin.Tactic.Default
import Mathbin.Data.Nat.Parity

namespace Chapter19.Exercise06

open Function

def f (n : ℕ) : ℤ :=
  if 2 ∣ n then n / 2 else -(n + 1) / 2

-- replace 37 with a surjective function
theorem f_surj : Surjective f := by
  intro z
  rcases lt_trichotomy z 0 with (h1 | rfl | h3)
  · use (-2 * z - 1).natAbs
    unfold f
    split_ifs
    · exfalso
      rw [int.coe_nat_dvd_left.symm] at h 
      simp only [Int.ofNat_bit0, Nat.cast_one, neg_mul] at h 
      rw [show -(2 * z) - 1 = 2 * (-z - 1) + 1 by ring] at h 
      rw [dvd_add_right] at h 
      norm_num at h 
      apply dvd_mul_right
    · apply Int.ediv_eq_of_eq_mul_left
      norm_num
      rw [Int.natAbs_of_nonneg (show -2 * z - 1 ≥ 0 by linarith)]
      ring
  · use 0
    unfold f
    split_ifs
    simp [Int.zero_div]
    exfalso
    norm_num at h 
  · use (2 * z).natAbs
    unfold f
    split_ifs
    · apply Int.ediv_eq_of_eq_mul_left
      norm_num
      rw [Int.natAbs_of_nonneg (show 2 * z ≥ 0 by linarith)]
      ring
    exfalso
    apply h
    rw [← Int.coe_nat_dvd_left]
    norm_num

def g (z : ℤ) : ℕ :=
  if 0 < z then 2 * z.natAbs else 2 * z.natAbs + 1

-- replace 37 with an injective function
theorem g_inj : Injective g := by
  intro a b hab
  rcases Nat.even_or_odd (g a) with (h1 | h2)
  · have ha : 0 < a := by
      by_contra
      push_neg at h 
      unfold g at h1 
      rw [if_neg h.not_lt, even_iff_two_dvd, Nat.dvd_add_right] at h1 
      norm_num at h1 
      apply dvd_mul_right
    have hgb : Even (g b) := by rw [← hab]; exact h1
    have hb : 0 < b := by
      by_contra
      push_neg at h 
      unfold g at hgb 
      rw [if_neg h.not_lt, even_iff_two_dvd, Nat.dvd_add_right] at hgb 
      norm_num at hgb 
      apply dvd_mul_right
    unfold g at hab 
    simp only [if_pos ha, if_pos hb, mul_eq_mul_left_iff, bit0_eq_zero, Nat.one_ne_zero,
      or_false_iff] at hab 
    zify at hab 
    rwa [abs_of_nonneg ha.le, abs_of_nonneg hb.le] at hab 
  · have ha : a ≤ 0 := by
      by_contra
      push_neg at h 
      unfold g at h2 
      rw [if_pos h, Nat.odd_iff_not_even] at h2 
      apply h2
      rw [even_iff_two_dvd]
      apply dvd_mul_right
    have hgb : Odd (g b) := by rw [← hab]; exact h2
    have hb : b ≤ 0 := by
      by_contra
      push_neg at h 
      unfold g at hgb 
      rw [if_pos h, Nat.odd_iff_not_even] at hgb 
      apply hgb
      rw [even_iff_two_dvd]
      apply dvd_mul_right
    unfold g at hab 
    simp only [if_neg ha.not_lt, if_neg hb.not_lt, add_left_inj, mul_eq_mul_left_iff, bit0_eq_zero,
      Nat.one_ne_zero, or_false_iff] at hab 
    zify at hab 
    simpa [abs_of_nonpos ha, abs_of_nonpos hb] using hab

end Chapter19.Exercise06

