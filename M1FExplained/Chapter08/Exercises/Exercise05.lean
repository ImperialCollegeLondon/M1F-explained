import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- for part d
-- for part d
namespace Chapter08.Exercise05

theorem part_a (n : ℕ) : (11 : ℤ) ∣ 5 ^ (2 * n) - 3 ^ n :=
  by
  induction' n with x hx
  · norm_num
  rw [Nat.succ_eq_add_one, mul_add, pow_add, mul_one]
  rw [pow_succ 3]
  cases' hx with m hm
  have q : (5 : ℤ) ^ 2 = (22 : ℤ) + (3 : ℤ); norm_num
  rw [q, mul_add]
  --nth_rw 3 [mul_comm]
  have _ :
    (3 : ℤ) * (5 : ℤ) ^ (2 * x) - (3 : ℤ) * (3 : ℤ) ^ x =
      (3 : ℤ) * ((5 : ℤ) ^ (2 * x) - (3 : ℤ) ^ x) :=
    by rw [mul_sub _]
  use (2 : ℤ) * (5 : ℤ) ^ (2 * x) + (3 : ℤ) * m
  linear_combination 3 * hm

-- let m be n-1 so 4n-1 becomes 4m+3
theorem part_b (m : ℕ) : 2 ^ (4 * m + 3) % 10 = 8 :=
  by
  induction' m with x hx
  norm_num
  rw [pow_add, pow_mul, pow_succ, ← pow_mul, mul_assoc, ← pow_add]
  rw [Nat.mul_mod, hx]
  norm_num

-- "positive" is not needed here
theorem part_c (n : ℕ) : 9 ∣ n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 :=
  by
  induction' n with x hx
  · norm_num
  repeat' rw [← Nat.add_one]
  have h : 9 ∣ 27 + 27 * x + 9 * x ^ 2 :=
    by
    use 3 + 3 * x + x ^ 2
    ring_nf
  have p := Nat.dvd_add h hx
  convert p using 1
  ring

-- also works for n=0
theorem part_d (n : ℕ) (x : ℝ) (hx : 2 ≤ x) : (n : ℝ) * x ≤ x ^ n :=
  by
  induction' n with h hh
  · norm_num
  by_cases hn : h = 0
  · subst hn 
    simp [show Nat.succ 0 = 1 from rfl]
  · rw [pow_succ, Nat.cast_succ, mul_comm]
    rw [mul_le_mul_left]
    have p : ↑h + 1 ≤ ↑h * x :=
      by
      have g : ↑h * 2 ≤ ↑h * x := by
        rwa [mul_le_mul_left]
        norm_cast
        exact pos_iff_ne_zero.mpr hn
      have q : ↑h + 1 ≤ ↑h * (2 : ℝ) := by
        norm_cast
        rw [mul_two]
        simp only [add_le_add_iff_left]
        exact Nat.one_le_iff_ne_zero.mpr hn
      exact le_trans q g
    apply le_trans p
    exact hh
    linarith

theorem part_e (n : ℕ) (hn : 3 ≤ n) : 4 ^ n + 3 ^ n + 2 ^ n < 5 ^ n := by
  induction' n with h hx
  norm_num at hn 
  repeat' rw [Nat.succ_eq_add_one, pow_succ]
  have p : 2 * 2 ^ h < 5 * 2 ^ h := by
    simp only [mul_lt_mul_right, pow_pos, Nat.succ_pos']
  have q : 3 * 3 ^ h < 5 * 3 ^ h := by
    simp only [mul_lt_mul_right, pow_pos, Nat.succ_pos']--, bit1_lt_bit1, Nat.one_lt_bit0_iff]
  have r : 4 * 4 ^ h < 5 * 4 ^ h := by
    simp only [mul_lt_mul_right, pow_pos, Nat.succ_pos']--, Nat.bit0_lt_bit1_iff]
  have t : 5 * 4 ^ h + 5 * 3 ^ h + 5 * 2 ^ h = 5 * (4 ^ h + 3 ^ h + 2 ^ h) := by ring_nf
  have s := add_lt_add (add_lt_add r q) p
  rw [t] at s 
  by_cases hh : h = 2;
  · rw [hh]
    norm_num
  · have hhh : 3 ≤ h := by
      obtain tt := Nat.of_le_succ hn
      have := Nat.succ_ne_succ.mpr hh
      norm_num at this 
      rcases tt with (tt | tt)
      · exact tt
      · exfalso
        replace tt := Nat.succ_injective tt
        exact this tt.symm
    rw [pow_succ 3, pow_succ 2]
    apply lt_trans s
    rw [pow_succ 5]
    rw [mul_lt_mul_left]
    · exact hx hhh
    norm_num

end Chapter08.Exercise05

