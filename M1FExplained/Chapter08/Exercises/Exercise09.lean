import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- for part d
-- for part d
namespace Chapter08.Exercise09

theorem exercise (n : ℕ) (q : ℝ) (hgq : 0 < q) (hlq : q < (1 / 2 : ℝ)) :
    (1 + q) ^ n ≤ 1 + (2 : ℝ) ^ n * q :=
  by
  induction' n with h hh; norm_num; exact le_of_lt hgq
  rw [Nat.succ_eq_add_one]
  by_cases hz : h ≥ 1
  swap
  rw [not_le, Nat.lt_one_iff] at hz 
  rw [hz]
  simp [pow_one, add_le_add_iff_left, two_mul, le_add_iff_nonneg_left]
  exact le_of_lt hgq
  rw [pow_succ, pow_succ]
  have p : (1 + q) * (1 + q) ^ h ≤ (1 + q) * (1 + 2 ^ h * q) :=
    by
    rwa [mul_le_mul_left]
    linarith
  apply le_trans p
  ring_nf
  rw [mul_two]
  --ring_nf
  simp only [add_assoc]; apply add_le_add_left
  rw [add_left_comm]; apply add_le_add_left
  sorry -- the rest of the port of this proof broke
  
  -- apply add_le_add
  -- · rw [mul_le_mul_right]
  --   · rw [add_comm, add_assoc]
  --     apply add_le_add
  --     rfl
  --     have t : 0 < (2 : ℝ) := by simp only [zero_lt_bit0, zero_lt_one]
  --     rw [← mul_le_mul_left t]
  --     ring_nf
  --     have s : 1 * (2 : ℝ) ^ h + 2 ≤ (2 : ℝ) * (2 : ℝ) ^ h :=
  --       by
  --       rw [two_mul]
  --       simp only [one_mul, add_le_add_iff_left]
  --       norm_cast
  --       nth_rw 1 [← pow_one 2]
  --       suffices 1 ≤ h by
  --         refine' pow_mono _ hz
  --         exact one_le_two
  --       exact hz
  --     have r : (2 : ℝ) * q * (2 : ℝ) ^ h + 2 ≤ 1 * (2 : ℝ) ^ h + 2
  --     rw [add_le_add_iff_right]
  --     · rw [mul_le_mul_right]
  --       · linarith
  --       exact pow_pos t h
  --     apply le_trans r s
  --   exact hgq
  -- rfl

end Chapter08.Exercise09

