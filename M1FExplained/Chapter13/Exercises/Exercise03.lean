import Mathbin.Data.Int.Modeq
import Mathbin.Data.Zmod.Algebra
import Mathbin.Tactic.Default

namespace Chapter13.Exercise03

/-
For each of the following congruence equations, either find a solution x ∈ ℤ or show that no solution exists:
(a) 99x ≡ 18 mod 30.
(b) 91x ≡ 84 mod 143.
(c) x^2 ≡ 2 mod 5.
(d) x^2 + x + 1 ≡ 0 mod 5.
(e) x^2 + x + 1 ≡ 0 mod 7.
-/
-- For the following parts, either provide a solution and proof that the solution solves the congruence,
-- or negate the statement of the lemma with ¬ and prove that no solution exists.
theorem part_a : ∃ x : ℤ, 99 * x ≡ 18 [ZMOD 30] :=
  by
  unfold Int.ModEq
  use 2
  norm_num

theorem part_b : ¬∃ x : ℤ, 91 * x ≡ 84 [ZMOD 143] :=
  by
  unfold Int.ModEq
  norm_num
  by_contra'
  cases' this with h h1
  have h2 : 13 * (7 * h) % (13 * 11) = 84 :=
    by
    convert h1 using 2
    ring
  · rw [Int.mul_emod_mul_of_pos] at h2 
    · have : (13 : ℤ) ∣ 84 := ⟨7 * h % 11, h2.symm⟩
      norm_num at this 
    · norm_num

theorem part_c : ¬∃ x : ℤ, x ^ 2 ≡ 2 [ZMOD 5] :=
  by
  unfold Int.ModEq
  norm_num
  by_contra'
  cases' this with h h1
  change h ^ 2 % (5 : ℕ) = 2 % (5 : ℕ) at h1 
  rw [← ZMod.int_cast_eq_int_cast_iff'] at h1 
  push_cast at h1 
  revert h1
  generalize (h : ZMod 5) = t
  decide!

theorem part_d : ¬∃ x : ℤ, x ^ 2 + x + 1 ≡ 0 [ZMOD 5] :=
  by
  unfold Int.ModEq
  by_contra'
  cases' this with h h1
  change (h ^ 2 + h + 1) % (5 : ℕ) = 0 % (5 : ℕ) at h1 
  rw [← ZMod.int_cast_eq_int_cast_iff'] at h1 
  push_cast at h1 
  revert h1
  generalize (h : ZMod 5) = t
  decide!

theorem part_e : ∃ x : ℤ, x ^ 2 + x + 1 ≡ 0 [ZMOD 7] :=
  by
  unfold Int.ModEq
  use 2
  norm_num

end Chapter13.Exercise03

