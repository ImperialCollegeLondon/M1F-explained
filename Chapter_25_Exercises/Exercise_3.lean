import Mathlib.Algebra.Group.Defs

--- part a

example {G : Type u_1} [Group G] (a : G) : (a⁻¹)⁻¹ = a := by
  rw [← mul_one (a⁻¹)⁻¹, ← mul_left_inv a, ← mul_assoc, mul_left_inv, one_mul]

--- part b

example {G : Type u_1} [Group G] (a b : G) : (a*b)⁻¹ = b⁻¹*a⁻¹ := by
  have h₁ : (a*b)*(b⁻¹*a⁻¹) = 1 := by
    rw [← mul_assoc, mul_assoc a, mul_right_inv, mul_one,mul_right_inv,]
  apply inv_eq_of_mul_eq_one_right
  exact h₁