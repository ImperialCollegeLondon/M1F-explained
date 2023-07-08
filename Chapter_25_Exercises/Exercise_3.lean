import Mathlib.Algebra.Group.Defs

/-
Let G be a group, and let a, b ∈ G. Prove that
  i) (a⁻¹)⁻¹ = a
  ii) (a * b)⁻¹ = b⁻¹ * a⁻¹
-/

--- part i)

example {G : Type u_1} [Group G] (a : G) : (a⁻¹)⁻¹ = a := by
  calc
    (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * a⁻¹*a := by
      rw [mul_assoc,mul_left_inv, mul_one]
    _ = a := by
      rw [mul_left_inv,one_mul]

--- part ii)

example {G : Type u_1} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h₁ : (a * b)*(b⁻¹ * a⁻¹) = 1 := by
    rw [← mul_assoc, mul_assoc a, mul_right_inv, mul_one,mul_right_inv]
  apply left_inv_eq_right_inv
  exact mul_left_inv (a * b)
  exact h₁