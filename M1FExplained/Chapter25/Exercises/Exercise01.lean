import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Basic
abbrev complex_size_1 :=
{ z : ℂ // ‖z‖  = 1 }

namespace complex_size_1

instance one : One complex_size_1 := ⟨1,  by exact CstarRing.norm_one⟩

@[simp]
lemma coe_one : (↑(1 : complex_size_1) : ℂ) = 1 := by rfl

lemma mul_closed (a b : complex_size_1) : ‖(a : ℂ) * b‖ = 1 := by
  rw [norm_mul, a.2,b.2,mul_one]

--- part i

instance : Mul complex_size_1 where mul a b:= ⟨a.1 * b.1, mul_closed a b⟩

@[simp]
lemma coe_mul (a b : complex_size_1) : (↑(a * b) : ℂ) = ↑a * ↑b := by
  rfl

lemma ne_zero (a : complex_size_1) : (a : ℂ) ≠ 0 := by
  intro h
  apply_fun norm at h
  rw [a.2, norm_zero,] at h
  norm_num at h

noncomputable instance : Group complex_size_1 where
  mul a b:= ⟨a.1 * b.1, mul_closed a b⟩
  mul_assoc := by 
    intro a b c
    ext1
    simp [mul_assoc]
  one := 1
  one_mul := by
    intro a
    ext1
    simp
  mul_one := by
    intro a
    ext1
    simp
  inv z := ⟨z.1⁻¹, by rw [norm_inv,z.2,inv_one]⟩
  mul_left_inv := by
    intro a
    ext1
    simp [inv_mul_cancel]
    rw [inv_mul_cancel]
    exact ne_zero a

--- part ii
abbrev real_not_minus_1 :=
{x : ℝ // x ≠ -1}

namespace real_not_minus_1

instance one : One real_not_minus_1 := ⟨1,  by norm_num⟩ 

lemma mul_closed2 (a b : real_not_minus_1) : (a : ℝ) * b + a + b ≠ -1 := by
  by_contra h
  sorry




instance : Group (real_not_minus_1) where
  mul a b :=  ⟨a.1 * b.1 + a.1 + b.1, mul_closed2 a b⟩ 
  mul_assoc := by
    intro a b c
    ext1
    sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry

-- part iv

def part_iv :=
{ x : ℝ // x ≥ 0}

noncomputable instance monoid_part_iv : AddMonoid part_iv where
  add a b:= ⟨max a.1 b.1,sorry⟩
  add_assoc := sorry
  zero := ⟨0,sorry ⟩
  zero_add := sorry
  add_zero := sorry

example (a b : part_iv): a+b ≠ 0 := sorry

--- part v

def part_v : Set ℂ :=
{z | z^3 - z^2 + z - 1 = 0}

example : ∃ a ∈  part_v, ∃ b ∈ part_v, ¬ a*b ∈ part_v := sorry

--- part vi

def part_vi :=
{z : ℂ  // z ≠ 0}

noncomputable instance semigroup_part_vi : Semigroup part_vi where
  mul a b := ⟨‖a.1‖*b.1,sorry⟩
  mul_assoc := sorry

example (a : sorry) : sorry := sorry


