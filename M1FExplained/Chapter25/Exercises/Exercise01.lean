import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Basic
def complex_size_1 :=
{ z : ℂ // ‖z‖  = 1 }

--- part i
noncomputable instance : Group complex_size_1 where
  mul a b:= ⟨a.1 * b.1, /- by rw [norm_mul, ] -/ sorry⟩
  mul_assoc := by 
    intro a b c
    
    sorry
  one := ⟨1,  by exact CstarRing.norm_one⟩
  one_mul := by
    intro a
    sorry
  mul_one := sorry
  inv z := ⟨z.1⁻¹,sorry⟩
  mul_left_inv := sorry

--- part ii
def real_not_minus_1 :=
{x : ℝ // x ≠ -1}

instance : Group (real_not_minus_1) where
  mul a b :=  ⟨a.1 * b.1 + a.1 + b.1, sorry⟩ 
  mul_assoc := sorry
  one := sorry
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


