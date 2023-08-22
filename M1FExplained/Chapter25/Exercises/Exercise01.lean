import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Basic

abbrev complex_size_1 :=
{ z : ℂ // ‖z‖  = 1 }

instance one : One complex_size_1 := ⟨1, by exact CstarRing.norm_one⟩

@[simp]
lemma coe_one : (↑(1 : complex_size_1) : ℂ) = 1 := by rfl

lemma mul_closed (a b : complex_size_1) : ‖(a : ℂ) * b‖ = 1 := by
  rw [norm_mul, a.2, b.2, mul_one]

--- part i

instance : Mul complex_size_1 where mul a b:= ⟨a.1 * b.1, mul_closed a b⟩

@[simp]
lemma coe_mul (a b : complex_size_1) : (↑(a * b) : ℂ) = ↑a * ↑b := by
  rfl

lemma ne_zero (a : complex_size_1) : (a : ℂ) ≠ 0 := by
  intro h
  apply_fun norm at h
  rw [a.2, norm_zero] at h
  norm_num at h

noncomputable instance : Group complex_size_1 where
  mul a b := ⟨a.1 * b.1, mul_closed a b⟩
  mul_assoc a b c := by 
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
  inv z := ⟨z.1⁻¹, by rw [norm_inv, z.2, inv_one]⟩
  mul_left_inv := by
    intro a
    ext1
    simp [inv_mul_cancel]
    rw [inv_mul_cancel]
    exact ne_zero a

--- part ii
abbrev real_not_minus_1 :=
{x : ℝ // x ≠ -1}

instance zero : Zero real_not_minus_1 := ⟨0, by norm_num⟩ 

lemma add_closed2 (a b : real_not_minus_1) : (a : ℝ) * b + a + b ≠ -1 := by
  by_contra h
  have h₁ : (a.1 + 1) * (b.1 + 1) = 0 :=
    calc
      (a.1 + 1) * (b.1 + 1) = a.1 * b.1 + a.1 + b.1 + 1 := by ring
      _ = 0 := by
        rw [h]
        norm_num
  have h₂ : a.1 + 1 = 0 ∨ b.1 + 1 = 0 := Iff.mp zero_eq_mul (id (Eq.symm h₁))
  have h₃ : a.1 = -1 ∨ b.1 = -1 := by 
    rcases h₂ with (h | h₁)
    left
    rwa [← add_eq_zero_iff_eq_neg]
    right
    exact Iff.mp add_eq_zero_iff_eq_neg h₁
  unfold real_not_minus_1 at a b
  rcases h₃ with (h₄|h₅)
  have := a.2
  exact this h₄
  have := b.2
  exact this h₅

@[simp,norm_cast]
lemma coe_zero : ((0 : real_not_minus_1) : ℝ) = 0 := by rfl 

instance : Add real_not_minus_1 where
  add a b :=  ⟨a.1 * b.1 + a.1 + b.1, add_closed2 a b⟩

@[norm_cast]
lemma rnm1_coe_add (a b : real_not_minus_1) : (a + b : real_not_minus_1) = (a : ℝ) * b + a + b := by rfl

lemma add_assoc2 (a b c : real_not_minus_1) : a + b + c = a + (b + c) := by
  ext
  push_cast
  ring

lemma neg_real_neq_one (a : real_not_minus_1) : -a.1 / (a.1 + 1) ≠ -1 := by
  intro h
  simp at h
  have : a.1 + 1 ≠ 0 := by
    have := a.2
    intro h₀
    apply this
    exact Iff.mp add_eq_zero_iff_eq_neg h₀
  have h₁ : a.1 / (a.1 + 1) = 1  := by
    calc
      a.1 / (a.1 + 1) = -(-a.1 / (a.1 + 1)) := by ring
      _ = -(-1) := by rw [h]
    ring
  have h₂ : a.1 = a.1 + 1 := by
    calc
      a.1 = a.1 / (a.1 + 1) * (a.1 + 1) := Iff.mp (div_eq_iff this) rfl
      _ = a.1 + 1 := by
        rw [h₁]
        ring
  simp at h₂

noncomputable instance : Neg real_not_minus_1 where
  neg a := ⟨-a / (a + 1), neg_real_neq_one a⟩

@[norm_cast]
lemma coe_neg (a : real_not_minus_1) : (-a : real_not_minus_1) = -(a : ℝ) / (a + 1) := by rfl

noncomputable instance : AddGroup real_not_minus_1 where
  add_assoc := add_assoc2
  zero_add := by
    intro a
    ext
    push_cast
    norm_num
  add_zero := by
    intro a
    ext
    push_cast
    norm_num
  add_left_neg := by
    intro a
    unfold real_not_minus_1
    ext
    push_cast
    calc
      _ = -a.1 / (a.1 + 1) * a.1 + -a.1 / (a.1 + 1) + (a.1 * (a.1 + 1)) / (a.1 + 1) := by
        simp only [ne_eq, add_right_inj]
        have : a.1 + 1 ≠ 0 := by
          have := a.2
          intro h₀
          apply this
          exact Iff.mp add_eq_zero_iff_eq_neg h₀
        exact Iff.mpr (eq_div_iff this) rfl
      _ = 0 := by ring

-- part iv

abbrev part_iv :=
{ x : ℝ // x ≥ 0}


instance zero_part_iv : Zero part_iv := ⟨0,  by norm_num⟩ 

lemma add_close_part_iv (a b : part_iv) : max a.1 b.1 ≥ 0 := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  simp
  exact Or.inr hb

noncomputable instance add_part_iv : Add part_iv where
  add a b:= ⟨max a.1 b.1, add_close_part_iv a b⟩

@[simp]
lemma add_part_iv_coe (a b : part_iv): (a + b : part_iv) = max (a : ℝ) b := by rfl 

example (a b : part_iv) (h : a.1 > 0): a.1 + b.1 ≠ 0 := by
  intro h₀
  norm_cast at h₀
  simp only [NNReal.val_eq_coe, NNReal.coe_eq_zero, add_eq_zero_iff] at h₀ 
  rcases h₀ with ⟨ha⟩
  have : a ≠ 0 := ne_of_gt h
  exact this ha

--- part v

def part_v : Set ℂ :=
{z | z^3 - z^2 + z - 1 = 0}

example : ∃ a ∈  part_v, ∃ b ∈ part_v, ¬ a * b ∈ part_v := by
  sorry

--- part vi

def part_vi :=
{z : ℂ  // z ≠ 0}

noncomputable instance semigroup_part_vi : Semigroup part_vi where
  mul a b := ⟨‖a.1‖ * b.1,sorry⟩
  mul_assoc := sorry

example (a : sorry) : sorry := sorry


