import Mathlib.Tactic

namespace Chapter10.Exercise04

-- part a

/-
Show that for all positive integers n, gcd(6 * n + 8, 4 * n + 5) = 1
-/

lemma part_a (n : ℕ) (hn : n > 0) : Nat.gcd (6 * n + 8) (4 * n + 5) = 1 := by 
  -- Generalise to the integers with `zify`.
  zify at *
  have h₁ : 6 * ↑n + 8 = Int.natAbs (6 * ↑n + 8) := by rfl
  have h₂ : 4 * ↑n + 5 = Int.natAbs (4 * ↑n + 5) := by rfl
  rw [h₁, h₂, ←Int.gcd_eq_natAbs, Nat.cast_eq_one]
  /-Use the fact that gcd(a, b) = 1 ↔ ∃ s, t, s * a + t * b = 1.
  We prove this without using `Int.gcd_eq_one_iff_coprime` in part c.-/
  refine Iff.mpr Int.gcd_eq_one_iff_coprime ?_
  use 2
  use -3
  simp
  rw [@add_neg_eq_iff_eq_add]
  ring

-- part b

/-
Suppose that a, b are integers such that a ∣ b and b ∣ a. Prove that a = ±b. 
-/

/-
Whilst in Lean division by zero is defined, it doesn't make sense for 
us to consider any pair (a, b) where either is zero, since we traditionaly 
don't have a way of defining things like `17 / 0` , `0 / 0` etc.

For this reason, I have stated that both `a ≠ 0` and `b ≠ 0`, though we could equivalently 
state just one of these assumptions and deduce the other based on the fact that `a ∣ b` and `b ∣ a`
with the following (choosing `a ≠ 0` WLOG):
-/

example (a b : ℤ) (ha : a ≠ 0) (hab : a ∣ b) (hba : b ∣ a) : b ≠ 0 := by
  intro h
  rw [h] at hba
  simp_all

/-
Now for the actual question. First a helper lemma is proven which is relevant for both 
part b and part c.
-/

lemma helper (m n : ℤ) (hmn : m * n = 1) : (m = 1) ∨ (m = -1) := by  
  have h_unit : IsUnit m := by apply Iff.mpr isUnit_iff_exists_inv; use n; exact hmn
  exact Int.isUnit_eq_one_or h_unit

/-
Statment of the quesiton, by above we assume `a ≠ 0` and `b ≠ 0`, but really only one is needed.
-/

lemma part_b (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ∣ b) (hba : b ∣ a) : a = b ∨ a = -b := by
  match hab with
  |⟨k₁, hk₁⟩ => 
  match hba with
  |⟨k₂, hk₂⟩ => 
  rw [hk₂] at hk₁
  -- If `b = a * k₁` and `a = b * k₂`, then it must be that `k₁ * k₂  = 1`.
  have h₁ : 1 = k₂ * k₁ := by 
    calc
      1 = b / b := by rw [Int.ediv_self hb]
      _ = (b * k₂ * k₁) / b := by nth_rewrite 1 [hk₁]; rfl
      _ = k₂ * k₁ := by rw [Int.mul_assoc]; exact Int.mul_ediv_cancel_left (k₂ * k₁) hb
  -- The helper tells us that `k₂ = ±1`. The same of course holds for k₁. 
  have h₂ : k₂ = 1 ∨ k₂ = -1 := by exact helper k₂ k₁ (Eq.symm h₁)
  -- After rewriting this into our assumptions, the statment can be proven.
  apply Or.elim h₂
  ·intro h
   apply Or.inl
   rw [h] at hk₂
   simp at hk₂
   assumption
  ·intro h
   apply Or.inr
   rw [h] at hk₂
   simp at hk₂
   assumption

-- part c

/-
Suppose that s, t, a, b are integers such that s * a + t * b = 1. Show that gcd(a, b) = 1.
-/

/-
This is the reverse implication of `Int.gcd_eq_one_iff_coprime` which we used earlier in part a.
Here it is proven without using this lemma. Provided afterwars is an alternate proof using the lemma.
-/

lemma part_c (s t a b : ℤ) (h : s * a + t * b = 1) : Int.gcd a b = 1 := by 
  let M : ℤ := Int.gcd a b
  have h₁ : M ∣ a := by exact gcd_dvd_left a b
  have h₂ : M ∣ b := by exact gcd_dvd_right a b
  match h₁ with
  |⟨k₁, hk₁⟩ =>
  match h₂ with
  |⟨k₂, hk₂⟩ =>
  rw [hk₁, hk₂] at h
  have hM : M ∣ 1 := by
    use s * k₁ + t * k₂ 
    apply Eq.symm
    calc
      M * (s * k₁ + t * k₂) = s * (M * k₁) + t * (M * k₂) := by ring
      _ = 1 := by exact h
  have : M = 1 := by {
    match hM with
    |⟨e, he⟩ => 
    have : M = 1 ∨ M = -1 := by exact helper M e (Eq.symm he)
    apply Or.elim this
    ·simp
    ·intro h
     exfalso
     have : M ≥ 0 := by exact Int.ofNat_nonneg (Int.gcd a b)
     contradiction
  }
  simp at this
  assumption

/-
Here is an alternate, much simpler proof of part c using `Int.gcd_eq_one_iff_coprime`.
-/

lemma part_c' (s t a b : ℤ) (h : s * a + t * b = 1) : Int.gcd a b = 1 := by
  have : IsCoprime a b := by use s; use t; assumption
  exact Iff.mpr Int.gcd_eq_one_iff_coprime this 

end Chapter10.Exercise04