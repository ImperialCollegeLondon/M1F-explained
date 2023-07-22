import Mathlib.Tactic

namespace Chapter10.Exercise04

lemma helper (m n : ℤ) (hmn : m * n = 1) : (m = 1 ∧ n = 1) ∨ (m = -1 ∧ n = -1) := by sorry

lemma part_a (n : ℕ) (hn : n > 0) : Nat.gcd (6 * n + 8) (4 * n + 5) = 1 := by sorry

lemma part_b (a b : ℤ) (hab : a ∣ b) (hba : b ∣ a) : a = b ∨ a = -b := by sorry

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
  have : M = 1 := by sorry
  simp at this
  assumption





end Chapter10.Exercise04