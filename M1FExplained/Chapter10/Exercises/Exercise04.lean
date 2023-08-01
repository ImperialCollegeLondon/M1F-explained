import Mathlib.Tactic

namespace Chapter10.Exercise04

/- Solve part a by induction and use:

theorem int.mod_eq_mod_iff_mod_sub_eq_zero  {m n k : ℤ} :
m % n = k % n ↔ (m - k) % n = 0

for the n + 1 case.
-/


lemma part_a (n : ℕ) (hn : n > 0) : Nat.gcd (6 * n + 8) (4 * n + 5) = 1 := by 
  zify at *
  sorry
  /-
  induction n with
  | zero => norm_num
  | succ n ih => rw [Nat.succ_eq_add_one]; 

  -/

  /- have : 1 = 2 * (6 * n + 8) - 3 * (4 * n + 5) := by
    calc
      1 = 1 + 12 * n - 12 * n := by norm_num
      _ = 2 * 6 * n + 16 - 3 * 4 * n - 15 := by ring -/

lemma helper (m n : ℤ) (hmn : m * n = 1) : (m = 1) ∨ (m = -1) := by  
  have h_unit : IsUnit m := by apply Iff.mpr isUnit_iff_exists_inv; use n; exact hmn
  exact Int.isUnit_eq_one_or h_unit

lemma part_b (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ∣ b) (hba : b ∣ a) : a = b ∨ a = -b := by
  match hab with
  |⟨k₁, hk₁⟩ => 
  match hba with
  |⟨k₂, hk₂⟩ => 
  rw [hk₂] at hk₁
  have h₁ : 1 = k₂ * k₁ := by 
    calc
      1 = b / b := by exact Eq.symm (Int.ediv_self hb)
      _ = (b * k₂ * k₁) / b := by nth_rewrite 1 [hk₁]; rfl
      _ = k₂ * k₁ := by rw [Int.mul_assoc]; exact Int.mul_ediv_cancel_left (k₂ * k₁) hb
  have h₂ : k₂ = 1 ∨ k₂ = -1 := by exact helper k₂ k₁ (Eq.symm h₁)
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
  



end Chapter10.Exercise04