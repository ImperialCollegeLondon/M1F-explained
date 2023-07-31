import Mathlib.Tactic


namespace Chapter10.Exercise05

lemma part_a (m n a : ℤ) (hmn : Int.gcd m n = 1) (hm : m ∣ a) (hn : n ∣ a) : (m * n) ∣ a := by 
  match hm with 
  |⟨k₁, hk₁⟩ => 
  match hn with 
  |⟨k₂, hk₂⟩ => 
  let r := Int.gcdA m n
  let s := Int.gcdB m n
  have h₁ : 1 = m * r + n * s := by rw [←Int.gcd_eq_gcd_ab m n, hmn]; norm_cast
  have h₂ : k₁ = k₁ * m * r + k₁ * n * s := by 
    calc
      k₁ = k₁ * 1 := by ring
      _ = k₁ * (m * r + n * s) := by rw [h₁]
      _ = k₁ * m * r + k₁ * n * s := by ring
  rw [mul_comm] at hk₁
  rw [←hk₁] at h₂
  rw [hk₂] at h₂
  have hc : n ∣ k₁  := by 
    use k₂ * r + k₁ * s
    ring_nf
    rw [mul_comm n k₁]
    exact h₂ 
  match hc with 
  |⟨e, he⟩ => 
  use e
  calc
    a = k₁ * m := by exact hk₁
    _ = (n * e) * m := by rw [he]
    _ = m * n * e := by ring

lemma helper_1 (m n M : ℤ) (hM : 1 < abs M) (hM' : M ∣ m * n) (hm : m ≠ 0) (hn : n ≠ 0) : abs (m * n / M)  < abs (m * n) := by
match hM' with 
|⟨k, hk⟩ => 
have hkn0 : 0 < abs k := by {
  rw [abs_pos]
  intro h
  rw [h] at hk
  simp at hk
  tauto
}
rw [hk, abs_mul, Int.mul_ediv_cancel_left]
·calc
  abs k = 1 * abs k := by norm_num
  _ < abs M * abs k := by rel [hM]
·intro h 
 have hM0 : abs M = 0 := by simp; exact h
 have : ¬ 1 < abs M := by rw [hM0]; norm_num
 contradiction

lemma helper_2 (m n : ℤ) (h1 : 0 < abs m) (h2 : abs m < abs n) : ¬ n ∣ m := by 
  have h1' : 0 < Int.natAbs m := by {
    rw [@Int.natAbs_pos]
    exact Iff.mp abs_pos h1
  }
  have h2' : Int.natAbs m < Int.natAbs n := by {
    rw [@Int.natAbs_lt_iff_sq_lt]
    exact Iff.mpr sq_lt_sq h2
  }
  have := @Nat.not_dvd_of_pos_of_lt _ _ h1' h2'
  simp at this
  assumption

-- QUESTION WRONG m, n ≠ 0 
lemma part_b (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (h2 : Int.gcd m n ≠ 1) : ∃ (a : ℤ), (m ∣ a) ∧ (n ∣ a) ∧ (¬(m * n) ∣ a) := by 
  let M : ℤ := Int.gcd m n
  use (m * n / M)
  apply And.intro
  ·rw [show m * n / M = m * (n / M) by {
    exact Int.mul_ediv_assoc m (show M ∣ n by exact Int.gcd_dvd_right m n)
  }]
   have : m ∣ m := by use 1; norm_num
   exact dvd_mul_of_dvd_left this (n / M)
  apply And.intro
  ·rw [show m * n / M = n * (m / M) by {
    rw [←mul_comm n m]
    exact Int.mul_ediv_assoc n (show M ∣ m by exact Int.gcd_dvd_left m n)
  }]
   have : n ∣ n := by use 1; norm_num
   exact dvd_mul_of_dvd_left this (m / M)
  have : M ∣ m := by exact Int.gcd_dvd_left m n
  have hMmn : M ∣ m * n := by {
    match this with
    |⟨k, hk⟩ => 
    use k * n
    rw [hk]
    rw [mul_assoc]}
  ·have h1' : 0 < abs (m * n / M) := by {
    rw [abs_pos]
    intro h
    have := Int.eq_zero_of_ediv_eq_zero hMmn h
    rw [mul_eq_zero] at this
    tauto
  }
   have h1M : 1 < abs M := by {
    apply by_contradiction
    intro h
    push_neg at h
    have := @Int.abs_le_one_iff M
    rw [this] at h
    apply Or.elim h
    ·intro hM0
     simp at hM0
     rw [Int.gcd_eq_zero_iff] at hM0
     tauto
    ·intro
     | Or.inl hone => simp at hone; contradiction
     | Or.inr hmone => 
     have : 0 < M := by {
      rw [@Int.ofNat_pos]
      exact Int.gcd_pos_of_ne_zero_left n hm
     }
     contradiction
   }
   have h2' : abs (m * n / M)  < abs (m * n) := by exact helper_1 m n M h1M hMmn hm hn
   exact helper_2 (m * n / M) (m * n) h1' h2'

lemma part_c (x y m : ℤ) (hx : Int.gcd x m = 1) (hy : Int.gcd y m = 1) : Int.gcd (x * y) m = 1 := by 
  let a := Int.gcdA x m
  let b := Int.gcdB x m
  let c := Int.gcdA y m
  let d := Int.gcdB y m
  have hxm : 1 = x * a + m * b := by rw [←Int.gcd_eq_gcd_ab x m, hx]; norm_cast
  have hym : 1 = y * c + m * d := by rw [←Int.gcd_eq_gcd_ab y m, hy]; norm_cast
  have h   : 1 = x * y * a * c + (x * a * d + b * y * c + m * b * d) * m := by
    calc 
      1 = 1 * 1 := by norm_num
      _ = (x * a + m * b) * (y * c + m * d) := by nth_rewrite 1 [hxm]; rw [hym]
      _ = x * a * y * c + x * a * m * d + m * b * y * c + m * b * m * d := by ring
      _ = x * y * a * c + (x * a * d + b * y * c + m * b * d) * m := by ring
  /- Need lemma saying that if ∃ s, t : a * s * b * t = 1, then gcd(a, b) = 1, this is Q4C -/
  sorry



end Chapter10.Exercise05