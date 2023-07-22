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

lemma part_b (m n : ℤ) (hmn : Int.gcd m n ≠ 1) : ∃ (a : ℤ), (m ∣ a) ∧ (n ∣ a) ∧ (¬(m * n) ∣ a) := by sorry
  

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