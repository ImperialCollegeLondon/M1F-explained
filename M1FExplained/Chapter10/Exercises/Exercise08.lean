import Mathlib.Tactic

namespace Chapter10.Exercise08

/-
Let n ≥ 2 be an integer. Prove that n is prime if and only if for every integer a, 
either gcd(a, n) = 1 or n ∣ a. 
-/

#check Nat.prime_def_lt'
#check Nat.prime_def_lt
#check Nat.prime_dvd_prime_iff_eq
#check Nat.prime_def_le_sqrt
#check Nat.prime_def_lt''
#check Nat.prime_mul_iff
#check Nat.prime_def_minFac
#check Nat.prime

example (n : ℤ) (hn : 2 ≤ n) : n = n.natAbs := by 
  rw [Int.coe_natAbs]
  exact Eq.symm (abs_of_nonneg (show 0 ≤ n by linarith))


lemma exercise08' (n : ℤ) (hn : 2 ≤ n) : Prime n ↔ ∀ (a : ℤ), Int.gcd a n = 1 ∨ n ∣ a := by
  rw [show n = n.natAbs by 
      rw [Int.coe_natAbs] 
      exact Eq.symm (abs_of_nonneg (show 0 ≤ n by linarith))] at *
  set N := n.natAbs with rfl
  constructor 
  <;> intro h 
  <;> rw [← Nat.prime_iff_prime_int] at *
  · sorry
  · rw [Nat.prime_def_lt']
    constructor
    · exact Iff.mp Int.ofNat_le hn
    · rintro m hm1 hm2
      apply Or.elim (h m)
      <;> rintro hm3 ⟨k, hk⟩
      · rw [hk] at hm3
        have := Int.gcd_eq_one_of_gcd_mul_right_eq_one_left hm3
        simp at this
        linarith
      · have := @Nat.le_of_dvd N m (show 0 < m by exact Nat.lt_of_succ_lt hm1) (show N ∣ m by exact Iff.mp Int.ofNat_dvd hm3)
        linarith
      

sorry

end Chapter10.Exercise08