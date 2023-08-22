import Mathlib.Tactic

namespace Chapter10.Exercise08

/-
Let n ≥ 2 be an integer. Prove that n is prime if and only if for every integer a, 
either gcd(a, n) = 1 or n ∣ a. 
-/

lemma exercise08 (n : ℤ) (hn : 2 ≤ n) : Prime n ↔ ∀ (a : ℤ), Int.gcd a n = 1 ∨ n ∣ a := by
  -- Since 2 ≤ n, it is a natural number, we can rewrite this in the local context.
  rw [← Int.natAbs_of_nonneg (show 0 ≤ n by linarith)] at *
  -- N is the coercion on n to the natural numbers.
  set N := n.natAbs
  constructor 
  <;> intro h 
  <;> rw [← Nat.prime_iff_prime_int] at *
  -- → direction. 
  · intro a
  -- Condition on whether N divides |a|.
    apply Or.elim (Classical.em (N ∣ a.natAbs))
    <;> intro h'
  -- If N ∣ |a|, then trivially N ∣ a.
    · right
      exact Iff.mpr Int.ofNat_dvd_left h'
  -- If ¬ N ∣ |a|, then since N is prime, gcd(N, a) = 1. This is proven by contradiction.
    · left
      by_contra h''
      set M := Int.gcd a N with hM
  -- M = gcd(a, N) divides N, and so is equal to 1 or N, both of which are contradictions.
      have : M ≠ 0 := by 
        · intro hM'
          rw [hM'] at hM
          have := Eq.symm hM
          rw [Int.gcd_eq_zero_iff] at this
          linarith
      rw [Nat.prime_def_lt''] at h
      rcases h with ⟨h1, h2⟩
      specialize h2 M (show M ∣ N by 
        rw [Int.gcd_dvd_iff]
        use 0, 1
        ring)
      apply Or.elim h2
      <;> intro hM''
-- Can't have M = 1, since we assume this wasn't the case.
      · contradiction
-- If M = N, then N ∣ a, which we also assumed wasn't the case.
      · rw [hM''] at hM 
        apply absurd (show N ∣ Int.natAbs a by exact Iff.mpr Nat.gcd_eq_right_iff_dvd hM'') h'
  -- ← direction.
  -- A natural number is prime if and only if any number less than it and greater than 1 doesn't divide it.
  · rw [Nat.prime_def_lt']
    constructor
    · exact Iff.mp Int.ofNat_le hn
    · rintro m hm1 hm2
  -- Condition over the disjunction in our assumption.
      apply Or.elim (h m)
      <;> rintro hm3 ⟨k, hk⟩
      · rw [hk] at hm3
  -- gcd(a, c * d) = 1 → gcd(a, c) = 1.
        have := Int.gcd_eq_one_of_gcd_mul_right_eq_one_left hm3
        simp at this
        linarith
  -- If 0 < n and m ∣ n, then m ≤ n.
      · have := @Nat.le_of_dvd N m (show 0 < m by exact Nat.lt_of_succ_lt hm1) (show N ∣ m by exact Iff.mp Int.ofNat_dvd hm3)
        linarith

end Chapter10.Exercise08