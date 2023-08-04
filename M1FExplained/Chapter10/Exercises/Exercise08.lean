import Mathlib.Tactic

namespace Chapter10.Exercise08

/-
Let n ≥ 2 be an integer. Prove that n is prime if and only if for every integer a, 
either gcd(a, n) = 1 or n ∣ a. 
-/

example (a n : ℤ) (hprime : Prime n) (ha :  a < n) : Int.gcd a n = 1 := by sorry

example (a n : ℤ) (hprime : Prime n) (ha : ¬n ∣ a) : Int.gcd a n = 1 := by sorry
#check Int.exists_prime_and_dvd

lemma exercise08 (n : ℤ) (hn : n ≥ 2) : Prime n ↔ ∀ (a : ℤ), Int.gcd a n = 1 ∨ n ∣ a := by 
  constructor
  · intros hprime a
    have := Classical.em (n ∣ a) 
    apply Or.elim this
    · intro; right; assumption 
    · intro; left; sorry
  · intro h
    constructor
    · intro; linarith
    constructor
    · rw [Int.isUnit_iff]
      intro h'; apply Or.elim h' <;> intro <;> linarith
    · intros a b hab
      apply Or.elim (h a)
      · intro h1
        apply Or.inr
        apply Or.elim (h b)
        · intro h2
          exfalso
          have h3 : Int.gcd (a * b) n = 1 := by sorry -- This is EX05 part c
          have h4 : Int.natAbs n  ∣ (Int.natAbs a * Int.natAbs b) := by {
            match hab with 
            | ⟨k, hk⟩ => 
            use Int.natAbs k
            calc 
              Int.natAbs a * Int.natAbs b = Int.natAbs (a * b) := by exact Eq.symm (Int.natAbs_mul a b)
              _ = Int.natAbs (n * k) := by rw [hk]
              _ = Int.natAbs n * Int.natAbs k := by exact Int.natAbs_mul n k
          }
          have h5 : Nat.gcd (Int.natAbs a * Int.natAbs b) (Int.natAbs n) = Int.natAbs n := by 
            exact Nat.gcd_eq_right h4
          rw [Int.gcd_eq_natAbs, Int.natAbs_mul] at h3
          rw [h3] at h5
          apply Or.elim (show n = 1 ∨ n = -1 by exact Iff.mp Int.natAbs_eq_natAbs_iff (id (Eq.symm h5)))
          <;> intro <;> linarith
        · tauto
      · tauto

end Chapter10.Exercise08