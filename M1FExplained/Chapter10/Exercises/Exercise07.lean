import Mathlib.Tactic


namespace Chapter10.Exercise07

/-
Jim plays chess every 3 days, and his friend Marmaduke eats spaghetti every 4 days.
One Sunday it happens that Jim plays chess and Marmaduke eats spaghetti. How long 
will it be before this again happens on a Sunday?
-/

/-
We can say that all three of these events happen on 'day 0'. The next day on which
all of these three things happen simultaneously will be 'day l' where l = lcm(3, 4, 7),
which is 84. Since Lean doesn't have an inbuilt 'lcm of three numbers', we can 
equivalently prove that 84 is the smallest element of the set of multiples of 3, 4 and 7. 
-/

lemma exercise07 : IsLeast {n : ℕ | n > 0 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} 84 := by 
  unfold IsLeast
  constructor
  · simp
  · rw [mem_lowerBounds]
    rintro x ⟨h0, h2, ⟨b, rfl⟩, h4⟩
    rw [Nat.Prime.dvd_mul Nat.prime_three] at h2
    norm_num at h2
    rcases h2 with ⟨k, rfl⟩
    rw [← mul_assoc] at h4
    rw [Nat.Prime.dvd_mul (by norm_num)] at h4
    norm_num at h4
    rcases h4 with ⟨r, rfl⟩ 
    calc
        4 * (3 * (7 * r)) = 84 * r := by ring
                        _ ≥ 84 * 1 := by gcongr; linarith

end Chapter10.Exercise07