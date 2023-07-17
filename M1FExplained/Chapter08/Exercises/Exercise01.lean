import Mathlib.Tactic

namespace Chapter08.Exercise01

example (b : ℕ) (hb : 1 ≤ b) : ∃ c, b = c + 1 := by exact Nat.exists_eq_add_of_le' hb
/-
Prove by induction that it's possible to pay, without requiring
change, any whole number of roubles greater than 7 with
banknotes of value 3 roubles and 5 roubles
-/
example (n : ℕ) (hn : 7 < n) : ∃ a b : ℕ, n = 3 * a + 5 * b :=
  by
  -- Remark: this looks a little subtle to me, you will have
  -- to think about exactly what statement you want to prove
  -- by induction.
  generalize hd : n - 8 = d
  have hnd : n = d + 8 := Iff.mp (Nat.sub_eq_iff_eq_add hn) hd
  · rw [hnd]
    clear hnd hd hn n
    induction' d with k hk
    · use 1
      use 1
    · change ∃ a b, k + 1 + 8 = 3 * a + 5 * b
      rcases hk with ⟨a, b, hp⟩
      by_cases h : 0 < b
      · use a + 2
        use b - 1
        change k + 8 + 1 = _
        rw [hp]
        ring_nf
        change 1 ≤ b at h
        replace h := Nat.exists_eq_add_of_le' h
        rcases h with ⟨bb, rfl⟩  
        simp
        linarith
      · push_neg at h 
        simp only [nonpos_iff_eq_zero] at h 
        subst h
        norm_num at hp 
        have hk : 6 < k + 8 := by linarith
        rw [hp] at hk 
        have h3 : 0 < 3 := by simp
        have ha : 2 < a := (mul_lt_mul_left h3).mp hk
        refine' ⟨a - 3, 2, _⟩
        change k + 8 + 1 = 3 * (a - 3) + 10
        rw [hp]
        replace ha := Nat.exists_eq_add_of_lt ha
        rcases ha with ⟨k, hk⟩
        rw [add_comm 2 k] at hk
        subst hk
        simp   
        linarith

end Chapter08.Exercise01

