import Mathlib.Tactic


namespace Chapter10.Exercise07

/-
Jim plays chess every 3 days, and his friend Marmaduke ats spaghetti every 4 days.
One Sunday it happens that Jim plays chess and Marmaduke eats spaghetti. How long 
will it be before this again happens on a Sunday?
-/

/-
We can say that all three of these events happen on 'day 0'. The next day on which
all of these three things happen simultaneously will be 'day l' where l = lcm(3, 4, 7).
-/

lemma exercise07 : IsLeast {n : ℕ | n > 0 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} 84 := by 
  unfold IsLeast
  constructor
  · simp
  · rw [mem_lowerBounds]
    intros x hx
    by_contra h
    push_neg at h
    have h'' : x ∈ {n : ℕ | n > 0 ∧ n < 84 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} := by sorry
    have h' : ∅ = {n : ℕ | n > 0 ∧ n < 84 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} := by 
      rw [@Set.ext_iff]
      intro y
      constructor
      · intro; exfalso; assumption
      · intro 
        | ⟨h0, h1, h2, h3, h4⟩ => 
        match h2, h3, h4 with
        | ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩ => 
        have hb' : 3 ∣ 4 * b := by rwa [hb] at h2
        obtain ⟨k, hk⟩ : 3 ∣ b := by 
          · have : Prime 3 := by rw [← @Nat.prime_iff]; exact Nat.prime_three
            apply Or.elim (this.right.right 4 b hb')
            · intro; simp at *
            · tauto
        rw [hk]at hb
        have hk' : 7 ∣ 12 * k := by rwa [hb, show (4 * (3 * k) = 12 * k) by ring] at h4
        obtain ⟨r, hr⟩ : 7 ∣ k := by 
          · have : Prime 7 := by rw [← @Nat.prime_iff]; exact Iff.mpr (Nat.prime_iff_card_units 7) rfl
            apply Or.elim (this.right.right 12 k hk')
            · intro; simp at *
            · tauto 
        rw [hr] at hb
        have : y ≥ 84 := by
          calc
            y = 4 * (3 * (7 * r)) := by exact hb
            _ = 84 * r := by ring
            _ ≥ 84 * 1 := by gcongr; linarith
        apply absurd this (show ¬y ≥ 84 by rw [@Nat.not_le]; assumption)
    rw [←h'] at h''
    contradiction

end Chapter10.Exercise07