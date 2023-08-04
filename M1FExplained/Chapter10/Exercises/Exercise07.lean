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

lemma exercise07 : IsLeast {n : ℕ | 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} 84 := by 
  unfold IsLeast
  constructor
  · simp
  · rw [mem_lowerBounds]
    intros x hx
    simp at hx 
    by_contra h
    push_neg at h
    have h1 : x ∈ {n : ℕ | n < 84 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} := by exact Set.mem_sep h hx 
    have h2 : ∅ = {n : ℕ | n < 84 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n} := by sorry
    rw [←h2] at h1 
    contradiction
sorry

end Chapter10.Exercise07