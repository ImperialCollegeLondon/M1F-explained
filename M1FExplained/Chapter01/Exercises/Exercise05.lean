import Mathbin.Tactic.Default

namespace Chapter01.Exercise05

-- True or false? n = 3 ↔ n^2-2n-3=0. If you think it's false
-- then you'll have to modify the statement by putting it in brackets
-- and adding a ¬ in front of it.
theorem part_a : ∀ n : ℤ, n = 3 → n ^ 2 - 2 * n - 3 = 0 := by norm_num

theorem part_b : ¬∀ n : ℤ, n ^ 2 - 2 * n - 3 = 0 → n = 3 :=
  by
  intro h
  specialize h (-1)
  norm_num at h 

theorem part_c : ¬∀ n : ℤ, n ^ 2 - 2 * n - 3 = 0 → n = 3 :=
  by
  intro h
  specialize h (-1)
  norm_num at h 

theorem part_d : ¬∀ a b : ℤ, IsSquare (a * b) → IsSquare a ∧ IsSquare b :=
  by
  intro h
  specialize h (-1) (-1)
  norm_num at h 
  unfold IsSquare at h 
  cases' h with m hm
  nlinarith

theorem part_e : ∀ a b : ℤ, IsSquare a ∧ IsSquare b → IsSquare (a * b) :=
  by
  intro a b h
  unfold IsSquare at h 
  rcases h with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  unfold IsSquare
  use x * y
  rw [hx]
  rw [hy]
  ring

end Chapter01.Exercise05

