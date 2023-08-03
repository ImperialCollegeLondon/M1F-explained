import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Nat.Basic

/-
(a) Let G be a group with the property that (ab)^2 = a^2b^2 for all a, b ∈ G. Prove that G is abelian.
(b) Let G be a group with the property that (ab)^i = a^ib^i ∀a, b ∈ G for three consecutive values of i.
  Prove that G is abelian.
(c) Show that the conclusion of part (b) does not follow if we only assume that (ab)^i = a^ib^i
  for two consecutive values of i.
-/



---part a

example {G : Type u_1} [Group G] : (∀ (a b : G), (a*b)^2 = a^2*b^2) → ∀ ( x y : G), y*x = x*y := by
  intro h₀ x y
  have h₁ : (x * y)^2 = x^2 * y^2 := by apply h₀ x y
  rwa [sq,sq,sq,mul_assoc, mul_assoc,mul_left_cancel_iff,← mul_assoc, ← mul_assoc, 
    mul_right_cancel_iff] at h₁

--- part b

example {G : Type u_1} [Group G] (i : ℕ) : 
    (∀ a b : G, (a*b)^i = a^i*b^i ∧ 
                (a*b)^(i + 1) = a^(i + 1)*b^(i + 1) ∧ 
                (a*b)^(i + 2) = a^(i + 2)*b^(i + 2)) → 
    ∀ a b : G, a*b = b*a := by
  intro h a b
  specialize h a b
  rcases h with ⟨h₀,h₁⟩
  rcases h₁ with ⟨h₁,h₂⟩
  have : i + 2 = i + 1 + 1 := by simp
  rw [this,pow_add,h₁, pow_one,mul_assoc,pow_add a (i+1),pow_add b (i+1),← mul_assoc,← mul_assoc,← mul_assoc,
  pow_one,pow_one, mul_right_cancel_iff,] at h₂
  nth_rw 1 [add_comm, pow_add,pow_add,← mul_assoc,mul_assoc (a ^ 1) (a ^ i) (b ^ i),← h₀,add_comm,pow_add,
  mul_assoc,mul_assoc,mul_assoc,mul_assoc,mul_left_cancel_iff,] at h₂
  nth_rw 1 [← mul_assoc,← mul_assoc,] at h₂
  nth_rw 4 [← pow_one a,] at h₂
  rw [← pow_add,← h₁, pow_add,mul_assoc,mul_left_cancel_iff,pow_one,pow_one] at h₂
  rw [h₂]


--- part c

example {G : Type u_1} [Group G] : ¬ (∀ i : ℕ, ∀ a b : G, (a*b)^i = a^i*b^i ∧ (a*b)^(i + 1) = a^(i + 1)*b^(i + 1)
    → a*b = b*a) := by
  sorry


