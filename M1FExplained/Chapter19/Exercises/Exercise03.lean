import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Chapter19.Exercise03

/-
Two functions f, g : ℝ → ℝ are such that for all x ∈ ℝ,
g(x) = x² + x + 3, and (g ∘ f)(x) = x² − 3x + 5.
Find the possibilities for f .
-/
def g : ℝ → ℝ := fun x => x ^ 2 + x + 3

-- Edit the "∀ x, f x = 37" part of the claim below and replace it with your answer
example (f : ℝ → ℝ) : (g ∘ f = fun x => x ^ 2 - 3 * x + 5) ↔ ∀ x, f x = x - 2 ∨ f x = -x + 1 :=
  by
  simp [Function.funext_iff, g]
  apply forall_congr'
  intro x
  have h' : f x ^ 2 + f x + 3 = x ^ 2 - 3 * x + 5 ↔ (f x - (x - 2)) * (f x - (-x + 1)) = 0 := by
    constructor <;> intro h <;> nlinarith
  rw [h', mul_eq_zero]
  congr 2
  simp [sub_eq_zero]

end Chapter19.Exercise03

