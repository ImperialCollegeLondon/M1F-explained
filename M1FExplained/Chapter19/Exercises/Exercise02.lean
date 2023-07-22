import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Chapter19.Exercise02

/-
Q2. The functions f , g : ℝ → ℝ are defined as follows:
f(x) = 2x if 0 ≤ x ≤ 1, and f (x) = 1 otherwise;
g(x) = x^2 if 0 ≤ x ≤ 1, and g(x) = 0 otherwise.

Give formulae describing the functions `g ∘ f` and
`f ∘ g`. (Draw the graphs of these functions.)
-/
noncomputable section

def f (x : ℝ) :=
  if 0 ≤ x ∧ x ≤ 1 then 2 * x else 1

def g (x : ℝ) :=
  if 0 ≤ x ∧ x ≤ 1 then x ^ 2 else 0

example (x : ℝ) :
    (g ∘ f) x = if 0 ≤ x ∧ x ≤ 1 / 2 then 4 * x ^ 2 else if 1 / 2 < x ∧ x ≤ 1 then 0 else 1 :=
  by
  -- replace with formula for g ∘ f
  change g (f x) = _
  have foo : (0 : ℝ) < 2⁻¹ := by norm_num -- handy to have around 
  unfold f
  unfold g
  split_ifs
  · ring
  · linarith
  · simp_all 
  · exfalso
    rename_i h1 h2 h3
    apply h2
    constructor <;> linarith
  · rfl
  · simp_all
  · rename_i h1 h2 h3
    exfalso
    apply h1
    constructor <;> linarith
  · simp_all [-foo]
    linarith 
  . simp_all
  · simp_all
  · simp_all
  · simp_all   
  
example (x : ℝ) : (f ∘ g) x = if 0 ≤ x ∧ x ≤ 1 then 2 * x ^ 2 else 0 :=
  by
  change f (g x) = _
  unfold f
  unfold g
  split_ifs
  · rfl
  · rename_i h1 h2
    exfalso ; apply h2
    constructor <;> nlinarith
  · norm_num
  · aesop

end -- noncomputable
    
end Chapter19.Exercise02

