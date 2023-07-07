/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Natasha Johnson

! This file was ported from Lean 3 source module chapter02.exercises.exercise03
-/
import Mathbin.Tactic.Default
import Mathbin.Data.Real.Irrational

namespace Chapter02.Exercise03

def Rational (x : ℝ) :=
  ∃ a b : ℤ, x = a / b

/-- The product of two rational numbers is always rational. -/
theorem part_a : ∀ {a b : ℝ}, Rational a → Rational b → Rational (a * b) :=
  by
  rintro a b ⟨x1, y1, rfl⟩ ⟨x2, y2, rfl⟩
  use x1 * x2, y1 * y2
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The product of two irrational numbers is not always irrational. -/
theorem part_b : ¬∀ {a b : ℝ}, Irrational a → Irrational b → Irrational (a * b) :=
  by
  push_neg
  refine' ⟨Real.sqrt 2, Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, _⟩
  rw [irrational_iff_ne_rational]
  push_neg
  use 2, 1
  norm_num

/-- The product of two irrational numbers is not always rational. -/
theorem part_c : ¬∀ {a b : ℝ}, Irrational a → Irrational b → Rational (a * b) := by sorry

/-- The product of a non-zero rational and an irrational is always irrational. -/
theorem part_d : ∀ {a b : ℝ}, a ≠ 0 → Rational a → Irrational b → Irrational (a * b) := by sorry

end Chapter02.Exercise03

