/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yuchen Wang

! This file was ported from Lean 3 source module chapter22.exercise01
-/
import Mathbin.Data.Real.Basic
import Mathbin.Analysis.Normed.Field.UnitBall
import Mathbin.Data.Real.Sqrt

namespace Chapter22.Exercise01

open scoped Topology BigOperators NNReal ENNReal uniformity Pointwise

/-
Which of the following sets S have an upper bound and which have a
lower bound? In the cases where these exist, state what the least upper
bounds and greatest lower bounds are.
(i) S = {-1, 3, 7, -2}.
(ii) S = {x | x ∈ ℝ and |x - 3| < |x + 7|}.
(iii) S = {x | x ∈ ℝ and  x³ - 3x < 0}.
(iv) S = {x | x ∈ ℝ and x² = a² + b² for some a, b ∈ ℕ}.
-/
def si : Set ℝ :=
  {-1, 3, 7, -2}

-- Si is bounded above.
theorem part_a_ub : ∃ z : ℝ, z ∈ upperBounds si :=
  by
  use 7
  rw [upperBounds]
  intro t
  intro h
  cases h
  · rw [h]
    norm_num
  cases h
  · rw [h]
    norm_num
  cases h
  · rw [h]
  simp at h 
  rw [h]
  norm_num

-- 7 is the least upper bound.
theorem part_a_lub : IsLUB si 7 := by
  rw [IsLUB, IsLeast]
  constructor
  · rw [upperBounds]
    intro t
    intro h
    cases h
    · rw [h]
      norm_num
    cases h
    · rw [h]
      norm_num
    cases h
    · rw [h]
    simp at h 
    rw [h]
    norm_num
  rw [lowerBounds]
  intro n
  intro h
  rw [upperBounds] at h 
  simp at h 
  apply h
  unfold Si
  simp

-- Si is bounded below.
theorem part_a_lb : ∃ z : ℝ, z ∈ lowerBounds si :=
  by
  use -2
  rw [lowerBounds]
  intro t
  intro h
  cases h
  · rw [h]
    norm_num
  cases h
  · rw [h]
    norm_num
  cases h
  · rw [h]
    norm_num
  simp at h 
  rw [h]

-- -2 is the greatest lower bound.
theorem part_a_glb : IsGLB si (-2) := by
  rw [IsGLB, IsGreatest]
  constructor
  · rw [lowerBounds]
    intro t
    intro h
    cases h
    · rw [h]
      norm_num
    cases h
    · rw [h]
      norm_num
    cases h
    · rw [h]
      norm_num
    simp at h 
    rw [h]
  rw [upperBounds]
  intro n
  intro h
  rw [lowerBounds] at h 
  simp at h 
  apply h
  unfold Si
  simp

def sii : Set ℝ :=
  {x | ‖x - 3‖ < ‖x + 7‖}

-- Sii is not bounded above.
theorem part_b_ub : ¬∃ z : ℝ, z ∈ upperBounds sii :=
  by
  rw [not_exists]
  intro n
  rw [upperBounds]
  simp
  by_cases h : n ≤ 3
  · use 4
    constructor
    · unfold Sii
      simp
      norm_num
      rw [abs_of_pos]
      · norm_num
      · norm_num
    · linarith
  use n + 1
  constructor
  · unfold Sii
    simp
    rw [abs_of_pos]
    · rw [abs_of_pos]
      · linarith
      · linarith
    · linarith
  linarith

-- if you proved there was an upper bound, then change 37 to the 
-- right answer and prove it's a least upper bound!
-- etc etc
-- Si is bounded below.
theorem part_b_lb : ∃ z : ℝ, z ∈ lowerBounds sii :=
  by
  use -2
  rw [lowerBounds]
  simp
  intro t
  intro h
  unfold Sii at h 
  simp at h 
  by_cases h1 : t < -7
  rw [abs_of_neg] at h 
  rw [abs_of_neg] at h 
  linarith
  linarith
  linarith
  by_cases h2 : t ≥ 3
  linarith
  rw [abs_of_neg] at h 
  rw [abs_of_nonneg] at h 
  linarith
  push_neg at h1 
  linarith
  linarith

-- -2 is the greatest lower bound.
theorem part_b_glb : IsGLB sii (-2) := by
  rw [IsGLB]
  rw [IsGreatest]
  constructor
  rw [lowerBounds]
  simp
  intro t
  intro h
  unfold Sii at h 
  simp at h 
  by_cases h1 : t < -7
  rw [abs_of_neg] at h 
  rw [abs_of_neg] at h 
  linarith
  linarith
  linarith
  by_cases h2 : t ≥ 3
  linarith
  rw [abs_of_neg] at h 
  rw [abs_of_nonneg] at h 
  linarith
  push_neg at h1 
  linarith
  linarith
  rw [upperBounds]
  simp
  intro n
  intro h
  rw [lowerBounds] at h 
  simp at h 
  unfold Sii at h 
  by_contra h1
  push_neg at h1 
  by_cases p : n ≤ -1
  let t := n + 2
  have ht : -2 + t = n
  simp [t]
  let k := -2 + t / 2
  have l1 : n ≤ k
  apply h
  simp [k]
  rw [abs_of_neg]
  rw [abs_of_pos]
  linarith
  linarith
  linarith
  simp [k] at l1 
  linarith
  push_neg at p 
  have l : n ≤ -1
  apply h
  simp
  rw [abs_of_neg]
  rw [abs_of_pos]
  linarith
  linarith
  linarith
  linarith

def siii : Set ℝ :=
  {x | x ^ 3 - 3 * x < 0}

-- Siii is bounded above.
theorem part_c_ub : ∃ z : ℝ, z ∈ upperBounds siii :=
  by
  use Real.sqrt 3
  rw [upperBounds]
  simp
  intro n
  intro h
  unfold Siii at h 
  simp at h 
  by_cases p : 0 < n
  have l := div_lt_div_of_lt p h
  rw [mul_div_assoc] at l 
  rw [div_self] at l 
  simp at l 
  have k : 1 + 2 = 3
  norm_num
  rw [← k] at l 
  rw [pow_add] at l 
  simp at l 
  rw [mul_comm] at l 
  rw [mul_div_assoc] at l 
  rw [div_self] at l 
  simp at l 
  have l1 : 3 = Real.sqrt 3 ^ 2
  norm_num
  rw [l1] at l 
  rw [sq_lt_sq] at l 
  have p1 : 0 ≤ n
  linarith
  rw [← abs_eq_self] at p1 
  rw [p1] at l 
  have p2 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [← abs_eq_self] at p2 
  rw [p2] at l 
  linarith
  linarith
  linarith
  push_neg at p 
  have p2 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  linarith

-- a lemma
theorem part_c_lemma1 : Real.sqrt 3 ∈ upperBounds siii :=
  by
  rw [upperBounds]
  simp
  intro n
  intro h
  unfold Siii at h 
  simp at h 
  by_cases p : 0 < n
  have l := div_lt_div_of_lt p h
  rw [mul_div_assoc] at l 
  rw [div_self] at l 
  simp at l 
  have k : 1 + 2 = 3
  norm_num
  rw [← k] at l 
  rw [pow_add] at l 
  simp at l 
  rw [mul_comm] at l 
  rw [mul_div_assoc] at l 
  rw [div_self] at l 
  simp at l 
  have l1 : 3 = Real.sqrt 3 ^ 2
  norm_num
  rw [l1] at l 
  rw [sq_lt_sq] at l 
  have p1 : 0 ≤ n
  linarith
  rw [← abs_eq_self] at p1 
  rw [p1] at l 
  have p2 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [← abs_eq_self] at p2 
  rw [p2] at l 
  linarith
  linarith
  linarith
  push_neg at p 
  have p2 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  linarith

-- Square root 3 is the least upper bound.
theorem part_c_lub : IsLUB siii (Real.sqrt 3) :=
  by
  rw [IsLUB]
  rw [IsLeast]
  constructor
  exact part_c_lemma1
  rw [lowerBounds]
  simp
  intro n
  intro h1
  rw [upperBounds] at h1 
  unfold Siii at h1 
  simp at h1 
  by_contra
  push_neg at h 
  by_cases p : (3 / 2 : ℝ) ≤ n
  let t := Real.sqrt 3 - n
  have ht : Real.sqrt 3 - t = n
  simp [t]
  let k := Real.sqrt 3 - t / 2
  have l : k ^ 3 < 3 * k
  have l2 : 0 < k
  simp [k]
  simp [t]
  linarith
  have l3 : k ^ 2 < 3
  simp [k]
  rw [sub_sq]
  rw [Real.sq_sqrt]
  have l4 : Real.sqrt 3 ≤ Real.sqrt 4
  have l5 : (3 : ℝ) ≤ (4 : ℝ)
  norm_num
  exact Real.sqrt_le_sqrt l5
  have l6 : (4 : ℝ) = (2 : ℝ) * (2 : ℝ)
  norm_num
  rw [l6] at l4 
  have l7 : 0 ≤ (2 : ℝ)
  norm_num
  rw [Real.sqrt_mul_self l7] at l4 
  have l8 : t / 2 < 1
  simp [t]
  linarith
  rw [sq]
  have l9 : 0 < Real.sqrt 3
  linarith
  have l10 : 1 < Real.sqrt 3
  linarith
  have l11 : 0 < t / 2
  linarith
  have l12 : -(2 * Real.sqrt 3) * (t / 2) + t / 2 * (t / 2) < 0
  rw [← right_distrib]
  have l13 : -(2 * Real.sqrt 3) + t / 2 < 0
  linarith
  exact mul_neg_of_neg_of_pos l13 l11
  linarith
  linarith
  have l4 : k ^ 2 * k < 3 * k := mul_lt_mul_of_pos_right l3 l2
  have l5 : 1 + 2 = 3
  norm_num
  rw [← l5]
  rw [pow_add]
  simp
  rw [mul_comm]
  exact l4
  have h2 := h1 l
  have h3 : n < k
  have h4 : 0 < t
  linarith
  simp [k]
  rw [← ht]
  linarith
  linarith
  push_neg at p 
  have ll : (3 / 2 : ℝ) ^ 3 < 3 * (3 / 2 : ℝ)
  norm_num
  have h2 := h1 ll
  linarith

-- Siii is not bounded below.
theorem part_c_lb : ¬∃ z : ℝ, z ∈ lowerBounds siii :=
  by
  push_neg
  intro n
  rw [lowerBounds]
  simp
  by_cases h : -2 < n
  use -2
  constructor
  unfold Siii
  simp
  linarith
  exact h
  push_neg at h 
  use n - 1
  constructor
  unfold Siii
  simp
  have k : 1 + 2 = 3
  norm_num
  rw [← k]
  rw [pow_add]
  simp
  rw [mul_comm]
  have l1 : n - 1 < 0
  linarith
  apply mul_lt_mul_of_neg_right
  have l2 : n - 1 < -2
  linarith
  have l3 : 2 ^ 2 < (n - 1) ^ 2
  rw [sq_lt_sq]
  rw [abs_of_pos]
  rw [abs_of_neg]
  linarith
  exact l1
  norm_num
  have l4 : (2 : ℝ) ^ 2 = 4
  norm_num
  rw [l4] at l3 
  linarith
  exact l1
  linarith

def siv : Set ℝ :=
  {x | ∃ a b : PNat, x = a ^ 2 + b ^ 2}

theorem part_d_ub : ∃ z : ℝ, z ∈ upperBounds siv := by sorry

theorem part_d_lub : IsLUB siv 37 := by sorry

theorem part_d_lb : ∃ z : ℝ, z ∈ lowerBounds siv := by sorry

theorem part_d_glb : IsGLB siv 37 := by sorry

end Chapter22.Exercise01

