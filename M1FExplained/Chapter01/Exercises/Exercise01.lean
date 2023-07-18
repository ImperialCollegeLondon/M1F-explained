import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Tactic

namespace Chapter01.Exercise01

theorem ZFSet.well_founded : ¬∃ α : ZFSet.{0}, α = {α} := by
  rintro ⟨α, hα⟩
  have hα' : α ∈ α := by 
    nth_rewrite 2 [hα]
    rw [ZFSet.mem_singleton] 
  have foo : WellFounded (α := ZFSet.{0}) (· ∈ ·) := ZFSet.mem_wf
  obtain ⟨a, haα, h⟩ := WellFounded.has_min foo {α} ⟨α, Set.mem_singleton _⟩
  rw [Set.mem_singleton_iff] at haα
  subst haα
  specialize h a $ Set.mem_singleton _
  contradiction

variable (α : ZFSet.{0})

def zero : ZFSet.{0} := {}

def one : ZFSet.{0} :=
  {zero}

def two : ZFSet.{0} :=
  {zero, one}

def three : ZFSet.{0} :=
  {zero, one, two}

@[reducible]
def a : ZFSet :=
  {α, {one, α}, {three}, {{one, three}}, three}

/-

This exercise is rather poorly-specified. Liebeck does not
give the set-theoretic definitions of `1` or `3`, and
does not say which set `α` is. As a result, the set `A`
depends on the input variable `α`, and some parts
of this question depend on the value of `α`.

-/
theorem part_a : α ∈ a α := by simp

theorem part_b_helper {α β} (h : α ≠ β) : ({α} : ZFSet) ≠ {β} :=
  by
  intro h2
  apply h
  have : α ∈ ({β} : ZFSet) := by simp [← h2]
  simpa

theorem part_b_helper' : zero ≠ one := by
  intro h
  have h0 : zero ∈ zero := by
    nth_rw 2 [h]
    simp [zero, one]
  simp [zero] at h0

/-
I'm assuming part(b) is supposed to be false. 
However this depends on what α is supposed to be
and also on the implementation of the set `3`.
-/
theorem part_b (h1 : α ≠ one)
    -- otherwise {α} = {1,α} ∈ A
    (h3 : α ≠ three)
    -- otherwise {α} ∈ A
    (h13 : α ≠ {one, three}) :-- otherwise {α} ∈ A
      {α} ∉
      a α :=
  by
  simp
  push_neg
  refine' ⟨_, _, _, _, _⟩
  · -- {α} ≠ α
    intro h
    apply ZFSet.well_founded
    use α
    rw [h]
  · -- α ≠ {1,α}
    intro h
    apply h1
    have : one ∈ ({one, α} : ZFSet) := by simp
    rw [← h] at this 
    symm
    simpa
  ·-- {α} ≠ {three}
    exact h3
  ·-- {α} ≠ {{one,three}}
    exact h13
  · -- With our implementation of {3} we can't have
    -- {α} = 3, but if you implement the naturals
    -- numbers as n+1={n} then we would have to avoid
    -- the case α = 2 as well
    intro h
    apply part_b_helper'
    trans α
    · suffices zero ∈ ({α} : ZFSet) by simpa
      rw [h]
      simp [three]
    · suffices one ∈ ({α} : ZFSet) by
        symm
        simpa
      rw [h]
      simp [three]

-- This part is true if α = 1
theorem part_c (h1 : α ≠ one) : ¬{one, α} ⊆ a α := by sorry

theorem part_d : {three, {three}} ⊆ a α := by sorry

-- This part is true if α = three or if α = {one, three}
theorem part_e (h1 : α ≠ three) (h13 : α ≠ {one, three}) : ¬{one, three} ∈ a α := by sorry

-- this part is true if α = three or if α = {one, three}
-- (because it's the same question as part (e))
theorem part_f (h1 : α ≠ three) (h13 : α ≠ {one, three}) : ¬{{one, three}} ⊆ a α := by sorry

theorem part_g : {{one, α}} ⊆ a α := by
  intro x hx
  simp at hx 
  subst hx
  simp

theorem part_h : ¬{one, α} ∉ a α := by
  push_neg
  simp

theorem part_i : ∅ ⊆ a α := by
  intro x hx
  simp at hx

end Chapter01.Exercise01

