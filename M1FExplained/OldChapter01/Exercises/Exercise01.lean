import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Tactic

lemma ZFSet.well_founded : ¬ ∃ α : ZFSet, α = {α} := by
  sorry

variable (α : ZFSet.{0})

def zero : ZFSet.{0} := {}
def one : ZFSet.{0} := {zero}
def two : ZFSet.{0} := {zero, one}
def three : ZFSet.{0} := {zero, one, two}

@[reducible] def A : ZFSet := {α, {one,α},{three},{{one,three}},three}

/-

This exercise is rather poorly-specified. Liebeck does not
give the set-theoretic definitions of `1` or `3`, and
does not say which set `α` is. As a result, the set `A`
depends on the input variable `α`, and some parts
of this question depend on the value of `α`.

-/

lemma part_a : α ∈ A (α) := by
  simp

lemma part_b_helper {α β} (h : α ≠ β) : ({α} : ZFSet) ≠ {β} := by
  intro h2
  apply h
  have : α ∈ ({β} : ZFSet)
  { simp [← h2] }
  simpa

lemma part_b_helper' : zero ≠ one := by
  intro h
  have h0 : zero ∈ zero := by
    nth_rewrite 2 [h]
    simp [zero, one]
  simpa [zero] using h0
  done

#exit -- the rest needs to be translated from Lean 3. Investigating mathport!

/-
I'm assuming part(b) is supposed to be false. 
However this depends on what α is supposed to be
and also on the implementation of the set `3`.
-/
lemma part_b (h1 : α ≠ one) -- otherwise {α} = {1,α} ∈ A
  (h3 : α ≠ three) -- otherwise {α} ∈ A
  (h13 : α ≠ {one, three}) -- otherwise {α} ∈ A
  : {α} ∉ A α :=
begin
  simp,
  push_neg,
  refine ⟨_, _, _, _, _⟩,
  { -- {α} ≠ α
    intro h,
    apply ZFSet.well_founded,
    use α,
    rw h, },
  { -- α ≠ {1,α}
    intro h,
    apply h1,
    have : one ∈ ({one, α} : ZFSet) := by simp,
    rw ← h at this,
    symmetry,
    simpa, },  
  { -- {α} ≠ {three}
    exact h3, },
  { -- {α} ≠ {{one,three}}
    exact h13, },
  { -- With our implementation of {3} we can't have
    -- {α} = 3, but if you implement the naturals
    -- numbers as n+1={n} then we would have to avoid
    -- the case α = 2 as well
    intro h,
    apply part_b_helper',
    transitivity α,
    { suffices : zero ∈ ({α} : ZFSet),
      { simpa },
      rw h,
      simp [three], },
    { suffices : one ∈ ({α} : ZFSet),
      { symmetry,
        simpa },
      rw h,
      simp [three], }, }
end

-- This part is true if α = 1
lemma part_c (h1 : α ≠ one) : ¬ {one, α} ⊆ A α :=
begin
  sorry
end

lemma part_d : {three, {three}} ⊆ A α :=
begin
  sorry
end

-- This part is true if α = three or if α = {one, three}
lemma part_e (h1 : α ≠ three) (h13 : α ≠ {one, three}) : ¬ {one, three} ∈ A α := 
begin
  sorry
end

-- this part is true if α = three or if α = {one, three}
-- (because it's the same question as part (e))
lemma part_f (h1 : α ≠ three) (h13 : α ≠ {one, three}) : ¬ {{one, three}} ⊆ A α := 
begin
  sorry
end

lemma part_g : {{one, α}} ⊆ A α :=
begin
  intros x hx,
  simp at hx,
  subst hx,
  simp,
end

lemma part_h : ¬ ({one,α} ∉ A α) :=
begin
  push_neg,
  simp,
end

lemma part_i : ∅ ⊆ A α :=
begin
  intros x hx,
  simp at hx,
  cases hx,
end
