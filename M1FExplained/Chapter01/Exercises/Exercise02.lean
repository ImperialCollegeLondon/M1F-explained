import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Chapter01.Exercise02

-- Let B,C,D,E be the following sets
def B : Set ℝ :=
  {x | x ^ 2 < 4}

def C : Set ℝ :=
  {x | 0 ≤ x ∧ x < 2}

def D : Set ℝ :=
  {x | ∃ n : ℤ, x = n ∧ x ^ 2 < 1}

def E : Set ℝ :=
  {1}

theorem hD : D = ({0} : Set ℝ) := by
  simp_rw [D]
  ext
  constructor
  · rintro ⟨n, rfl, hn⟩
    simp_rw [sq_lt_one_iff_abs_lt_one] at hn 
    rw [Set.mem_singleton_iff]
    rw [abs_lt] at hn 
    cases' hn with hl hr
    norm_cast at *
    change -1 < n at hl
    interval_cases n
    rfl
  intro hx
  rw [Set.mem_singleton_iff] at hx 
  simp_rw [hx, sq_lt_one_iff_abs_lt_one, exists_and_right, Set.mem_setOf_eq, abs_zero, zero_lt_one,
    and_true_iff]
  use (0 : ℤ)
  norm_num

-- Which pair of these sets has the property that neither is contained in the other?
theorem part_a :
    ∃ (S : Set ℝ) (_ : S ∈ ({B, C, D, E} : Set (Set ℝ))) 
      (T : Set ℝ) (_ : T ∈ ({B, C, D, E} : Set (Set ℝ))),
      ¬S ⊆ T ∧ ¬T ⊆ S := by
  use D, by simp, E, by simp
  constructor
  · rw [Set.subset_def]
    push_neg
    use 0
    constructor
    · rw [D]
      use 0
      norm_num
    · simp [E]
  · rw [Set.subset_def]
    push_neg
    use 1
    constructor
    · simp [E]
    · simp [D]

-- If X is either B,C,D,E and E ⊆ X ⊆ B, what else can we deduce about X? 
-- Note that figuring out what to prove is part of the question
theorem partb (X : Set ℝ) (hX : X ∈ ({B, C, D, E} : Set (Set ℝ))) (h1 : E ⊆ X) (h2 : X ⊆ B) :
    X = B ∨ X = C ∨ X = E := by
  simp at hX 
  cases' hX with hb hc
  · left
    apply hb
  · cases' hc with h3 h4
    · right
      left
      apply h3
    · cases' h4 with h5 h6
      · left
        subst h5
        rw [D, E] at h1 
        simp at h1 
      · right
        subst h6
        right
        rfl

theorem partb' (X : Set ℝ) (hX : X ∈ ({B, C, D, E} : Set (Set ℝ))) (h1 : E ⊆ X) (h2 : X ⊆ B) :
    X ≠ D := by
  rintro rfl
  have hD2 : ¬E ⊆ D := by
    exfalso
    simp_rw [E, hD] at h1 
    simp at h1
  contradiction

end Chapter01.Exercise02

