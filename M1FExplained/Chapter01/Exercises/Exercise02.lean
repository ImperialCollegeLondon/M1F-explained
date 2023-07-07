import Mathbin.Tactic.IntervalCases
import Mathbin.Data.Real.Basic

namespace Chapter01.Exercise02

-- Let B,C,D,E be the following sets
def b : Set ℝ :=
  {x | x ^ 2 < 4}

def c : Set ℝ :=
  {x | 0 ≤ x ∧ x < 2}

def d : Set ℝ :=
  {x | ∃ n : ℤ, x = n ∧ x ^ 2 < 1}

def e : Set ℝ :=
  {1}

theorem hD : d = ({0} : Set ℝ) := by
  simp_rw [D]
  ext
  constructor
  · rintro ⟨n, rfl, hn⟩
    simp_rw [sq_lt_one_iff_abs_lt_one] at hn 
    rw [Set.mem_singleton_iff]
    rw [abs_lt] at hn 
    cases' hn with hl hr
    norm_cast at *
    interval_cases
  intro hx
  rw [Set.mem_singleton_iff] at hx 
  simp_rw [hx, sq_lt_one_iff_abs_lt_one, exists_and_right, Set.mem_setOf_eq, abs_zero, zero_lt_one,
    and_true_iff]
  use (0 : ℤ)
  norm_num

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (S
 T «expr ∈ » ({B[chapter01.exercise02.B], C[chapter01.exercise02.C], D[chapter01.exercise02.D], E[chapter01.exercise02.E]} : set[set]
 (set[set] exprℝ()))) -/
-- Which pair of these sets has the property that neither is contained in the other?
theorem parta :
    ∃ (S : _) (_ : S ∈ ({b, c, d, e} : Set (Set ℝ))) (T : _) (_ : T ∈ ({b, c, d, e} : Set (Set ℝ))),
      ¬S ⊆ T ∧ ¬T ⊆ S :=
  by
  use D
  constructor
  · simp
  · use E
    constructor
    · simp
    · constructor
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
theorem partb (X : Set ℝ) (hX : X ∈ ({b, c, d, e} : Set (Set ℝ))) (h1 : e ⊆ X) (h2 : X ⊆ b) :
    X = b ∨ X = c ∨ X = e := by
  simp at hX 
  cases' hX with hb hc
  · left
    apply hb
  · cases' hc with h3 h4
    right
    left
    apply h3
    · cases' h4 with h5 h6
      · left
        subst h5
        rw [D] at h1 
        rw [E] at h1 
        finish
      · right
        subst h6
        right
        rfl

theorem partb' (X : Set ℝ) (hX : X ∈ ({b, c, d, e} : Set (Set ℝ))) (h1 : e ⊆ X) (h2 : X ⊆ b) :
    X ≠ d := by
  intro hX'
  rw [hX'] at *
  have hD2 : ¬E ⊆ D := by
    exfalso
    simp_rw [E, hD] at h1 
    simp at h1 
    exact h1
  contradiction

end Chapter01.Exercise02

