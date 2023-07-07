/-
7. (a) Let S = {1, 2, 3} and T = {1, 2, 3, 4, 5}. How many functions are
there from S to T ? How many of these are 1-1?
(b) Let |S| = m, |T | = n with m ≤ n. Show that the number of 1-1 func-
tions from S to T is equal to n(n − 1)(n − 2) · · ·(n − m + 1).

! This file was ported from Lean 3 source module chapter19.exercises.exercise07
-/
import Mathbin.Tactic.Default
import Mathbin.Data.Fintype.CardEmbedding

namespace Chapter19.Exercise07

open scoped Classical

-- replace 37 with the right number
theorem parta (S T : Type) [Fintype S] [Fintype T] (hS : Fintype.card S = 3)
    (hT : Fintype.card T = 5) : Fintype.card (S → T) = 125 :=
  by
  simp [Fintype.card_fun, hS, hT]
  norm_num

-- replace 37 with the right number
theorem parta' (S T : Type) [Fintype S] [Fintype T] (hS : Fintype.card S = 3)
    (hT : Fintype.card T = 5) : Fintype.card { f : S → T // Function.Injective f } = 60 :=
  by
  have h : Fintype.card { f : S → T // Function.Injective f } = Fintype.card (S ↪ T) :=
    by
    apply Fintype.card_congr
    exact Equiv.subtypeInjectiveEquivEmbedding S T
  rw [h]
  simpa [Fintype.card_embedding_eq, hS, hT]

open scoped BigOperators

-- for Π
theorem partb (S T : Type) [Fintype S] [Fintype T] (m n : ℕ) (hmn : m ≤ n) (hS : Fintype.card S = m)
    (hT : Fintype.card T = n) :
    Fintype.card { f : S → T // Function.Injective f } = ∏ i in Finset.Icc (n - m + 1) n, i :=
  by
  have h : Fintype.card { f : S → T // Function.Injective f } = Fintype.card (S ↪ T) :=
    by
    apply Fintype.card_congr
    exact Equiv.subtypeInjectiveEquivEmbedding S T
  rw [h]
  simp [Fintype.card_embedding_eq, hS, hT]
  clear hS hT h _inst_1 _inst_2
  induction m
  simp
  have hm : m_n ≤ n := Nat.le_of_succ_le hmn
  specialize m_ih hm
  simp [Nat.descFactorial_succ, m_ih, Nat.succ_eq_add_one]
  have p : insert (n - m_n) (Finset.Icc (n - m_n + 1) n) = Finset.Icc (n - (m_n + 1) + 1) n :=
    by
    ext c
    constructor
    · intro hc
      simp at *
      cases' hc with hc1 hc2
      · subst hc1
        simp
        linarith
      · simp [hc2]
        linarith [hc2.1]
    · intro hc
      simp at *
      simp [hc]
      cases' hc with hc1 hc2
      by_cases n - m_n + 1 ≤ c
      · right
        exact h
      · push_neg at h 
        left
        linarith
  rw [← p]
  simp

end Chapter19.Exercise07

