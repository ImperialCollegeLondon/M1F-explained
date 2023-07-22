/-
8. The manufacturers of the high-fibre cereal “Improve Your Functions”
are offering a prize of £1000 to anyone who can find three different
integers a, b, c and a polynomial P(x) with integer coefficients, such that
P(a) = b, P(b) = c and P(c) = a.
Critics Ivor Smallbrain and Greta Picture spend several long evenings
trying to solve this, without success.
Prove that nobody will win the prize.
(Hint: Observe that P(x) − P(y) = (x − y)Q(x, y), where Q(x, y) is a
polynomial in x, y with integer coefficients. Substitute x = a, y = b, etc.,
into this equation and see what happens.)

! This file was ported from Lean 3 source module chapter19.exercises.exercise08
-/
import Mathlib.Tactic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.MvPolynomial.CommRing

namespace Chapter19.Exercise08

open scoped Polynomial

-- notation for polynomials
open Polynomial

-- prove for the hint
variable {R : Type _} [CommRing R] (p : R[X]) {A : Type _} [CommRing A] (f : R →+* A) (s t : A)

--open MvPolynomial -eval

open scoped BigOperators

theorem dvd_pow_sub_pow (a b : R) (n : ℕ) : a - b ∣ a ^ n - b ^ n :=
  by
  cases n with
  | zero => simp
  | succ n => 
    use ∑ i in Finset.range n.succ, a ^ i * b ^ (n - i)
    simp_rw [Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ']
    suffices : ∑ x : ℕ in Finset.range n, a * (a ^ x * b ^ (n - x)) =
        ∑ k : ℕ in Finset.range n, b * (a ^ (k + 1) * b ^ (n - (k + 1))) 
    · rw [this, Nat.succ_eq_add_one, Nat.sub_self]; ring_nf; aesop
    refine' Finset.sum_congr rfl fun i hi => _
    rw [Finset.mem_range] at hi 
    rw [pow_add]
    ring_nf
    simp only [mul_assoc]
    congr
    rw [← pow_succ]
    congr
    rw [Nat.sub_eq_iff_eq_add hi.le, add_right_comm, add_assoc]
    rw [Nat.lt_iff_add_one_le] at hi 
    refine (Nat.sub_eq_iff_eq_add hi).mp ?_
    rw [add_comm]

theorem dvd_poly_sub_poly : s - t ∣ p.eval₂ f s - p.eval₂ f t :=
  by
  refine p.induction_on ?_ ?_ ?_
  -- check it for zero, monomials and sums
  · simp
  -- that's zero
  · intro p q hp hq
    -- this is addition
    convert dvd_add hp hq using 1
    simp only [Polynomial.eval₂_add]
    ring
  -- this is the tricky case
  · rintro m a _
    simp
    rw [← mul_sub]
    apply dvd_mul_of_dvd_right
    apply dvd_pow_sub_pow

-- useful lemma for the proof
theorem iff_one_mul (a b : ℤ) (ha : a ≠ (0 : ℤ)) : a = b * a ↔ b = 1 := by
  constructor
  · intro h
    have h1 : a / a = b * a / a := congr (congr_arg Div.div h) rfl
    have h2 : a / a = 1 := by apply Int.ediv_eq_of_eq_mul_right ha; ring
    have h3 : b * a / a = b * (a / a) := Int.mul_ediv_assoc _ (by rfl)
    simp [h2, h3, h2] at h1 
    rw [h1]
  · intro h
    rw [h]
    ring

-- another useful fact for the proof
theorem cube_one (a b c : ℤ) (h : a * b * c = 1) (ha : a ≠ -1) (hb : b ≠ -1) (hc : c ≠ -1) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · suffices a = 1 ∨ a = -1 by
      cases' this with h1 h2
      exact h1
      exfalso
      aesop
    · apply Int.eq_one_or_neg_one_of_mul_eq_one (w := b * c)
      linarith
  · constructor
    · rw [show a * b * c = b * a * c by ring] at h 
      suffices b = 1 ∨ b = -1 by
        cases' this with h1 h2
        exact h1
        exfalso
        aesop
      · apply Int.eq_one_or_neg_one_of_mul_eq_one (w := a * c)
        linarith
    · rw [show a * b * c = c * a * b by ring] at h 
      suffices c = 1 ∨ c = -1 by
        cases' this with h1 h2
        exact h1
        exfalso
        aesop
      · apply Int.eq_one_or_neg_one_of_mul_eq_one (w := a * b)
        linarith

example :
    ¬∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ P : ℤ[X], 
    Polynomial.eval a P = b ∧ Polynomial.eval b P = c ∧ Polynomial.eval c P = a := by
  intro h
  rcases h with ⟨a, b, c, hab, hbc, hca, P, hP1, hP2, hP3⟩
  have h : ∀ x y : ℤ, x - y ∣ eval x P - eval y P := by apply dvd_poly_sub_poly
  have h1 : ∃ k1 : ℤ, b - c = k1 * (a - b) := by 
    specialize h a b
    rw [hP1, hP2] at h
    exact exists_eq_mul_left_of_dvd h
  have h2 : ∃ k2 : ℤ, c - a = k2 * (b - c) := by 
    specialize h b c; 
    rw [hP2, hP3] at h ;
    exact exists_eq_mul_left_of_dvd h
  have h3 : ∃ k3 : ℤ, a - b = k3 * (c - a) := by 
    specialize h c a; 
    rw [hP3, hP1] at h ;
    exact exists_eq_mul_left_of_dvd h
  clear hP1 hP2 hP3 h P
  cases' h1 with k1 h1
  cases' h2 with k2 h2
  cases' h3 with k3 h3
  have hk : k1 * k2 * k3 = 1 := by
    ring_nf
    suffices : a - b = k3 * k2 * k1 * (a - b)
    rw [iff_one_mul] at this; rw [← this]; ring
    exact sub_ne_zero.mpr hab
    linear_combination (-k2 - 1) * h1 + (-(k3 * k1) - 1) * h2 + (-(k2 * k1) - k1) * h3
  have hk1 : k1 ≠ -1 := by
    by_contra hk
    simp [hk] at h1 
    norm_cast at *
  have hk2 : k2 ≠ -1 := by
    by_contra hk
    simp [hk] at h2 
    norm_cast at *
  have hk3 : k3 ≠ -1 := by
    by_contra hk
    simp [hk] at h3 
    norm_cast at *
  have hk' : k1 = 1 ∧ k2 = 1 ∧ k3 = 1 := cube_one k1 k2 k3 hk hk1 hk2 hk3
  clear hk1 hk2 hk3
  rcases hk' with ⟨hk1, hk2, hk3⟩
  simp [hk1, hk2, hk3] at *
  clear hk hk1 hk2 hk3
  suffices : a = c
  apply hca
  rw [this]
  rw [h3] at h1 
  have h' : b - c = c - a ↔ b = 2 * c - a := by
    constructor
    intro h
    linarith
    intro h
    linarith
  rw [h'] at h1 
  rw [h1] at h2 
  have h'' : c - a = 2 * c - a - c ↔ 3 * c = 3 * a :=
    by
    constructor
    intros
    linear_combination -h3 - h1
    intros
    linear_combination
  rw [h''] at h2 
  linarith

-- thinking if an alternative way may be more easier using the following two
theorem dvd_mod_le (a b : ℤ) (hb : b ≠ 0) : a ∣ b → |a| ≤ |b| :=
  by
  intro h
  have := exists_eq_mul_left_of_dvd h
  cases' this with c h1
  have h2 : |b| = |c| * |a| := by rw [h1, abs_mul]
  have hc : c ≠ 0 := by
    by_contra hc
    simp [hc] at h1 
    norm_cast at *
  have hc : 1 ≤ |c| := Int.one_le_abs hc
  rw [h2]
  exact le_mul_of_one_le_left (abs_nonneg a) hc

theorem squeeze_three (a b c : ℤ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ a) : a = b ∧ a = c ∧ b = c :=
  by
  constructor
  have h4 : b ≤ a := by linarith
  exact ge_antisymm h4 h1
  constructor
  have h5 : a ≤ c := by linarith
  exact ge_antisymm h3 h5
  have h6 : c ≤ b := by linarith
  exact ge_antisymm h6 h2

-- alternative full solution
example :
    ¬∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ P : ℤ[X], eval a P = b ∧ eval b P = c ∧ eval c P = a :=
  by
  intro h
  rcases h with ⟨a, b, c, hab, hbc, hca, P, hP1, hP2, hP3⟩
  have h : ∀ x y : ℤ, x - y ∣ eval x P - eval y P := by apply dvd_poly_sub_poly
  have h1 : a - b ∣ b - c := by specialize h a b; rwa [hP1, hP2] at h 
  have h2 : b - c ∣ c - a := by specialize h b c; rwa [hP2, hP3] at h 
  have h3 : c - a ∣ a - b := by specialize h c a; rwa [hP3, hP1] at h 
  clear hP1 hP2 hP3 h P
  have h4 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h5 : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have h6 : c - a ≠ 0 := sub_ne_zero.mpr hca
  have h7 : |a - b| ≤ |b - c| := dvd_mod_le (a - b) (b - c) h5 h1
  have h8 : |b - c| ≤ |c - a| := dvd_mod_le (b - c) (c - a) h6 h2
  have h9 : |c - a| ≤ |a - b| := dvd_mod_le (c - a) (a - b) h4 h3
  have h10 : |a - b| = |b - c| ∧ |a - b| = |c - a| ∧ |b - c| = |c - a| :=
    squeeze_three |a - b| |b - c| |c - a| h7 h8 h9
  clear h1 h2 h3 h4 h5 h6 h7 h8 h9
  rcases h10 with ⟨h1, h2, h3⟩
  simp [abs_eq_abs] at *
  cases' h1 with h11 h12
  swap
  aesop
  cases' h2 with h21 h22
  swap
  aesop
  cases' h3 with h31 h32
  swap
  aesop
  apply hca
  linarith

end Chapter19.Exercise08

