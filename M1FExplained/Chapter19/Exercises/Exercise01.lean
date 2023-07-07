import Mathbin.Tactic.Default
import Mathbin.Data.Real.Sqrt
import Mathbin.Data.Int.Modeq
import Mathbin.Data.Real.Irrational
import Mathbin.Data.Nat.Factorization.PrimePow
import Mathbin.Data.Nat.PrimeNormNum

namespace Chapter19.Exercise01

/-

For each of the following functions `f`, say whether `f` is `1-1` and whether `f`
is `onto`.

-/
def f1 (x : ℝ) : ℝ :=
  x ^ 2 + 2 * x

noncomputable def f2 (x : ℝ) : ℝ :=
  if 1 < x then x - 2 else if x < -1 then x + 2 else -x

noncomputable def f3 (x : ℚ) : ℝ :=
  (x + Real.sqrt 2) ^ 2

def f4 (mnr : ℕ × ℕ × ℕ) : ℕ :=
  let ⟨m, n, r⟩ := mnr
  2 ^ m * 3 ^ n * 5 ^ r

def f5 (mnr : ℕ × ℕ × ℕ) : ℕ :=
  let ⟨m, n, r⟩ := mnr
  2 ^ m * 3 ^ n * 6 ^ r

-- For the last question let's first make the equivalence relation
def E (a b : ℤ) : Prop :=
  a ≡ b [ZMOD 7]

theorem he : Equivalence E :=
  ⟨-- reflexive
  by
    intro x
    unfold e,-- symmetric
  by
    intro x y h
    unfold e at *
    exact Int.ModEq.symm h,-- transitive
  by
    intro x y z hxy hyz
    unfold e at *
    exact Int.ModEq.trans hxy hyz⟩

-- Let's now say that `e` is the "canonical" equivalence relation on ℤ
instance s : Setoid ℤ :=
  ⟨E, he⟩

theorem s_def (a b : ℤ) : a ≈ b ↔ a ≡ b [ZMOD 7] :=
  Iff.rfl

-- and now we can use the theory of quotients. The set `S` in the question
-- is called `quotient s` here.
def f6 (x : Quotient Chapter19.Exercise01.s) : Quotient Chapter19.Exercise01.s :=
  Quotient.map (fun t : ℤ => t + 1)
    (by
      -- Lean points out that if we don't show the below, then `f6` isn't well-defined!
      show ∀ a b : ℤ, a ≈ b → a + 1 ≈ b + 1
      -- So we have to prove it now.
      intro a b hab
      rw [s_def] at *
      exact Int.ModEq.add_right 1 hab)
    x

-- `injective` is actually called `function.injective` so let's open `function`
open Function

-- now we can just call it `injective`
/-

## The rules

If the functions are injective/surjective, prove the lemmas. If they're not,
then put `¬` in front of them (e.g. `exercise01inj : ¬ (injective f1)` and prove
that instead!

-/
theorem exercise01inj : ¬Injective f1 := by
  intro h
  have hp : f1 (-2) = f1 0 := by unfold f1; norm_num
  specialize h hp
  norm_num at h 

theorem exercise01surj : ¬Surjective f1 := by
  intro h
  specialize h (-2)
  cases' h with x hx
  unfold f1 at hx 
  have hp : ∀ x : ℝ, x ^ 2 + 2 * x = -2 ↔ (x + 1) ^ 2 = -1 :=
    by
    intro x; constructor; · intro h1; linear_combination h1
    · intro h2; linear_combination h2
  specialize hp x
  rw [hp] at hx 
  nlinarith

theorem exercise02inj : ¬Injective f2 := by
  intro h
  have hp : f2 (-1 / 2) = f2 (5 / 2) := by unfold f2; split_ifs <;> linarith
  specialize h hp
  norm_num at h 

theorem exercise02surj : Surjective f2 := by
  intro y
  rcases lt_trichotomy y 0 with (h1 | rfl | h3)
  · use y - 2; unfold f2; split_ifs <;> linarith
  · use 0; unfold f2; split_ifs <;> linarith
  · use y + 2; unfold f2; split_ifs <;> linarith

theorem exercise03inj : Injective f3 := by
  intro a b hab
  unfold f3 at hab 
  simp [mul_self_eq_mul_self_iff, pow_two] at hab 
  rcases hab with (h1 | h2)
  · assumption
  · exfalso; suffices h : Real.sqrt 2 = -(a + b) / 2
    · norm_cast at h ; apply irrational_sqrt_two; use -(a + b) / 2; exact h.symm
    · linear_combination h2 / 2

theorem exercise03surj : ¬Surjective f3 := by
  intro h
  specialize h (-1)
  cases' h with x h
  unfold f3 at h 
  nlinarith

theorem padicValNat_two_aux (a b c : ℕ) : padicValNat 2 (2 ^ a * 3 ^ b * 5 ^ c) = a :=
  by
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  rw [padicValNat.mul (mul_ne_zero _ _), padicValNat.mul, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    norm_num at h 
  all_goals try exact pow_ne_zero _ (by norm_num)
  assumption

theorem padicValNat_three_aux (a b c : ℕ) : padicValNat 3 (2 ^ a * 3 ^ b * 5 ^ c) = b :=
  by
  haveI : Fact (Nat.Prime 3) := Fact.mk Nat.prime_three
  rw [padicValNat.mul (mul_ne_zero _ _), padicValNat.mul, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h 
  all_goals try exact pow_ne_zero _ (by norm_num)
  assumption

theorem Nat.prime_five : Nat.Prime 5 := by norm_num

theorem padicValNat_five_aux (a b c : ℕ) : padicValNat 5 (2 ^ a * 3 ^ b * 5 ^ c) = c :=
  by
  haveI : Fact (Nat.Prime 5) := Fact.mk nat.prime_five
  rw [padicValNat.mul (mul_ne_zero _ _), padicValNat.mul, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_five h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_five h
    norm_num at h 
  all_goals try exact pow_ne_zero _ (by norm_num)
  assumption

theorem exercise04inj : Injective f4 :=
  by
  rintro ⟨a1, b1, c1⟩ ⟨a2, b2, c3⟩ h
  unfold f4 at h 
  simp only [Prod.mk.inj_iff]
  refine' ⟨_, _, _⟩
  · rw [← padic_val_nat_two_aux a1 b1 c1, h, padic_val_nat_two_aux]
  · rw [← padic_val_nat_three_aux a1 b1 c1, h, padic_val_nat_three_aux]
  · rw [← padic_val_nat_five_aux a1 b1 c1, h, padic_val_nat_five_aux]

theorem Nat.prime_seven : Nat.Prime 7 := by norm_num

theorem padicValNat_seven_aux (a b c : ℕ) : padicValNat 7 (2 ^ a * 3 ^ b * 5 ^ c) = 0 :=
  by
  haveI : Fact (Nat.Prime 7) := Fact.mk nat.prime_seven
  rw [padicValNat.mul (mul_ne_zero _ _), padicValNat.mul, padicValNat.eq_zero_of_not_dvd,
    padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd]
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_seven h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_seven h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_seven h
    norm_num at h 
  all_goals try exact pow_ne_zero _ (by norm_num)
  assumption

theorem exercise04surj : ¬Surjective f4 := by
  intro h
  specialize h 7
  cases' h with x h
  rcases x with ⟨a, b, c⟩
  unfold f4 at h 
  have := padic_val_nat_seven_aux a b c
  rw [h] at this 
  simpa using this

theorem exercise05inj : ¬Injective f5 := by
  intro h
  unfold injective at h 
  have hp : f5 ⟨1, 1, 1⟩ = f5 ⟨2, 2, 0⟩ := by unfold f5 at *; norm_num
  specialize h hp
  simpa using h

theorem padicValNat_five_aux_ (a b c : ℕ) : padicValNat 5 (2 ^ a * 3 ^ b * 6 ^ c) = 0 :=
  by
  haveI : Fact (Nat.Prime 5) := Fact.mk nat.prime_five
  rw [padicValNat.mul (mul_ne_zero _ _), padicValNat.mul, padicValNat.eq_zero_of_not_dvd,
    padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd]
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_five h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_five h
    norm_num at h 
  · intro h
    replace h := Nat.Prime.dvd_of_dvd_pow nat.prime_five h
    norm_num at h 
  all_goals try exact pow_ne_zero _ (by norm_num)
  assumption

theorem exercise05surj : ¬Surjective f5 := by
  intro h
  specialize h 5
  cases' h with x h
  rcases x with ⟨a, b, c⟩
  unfold f5 at h 
  have := padic_val_nat_five_aux_ a b c
  rw [h] at this 
  simpa using this

theorem exercise06inj : Injective f6 := by
  intro a b hab
  unfold f6 at hab 
  revert hab
  apply Quotient.induction_on₂ a b
  intro x y hab
  simp [s_def] at hab 
  rw [Quotient.eq', s_def]
  convert Int.ModEq.sub_right 1 hab <;> simp

theorem exercise06surj : Surjective f6 := by
  intro y
  apply Quotient.inductionOn y
  clear y
  intro a
  use ⟦a - 1⟧
  unfold f6
  simp

end Chapter19.Exercise01

