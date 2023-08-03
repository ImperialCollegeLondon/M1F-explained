import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic

/- a) Show that if G is an abelian group and n is an integer, then (a * b)^n = a^n * b^n for all a, b, ∈ G.
   b) Give an example of a group G, an integer n, and elements a, b ∈ G such that (a * b)^n ≠ a^n * b^n. -/


--- part a)

example {G : Type u_1} [CommGroup G] (a b : G) (n : ℕ) : (a*b)^n = a^n*b^n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero, pow_zero, mul_one]
  rw [Nat.succ_eq_add_one,pow_add,ih, mul_pow,mul_comm (a^1), mul_assoc, ← mul_assoc (b^n), ← pow_add,
    mul_comm (b^(n+1)), ← mul_assoc, ← pow_add]


--- part b)
/- Here G = S_3, n = 1, a = (1 2) and b = (2 3) -/

example : ∃ (a b : Equiv.Perm (Fin 3)),  (a * b) i ≠ (b * a) i := by
  use Equiv.swap 0 1
  use Equiv.swap 1 2
  intro h
  rcases i with  ⟨i, i_is_lt⟩
  sorry

