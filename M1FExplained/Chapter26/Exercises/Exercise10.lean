import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Modeq

/-
a) Use Proposition 26.7 to find the remainder when 3798 is divided by 24.
(b) True or false: if a, n are coprime positive integers and a^2 ≡ 1 mod n, then a ≡ ±1 mod n.
(c) True or false: if a, m, n are positive integers such that hcf(a, n) = hcf(m,φ (n)) = 1, then
                            a^m ≡ 1 mod n ⇒ a ≡ 1 mod n.
-/

--- part a)
example :  37^98 ≡ 1 [MOD 24] := by norm_num 

--- part b)
example (a n : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : a.coprime n): ¬ (a^2 ≡ 1 [MOD n] → (a ≡  1 [MOD n])
∨ (a ≡ n-1 [MOD n])) := by
  intro h
  have : 4^2 ≡ 1 [MOD 15] := by norm_num 
  have hh: 4 ≡ 1 [MOD 15] ∨ 4 ≡ 15-1 [MOD 15]:= by 
    
    sorry
  rcases this with ⟨a,b⟩
  norm_num at hh

