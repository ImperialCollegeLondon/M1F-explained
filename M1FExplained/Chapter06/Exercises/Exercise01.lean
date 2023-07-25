import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Chapter06.Exercise01

open Complex

--Prove the following facts about complex numbers:
--Part (a) u+v = v+u for all u,v ∈ ℂ.
--Part (b) uv = vu for all u,v ∈ ℂ
--Part (c) (u+v) +w = (u+v) +w for all u,v,w ∈ ℂ.
--Part (d) u(v+w) = uv+uw for all u,v,w ∈ ℂ.
--Part (e) u(vw) = (uv)w for all u,v,w ∈ ℂ.

--All exercises share a common theme, so I will simplify solutions
--for (a), (c), and (d) and provide comprehensive solutions for (b) and (d).


--Prove the equality by separately expanding and rewriting
--both the imaginary and real parts.

theorem part_a : ∀ (u v : ℂ), u + v = v + u := by
  intro u v
  ext <;> simp <;> linarith

theorem part_b : ∀ (u v : ℂ), u * v = v * u := by
  intro u v
  ext
  · rw [mul_re, mul_re]
    linarith
  · rw [mul_im, mul_im]
    linarith

theorem part_c : ∀ (u v w: ℂ), (u + v) + w = u + (v + w) := by
  intro u v w
  ext <;> simp <;> linarith

theorem part_d : ∀ (u v w: ℂ), u * (v + w) = u * v + u * w := by
  intro u v w
  ext
  · rw [mul_re, add_re, mul_add, add_im, mul_add, sub_add_eq_sub_sub]
    rw [add_re, mul_re, mul_re, ← add_sub_assoc]
    linarith
  · rw [mul_im, add_im, mul_add, add_re, mul_add, ← add_assoc]
    rw [add_im, mul_im, mul_im, ← add_assoc]
    linarith

theorem part_e : ∀ (u v w: ℂ), u * (v * w) = (u * v) * w := by
  intro u v w
  ext <;> simp <;> linarith

end Chapter06.Exercise01
