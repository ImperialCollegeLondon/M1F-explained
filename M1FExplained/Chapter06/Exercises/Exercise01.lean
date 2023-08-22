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
--for (c), (d), and (e) and provide comprehensive solutions for (a) and (b).


--Prove the equality by expanding the definition of complex number 
--and rewriting both the imaginary and real parts.

theorem part_a : ∀ (u v : ℂ), u + v = v + u := by
  intro u v
  ext
  · calc
      (u + v).re = v.re + u.re := by
        rw [add_re, add_comm]
      _ = (v + u).re := by
        rw [← add_re]
  · calc
      (u + v).im = v.im + u.im := by
        rw [add_im, add_comm]
      _ = (v + u).im := by
        rw [← add_im]

theorem part_b : ∀ (u v : ℂ), u * v = v * u := by
  intro u v
  ext
  · calc
      (u * v).re = v.re * u.re - v.im * u.im:= by 
        rw[mul_re u v, mul_comm, mul_comm v.im]
      _ = (v * u).re := by
        rw[← mul_re]
  · calc
      (u * v).im = v.re * u.im + v.im * u.re:= by 
        rw[mul_im u v, add_comm, mul_comm, mul_comm u.re]
      _ = (v * u).im := by
        rw[← mul_im]


theorem part_c : ∀ (u v w: ℂ), (u + v) + w = u + (v + w) := by
  intro u v w
  ext <;> simp <;> linarith

theorem part_d : ∀ (u v w: ℂ), u * (v + w) = u * v + u * w := by
  intro u v w
  ext <;> simp <;> linarith

theorem part_e : ∀ (u v w: ℂ), u * (v * w) = (u * v) * w := by
  intro u v w
  ext <;> simp <;> linarith

end Chapter06.Exercise01
