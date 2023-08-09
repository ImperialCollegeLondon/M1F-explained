import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Basic

def set1 : Set ℂ :=  {1, -1,Complex.I, -Complex.I}
def set2 : Set ℂ := {1, -1}
def D := set1.prod set2

--- part i
noncomputable instance : Group mygroup where
  mul a b:= sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv z := sorry
  mul_left_inv := sorry