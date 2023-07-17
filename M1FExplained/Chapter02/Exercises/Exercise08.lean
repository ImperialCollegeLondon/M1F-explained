import Mathlib.Tactic

namespace Chapter02.Exercise08

inductive Colour : Type
  | red : Colour
  | blue : Colour
  | green : Colour

def horrify : ℕ × ℕ × ℕ → Colour → ℕ × ℕ × ℕ
  | (r, b + 1, g + 1), Colour.red => (r + 2, b, g)
  | (r + 1, b, g + 1), Colour.blue => (r, b + 2, g)
  | (r + 1, b + 1, g), Colour.green => (r, b, g + 2)
  | (r, b, g), _ => (r, b, g)

def _root_.Nat.induction_on {motive : ℕ → Prop} (zero : motive (0 : ℕ)) 
  (succ : (n : ℕ) → motive n → motive (n + 1)) (n : ℕ) : motive n := Nat.rec (motive := motive) zero succ n

def _root_.Nat.cases_on {motive : ℕ → Prop} (zero : motive (0 : ℕ)) 
  (succ : (n : ℕ) → motive (n + 1)) (n : ℕ) : motive n := Nat.induction_on zero (fun _ _ ↦ succ _) n

--set_option trace.Elab.definition true in
/-- Critic Ivor Smallbrain is watching the horror movie Salamanders on a
Desert Island. In the film, there are 30 salamanders living on a desert
island: 15 are red, 7 blue and 8 green. When two of a different colour
meet, horrifyingly they both change into the third colour. (For example,
if a red and a green meet, they both become blue.) When two of the same
colour meet, they change into both of the other colours. (For example, if
two reds meet, one becomes green and one becomes blue.) It is all quite
terrifying.

In between being horrified and terrified, Ivor idly wonders whether it
could ever happen that at some instant in the future, all of the salaman-
ders would be red. It turns out that this would never happen. -/
theorem mod_invar (li : ℕ × ℕ × ℕ) (t : Colour) :
    2 * (horrify li t).2.1 + (horrify li t).2.2 ≡ 2 * li.2.1 + li.2.2 [MOD 3] := by
  have h : (4 : ℕ) = 1 + 3; rfl
  rcases li with ⟨a, b, c⟩
  dsimp
  cases t <;> apply a.cases_on <;> apply b.cases_on <;> apply c.cases_on <;> 
    simp [horrify, Nat.ModEq] <;>
    simp <;>
    ring_nf <;>
    try rw [h, ← add_assoc (G := ℕ), Nat.add_mod_right] <;>
    try rw [h, ← add_assoc (G := ℕ), Nat.add_mod_right] <;>
    try rw [h, ← add_assoc (G := ℕ), Nat.add_mod_right] <;>
    try rw [h, ← add_assoc (G := ℕ), Nat.add_mod_right] <;>
    simp_all <;>
    simp [← add_assoc, Nat.add_mod_right] <;>
    simp (config := {contextual := true}) only [add_assoc, Nat.add_mod_left]
  · intros
    simp_rw [add_assoc, Nat.add_mod_left]
  · intros
    simp_rw [add_assoc, Nat.add_mod_left]
  · intros; simp [show 4 = 3 + 1 from rfl, add_assoc, Nat.add_mod_left]
  · intros
    simp_rw [Nat.succ_eq_add_one, add_assoc, Nat.add_mod_left]
    ring_nf
    simp only [show 6 = 3 + 3 from rfl, add_assoc, Nat.add_mod_left]
  · intro n; simp
  · intros a b; simp [Nat.succ_eq_add_one]
    ring_nf
  done

theorem list_invar (l : List Colour) (li : ℕ × ℕ × ℕ) :
    2 * (List.foldl horrify li l).2.1 + (List.foldl horrify li l).2.2 ≡ 2 * li.2.1 + li.2.2 [MOD 3] := by
  induction' l using List.reverseRecOn with x hx hm
  simp [List.foldl_nil, horrify]; rfl
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h := mod_invar (List.foldl horrify li x) hx
  unfold Nat.ModEq at *
  rwa [hm] at h 

theorem salamander : ¬∃ l : List Colour, List.foldl horrify (15, 7, 8) l = (30, 0, 0) := by
  rintro ⟨l, hl⟩
  have t := list_invar l (15, 7, 8)
  rw [hl] at t 
  simp only [MulZeroClass.mul_zero, add_zero] at t 

end Chapter02.Exercise08

