/-
Let X, Y, Z be sets, and let f : X → Y and g : Y → Z be functions.
(a) Given that g ∘ f is onto, can you deduce that f is onto? Give a proof
or a counterexample.
(b) Given that g ∘ f is onto, can you deduce that g is onto?
(c) Given that g ∘ f is 1-1, can you deduce that f is 1-1?
(d) Given that g ∘ f is 1-1, can you deduce that g is 1-1?

! This file was ported from Lean 3 source module chapter19.exercises.exercise04
-/
import Mathbin.Tactic.Default

namespace Chapter19.Exercise04

open Function

-- so we can write `injective`/`surjective` instead of `function.injective`/`function.surjective`
-- For each of the parts below, if you think it's false then stick `¬` in front of it before you start proving it.
-- The below is for counterexamples
-- Let X be {a}
inductive X : Type
  | a : X

-- Let Y be {b,c}
inductive Y : Type
  | b : Y
  | c : Y

-- Let Z be {d}
inductive Z : Type
  | d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
  | X.a => Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

theorem parta : ¬∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Surjective (g ∘ f) → Surjective f :=
  by
  by_contra
  specialize h X Y Z f g
  have hgf : surjective (g ∘ f) := by
    rintro ⟨⟩
    use X.a
    rfl
  obtain ⟨⟨⟩, ⟨⟩⟩ := h hgf Y.c

theorem partb : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Surjective (g ∘ f) → Surjective g :=
  by
  intro X Y Z f g hgf b
  obtain ⟨a, hgf⟩ := hgf b
  exact ⟨f a, hgf⟩

theorem gf_injective : Injective (g ∘ f) :=
  by
  rintro ⟨⟩ ⟨⟩ _
  rfl

theorem partc : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Injective (g ∘ f) → Injective f :=
  by
  intro X Y Z f g hgf a b hf
  have hg : g (f a) = g (f b) := by rw [hf]
  exact hgf hg

theorem partd : ¬∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Injective (g ∘ f) → Injective g :=
  by
  by_contra
  specialize h X Y Z f g
  specialize h gf_injective
  have hy : g Y.b = g Y.c := by unfold g
  specialize h hy
  simpa using h

end Chapter19.Exercise04

