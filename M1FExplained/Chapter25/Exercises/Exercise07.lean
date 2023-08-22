import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Basic

abbrev set1 : Set ℂ :=  {1, -1, Complex.I, -Complex.I}
abbrev set2 : Set ℤ := {1, -1}
def D := set1 × set2

instance : One set1 where
  one := ⟨1, by tauto⟩

@[simp,norm_cast]
lemma set_one_coe_one : ((1 : set1) : ℂ) = 1 := rfl

instance : One set2 where
  one := ⟨1, by tauto⟩

lemma closed_mul (a b : set1) : (↑a : ℂ) * b ∈ set1 := by
  cases' a with a ha
  cases' b with b hb
  rcases ha with (rfl|rfl|rfl|rfl) <;> rcases hb with (rfl|rfl|rfl|rfl) <;> norm_num

instance : Mul set1 where
  mul a b := ⟨a.1 * b.1, closed_mul a b⟩

@[simp,norm_cast]  
lemma set1_coe_mul (a b : set1) : (a * b : set1) = (a : ℂ) * b := by rfl

lemma closed_mul2 (a b : set2) : (a : ℤ) * b ∈ set2 := by
  cases' a with a ha
  cases' b with b hb
  rcases ha with (rfl|rfl) <;> rcases hb with (rfl|rfl) <;> norm_num

instance : Mul set2 where
  mul a b := ⟨a * b, closed_mul2 a b⟩

@[norm_cast]
lemma set2_coe_mul (a b : set2): (a * b : set2) = (a : ℤ) * b := by rfl

lemma closed_pow (a : set1) (c : set2) : (a : ℂ) ^ (c : ℤ) ∈ set1 := by
  cases' a with a ha
  cases' c with b hc
  rcases ha with (rfl|rfl|rfl|rfl) <;> rcases hc with (rfl|rfl) <;> norm_num
  right
  right
  left
  rw [inv_neg]
  norm_num


noncomputable instance : HPow set1 set2 set1 where
  hPow a c := ⟨a.1 ^ c.1, closed_pow a c⟩   

@[simp,norm_cast]
lemma coe_pow (a : set1) (b : set2) : (a ^ b : set1) = (a : ℂ) ^ (b : ℤ) := by rfl

noncomputable instance : Mul D where 
  mul a b := ⟨a.1 * b.1 ^ a.2, a.2*b.2⟩

@[simp]
lemma mul_first (a b : D): (a * b).fst = a.1 * b.1 ^ a.2 := by rfl

@[simp]
lemma mul_snd (a b : D) : (a * b).snd = a.2 * b.2 := by rfl

lemma mul_assocD (a b c : D): a * b * c = a * (b * c) := by
  unfold D
  apply Prod.ext
  · repeat rw [mul_first]
    rw [mul_snd]
    ext1
    push_cast
    rw [mul_zpow, mul_comm (a.snd : ℤ), zpow_mul,mul_assoc]
  · repeat rw [mul_snd]
    ext
    push_cast
    rw [mul_assoc]

instance : One D := ⟨(1,1)⟩ 

@[simp]
lemma one_first : (1 : D).fst = 1 := by rfl

@[simp, norm_cast]
lemma set_two_coe_one : ((1 : set2) : ℤ) = 1 := rfl


lemma one_mulD (a : D) : 1 * a = a := by
  unfold D
  ext1
  · rw [mul_first]
    ext1
    push_cast
    simp
  · rw [mul_snd]
    ext
    push_cast
    simp

lemma mul_oneD (a : D) : a * 1 = a := by
  unfold D
  ext1
  · rw [mul_first]
    ext1
    push_cast
    simp
  · rw [mul_snd]
    ext
    push_cast
    simp

lemma neg_set2 (a : set2) : -a.1 ∈ set2 := by
  cases' a with a ha
  rcases ha with (rfl|rfl)  <;> norm_num

instance : Neg set2 where 
  neg a := ⟨-a.1, neg_set2 a⟩  

@[simp,norm_cast]
lemma neg_coe (a : set2) : (-a : set2) = -(a : ℤ) := by rfl


noncomputable instance : Inv D where
  inv a := ⟨a.1 ^ (-a.2), a.2⟩


@[simp]
lemma inv_first (a : D): (a⁻¹).fst = a.1 ^ (-a.2) := by rfl

@[simp]
lemma inv_snd (a : D) : (a⁻¹).snd = a.2 := by rfl

lemma set1_ne_zero (a : set1) : (a : ℂ) ≠ 0 := by
  cases' a with a ha
  rcases ha with (rfl|rfl|rfl|rfl)  <;> norm_num
  · intro h
    apply_fun Complex.im at h
    simp at h
  · intro h
    apply_fun Complex.im at h
    simp at h

lemma set.mul_self (a : set2) : (a : ℤ) * a = 1 := by
  cases' a with a ha
  rcases ha with (rfl|rfl)  <;> norm_num

lemma mul_left_invD (a : D): a⁻¹ * a = 1 := by
  unfold D
  ext1
  · simp only [Prod.fst_one]
    rw [mul_first]
    ext1
    push_cast
    rw [inv_first, inv_snd]
    push_cast
    simp only [zpow_neg, ne_eq]
    apply inv_mul_cancel
    apply zpow_ne_zero
    exact set1_ne_zero a.1
  · simp only [Prod.snd_one]
    rw [mul_snd, inv_snd]
    ext1
    push_cast
    apply set.mul_self

--- part i
noncomputable instance : Group D where
  mul_assoc := mul_assocD
  one_mul := one_mulD
  mul_one := mul_oneD
  mul_left_inv := mul_left_invD


noncomputable instance : Fintype set1 where
  elems := List.toFinset [(⟨1,by norm_num⟩ : set1),⟨-1,by norm_num⟩,⟨Complex.I,by norm_num⟩,⟨-Complex.I,by norm_num⟩]
  complete := by
    rintro ⟨x,(rfl|rfl|rfl|rfl)⟩ <;> simp

noncomputable instance : Fintype set1 := Set.fintypeInsert 1 _

noncomputable instance : Fintype set2 := Set.fintypeInsert 1 _

theorem card_eq_four : Fintype.card set1 = 4 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, neg_inj, Set.toFinset_insert, Set.toFinset_singleton,
    Finset.mem_insert, Finset.mem_singleton, forall_const, Fintype.card_ofFinset]
  iterate 3
    rw [Finset.card_insert_of_not_mem]
  all_goals
    simp only [Finset.mem_singleton, Finset.mem_insert, neg_inj, Complex.ext_iff]
    try norm_num

theorem card_eq_two : Fintype.card set2 = 2 := by rfl

noncomputable instance : Fintype D := by unfold D ; infer_instance

theorem card_eq_eight : Fintype.card D = 8 := by
  unfold D
  rw [Fintype.card_prod, card_eq_four, card_eq_two]

---part ii)

def i : set1 := ⟨Complex.I, by tauto⟩ 
def a : D := (i , 1)
def b : D := (1, -1)

lemma eq_pow_a_of_snd_eq_one (d : D) (h₀ : d.snd = 1) : ∃ n : ℕ, n ≤ 3 ∧ d = a^n := by
  cases' d with x y
  dsimp only at h₀ 
  subst h₀
  cases' x with x hx
  rcases hx with (rfl|rfl|rfl|rfl)
  · use 0
    rw [pow_zero]
    constructor
    norm_num
    exact rfl
  · use 2
    constructor
    norm_num
    apply Prod.ext
    · dsimp only
      rw [sq]
      rw [mul_first]
      unfold a
      dsimp only
      ext1
      push_cast
      unfold i
      dsimp only
      norm_num
    · dsimp only
      rw [sq]
      rw [mul_snd]
      unfold a
      dsimp only
      ext1
      push_cast
  · use 1
    constructor
    norm_num
    apply Prod.ext
    · dsimp only
      rw [pow_one]
      unfold a
      dsimp only
      ext1
      push_cast
      unfold i
      dsimp
    · dsimp only
      rw [pow_one]
      unfold a
      dsimp
  · use 3
    constructor
    norm_num
    apply Prod.ext
    · dsimp only
      rw [pow_succ,sq]
      rw [mul_first]
      unfold a
      dsimp only
      ext1
      push_cast
      unfold i
      dsimp
      norm_num
    · dsimp only
      rw [pow_succ,sq]
      rw [mul_snd]
      unfold a
      dsimp only
      ext1
      push_cast


lemma b_self_inv : b * b = 1 := by
  apply Prod.ext
  · dsimp only
    unfold b
    dsimp only
    ext1
    push_cast
    norm_num
  · dsimp only
    unfold b
    dsimp only
    ext1
    push_cast


lemma bar (d : D) (h₀ : d.snd = -1) : ∃ d' : D, d'.snd = 1 ∧ d = d' * b := by
  use d * b
  constructor
  unfold b
  dsimp only [mul_snd]
  rw [h₀]
  norm_num
  rw [mul_assoc, b_self_inv, mul_one]

lemma a_four: a^4 = 1 := by 
  apply Prod.ext
  · dsimp only [Prod.fst_one]
    unfold a
    repeat rw [pow_succ]
    ext1
    push_cast
    dsimp only [mul_first, set1_coe_mul, coe_pow, set_two_coe_one]
    norm_num
    unfold i
    norm_num
  · dsimp only [Prod.snd_one]
    unfold a
    ext1
    push_cast


lemma set2.eq_one_or_neg_one  (a : set2) : a = 1 ∨ a = -1 := by
  cases' a with a ha
  rcases ha with (rfl|rfl)
  · left
    rfl
  · right
    rfl

theorem part_ii : Set.univ = {1, a, a ^ 2, a ^ 3, b, a * b, a ^ 2 * b, a ^ 3 * b} := by
  ext g
  simp
  cases' set2.eq_one_or_neg_one g.snd with h h
  · have := eq_pow_a_of_snd_eq_one g h
    rcases this with ⟨n,hn₁,rfl⟩
    interval_cases n
    · simp
    . simp
    . tauto
    · tauto
  · have := bar g h
    rcases this with ⟨z,hz₁,rfl⟩
    have := eq_pow_a_of_snd_eq_one z hz₁
    rcases this with ⟨n,hn₁,rfl⟩
    interval_cases n
    · simp
    . simp
    . tauto
    · tauto
