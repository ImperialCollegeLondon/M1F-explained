/-
5. Use the Pigeonhole Principle to prove the following statements involv-
ing a positive integer n:
(a) In any set of 6 integers, there must be two whose difference is divisible by 5.
(b) In any set of n + 1 integers, there must be two whose difference is
divisible by n.
(c) Given any n integers a₁, a₂,..., aₙ, there is a non-empty subset of
these whose sum is divisible by n. (Hint: Consider the integers 0,a₁ ,
a₁ + a₂ ,..., a₁ +...+aₙ and use (b).)
(d) Given any set S consisting of ten distinct integers between 1 and 50,
there are two different 5-element subsets of S with the same sum.
(e) Given any set T consisting of nine distinct integers between 1 and
50, there are two disjoint subsets of T with the same sum.
(f) In any set of 101 integers chosen from the set {1, 2, . . . , 200}, there
must be two integers such that one divides the other.

! This file was ported from Lean 3 source module chapter19.exercises.exercise05
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.Int.Parity
import Mathlib.Data.Nat.Factorization.Basic

namespace Chapter19.Exercise05

open Function

theorem parta (S : Finset ℤ) (hS : S.card = 6) :
    ∃ (a : _) (_ : a ∈ S) (b : _) (_ : b ∈ S), a ≠ b ∧ (5 : ℤ) ∣ a - b :=
  by
  let T : Finset ℤ := Finset.Ico 0 5
  have hfT : ∀ z : ℤ, z ∈ S → z % 5 ∈ T := by
    intro z _
    simp only [Finset.mem_Ico]
    constructor
    apply Int.emod_nonneg
    norm_num
    apply Int.emod_lt
    norm_num
  have hST : T.card * 1 < S.card :=
    by
    simp only [hS, Int.card_Ico, tsub_zero, mul_one]
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hfT hST
  dsimp at this 
  rcases this with ⟨y, _, H⟩
  rw [Finset.one_lt_card] at H 
  rcases H with ⟨a, ha, b, hb, H⟩
  simp only [Finset.mem_filter] at ha hb 
  use a, ha.1, b, hb.1, H
  apply Int.ModEq.dvd
  change b % 5 = a % 5
  rw [hb.2, ha.2]

theorem partb (n : ℕ) (hn : 0 < n) (S : Finset ℤ) (hS : S.card = n + 1) :
    ∃ (a : _) (_ : a ∈ S) (b : _) (_ : b ∈ S), a ≠ b ∧ (n : ℤ) ∣ a - b :=
  by
  let f : ℤ → ℤ := fun z => z % n
  let T : Finset ℤ := Finset.Ico 0 n
  have hfT : ∀ z : ℤ, z ∈ S → f z ∈ T := by
    intro z _
    simp only [Finset.mem_Ico]
    constructor
    apply Int.emod_nonneg
    linarith
    convert Int.emod_lt _ _
    simp only [Nat.abs_cast]
    linarith
  have hST : T.card * 1 < S.card := by
    simp only [hS, Int.card_Ico, tsub_zero, Int.toNat_coe_nat, mul_one, lt_add_iff_pos_right,
      Nat.lt_one_iff]
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hfT hST
  dsimp at this 
  rcases this with ⟨y, _, H⟩
  rw [Finset.one_lt_card] at H 
  rcases H with ⟨a, ha, b, hb, H⟩
  simp at ha hb 
  use a, ha.1, b, hb.1, H
  apply Int.ModEq.dvd
  change b % n = a % n
  rw [hb.2, ha.2]

-- A stronger version of part b which should be easier to use
-- (the point is that f might not be injective on s)
theorem partb' {ι : Type _} {s : Finset ι} (f : ι → ℤ) (_ : s.Nonempty) {n : ℕ} (hn : 0 < n)
    (hs' : n < s.card) : ∃ (a : _) (_ : a ∈ s) (b : _) (_ : b ∈ s), a ≠ b ∧ (n : ℤ) ∣ f a - f b :=
  by
  let f' : ι → ℤ := fun z => f z % n
  let T : Finset ℤ := Finset.Ico 0 n
  have hfT : ∀ z : ι, z ∈ s → f' z ∈ T := by
    intro z _
    simp only [Finset.mem_Ico]
    have hn' : (n : ℤ) ≠ 0 := by norm_cast; exact hn.ne'
    constructor
    · exact Int.emod_nonneg _ hn'
    · convert Int.emod_lt _ hn'
      simp only [Nat.abs_cast]
  have hST : T.card * 1 < s.card := by simp [hs']
  obtain ⟨y, _, hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hfT hST
  rw [Finset.one_lt_card_iff] at hcard 
  rcases hcard with ⟨a, b, ha, hb, hab⟩
  rw [Finset.mem_filter] at ha hb 
  refine' ⟨a, ha.1, b, hb.1, hab, _⟩
  dsimp at ha hb 
  apply Int.ModEq.dvd
  change f b % n = f a % n
  rw [hb.2, ha.2]

open scoped BigOperators

theorem Finset.sum_Ico {M : Type _} [AddCommGroup M] {a b : ℕ} (h : a ≤ b) (f : ℕ → M) :
    ∑ i in Finset.Ico a b, f i = ∑ j in Finset.range b, f j - ∑ j in Finset.range a, f j :=
  by
  rw [eq_sub_iff_add_eq]
  rw [← Finset.sum_union]
  · apply Finset.sum_congr _ fun x _ => rfl
    rw [Finset.range_eq_Ico, Finset.union_comm, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) h]
  · rintro x h1 h2
    intro y hy
    specialize h1 hy
    specialize h2 hy
    rw [Finset.mem_Ico] at h1 
    rw [Finset.mem_range] at h2 
    rcases h1 with ⟨h1, _⟩
    exact False.elim (h1.not_lt h2)

theorem partc (n : ℕ) (hn : 0 < n) (f : ℕ → ℤ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.Nonempty ∧ (n : ℤ) ∣ ∑ i in S, f i :=
  by
  --  {ι : Type*} {s : finset ι} (f : ι → ℤ) (hs : s.nonempty) {n : ℕ} (hn : 0 < n)
  -- (hs' : n < s.card): ∃ a b ∈ s, a ≠ b ∧ (n : ℤ) ∣ f a - f b := sorry
  rcases partb' (fun t => ∑ i in Finset.range t, f i) (@Finset.nonempty_range_succ n) hn
      (by simp) with
    ⟨a, ha, b, hb, hab, hn⟩
  rw [Finset.mem_range_succ_iff] at ha hb 
  rw [ne_iff_lt_or_gt] at hab 
  rcases hab with (hab | (hab : b < a))
  · use Finset.Ico a b
    refine' ⟨_, _, _⟩
    · rw [Finset.range_eq_Ico, Finset.Ico_subset_Ico_iff hab]
      exact ⟨zero_le a, hb⟩
    · rwa [Finset.nonempty_Ico]
    · rwa [Finset.sum_Ico hab.le, ← dvd_neg, neg_sub]
  · -- b < a case
    use Finset.Ico b a
    refine' ⟨_, _, _⟩
    · rw [Finset.range_eq_Ico, Finset.Ico_subset_Ico_iff hab]
      exact ⟨zero_le b, ha⟩
    · rwa [Finset.nonempty_Ico]
    · rwa [Finset.sum_Ico hab.le]

-- should be in mathlib maybe? (thanks Eric Rodriguez)
def sum_le_max (S : Finset ℤ) (x : ℤ) (hS' : ∀ s ∈ S, s ≤ x) :
    ∑ i in S, i ≤ ∑ i in Finset.Ioc (x - Finset.card S) x, i :=
  by
  induction' h : Finset.card S with k ih generalizing S x
  · obtain rfl := Finset.card_eq_zero.mp h; simp
  have hSn : 0 < S.card := h.symm ▸ k.succ_pos
  replace hSn : S.Nonempty := Finset.card_pos.mp hSn
  specialize ih (S.erase (S.max' hSn)) (x - 1) (fun s hs => _) _
  · rw [← Int.pred, ← Int.pred_eq_pred, Order.le_pred_iff]
    obtain ⟨_, _⟩ := Finset.mem_erase.1 hs
    exact (S.lt_max'_of_mem_erase_max' hSn hs).trans_le (hS' _ <| S.max'_mem hSn)
  · simpa [h] using Finset.card_erase_of_mem (S.max'_mem hSn)
  have : x - 1 - k = x - k.succ := by
    rw [sub_sub, sub_right_inj]
    simp only [add_comm, Nat.cast_succ]
  rw [this] at ih 
  have hSm : S.max' hSn ≤ x := hS' _ (S.max'_mem hSn)
  replace ih := add_le_add ih hSm
  suffices Finset.Ioc (x - k.succ) (x - 1) = (Finset.Ioc (x - k.succ) x).erase x
    by
    rwa [Finset.sum_erase_add _ _ <| S.max'_mem hSn, this, Finset.sum_erase_add] at ih 
    simp only [Finset.right_mem_Ioc, sub_lt_self_iff]
    exact Nat.cast_pos.mpr k.succ_pos
  ext
  simp only [Nat.cast_succ, Finset.mem_Ioc, Finset.Ioc_erase_right, Finset.mem_Ioo,
    and_congr_right_iff]
  rintro -
  rw [← Int.pred, ← Int.pred_eq_pred, Order.le_pred_iff]

-- should also be in mathlib maybe?
def min_le_sum (S : Finset ℤ) (x : ℤ) (hS' : ∀ s ∈ S, x ≤ s) :
    ∑ i in Finset.Ico x (x + Finset.card S), i ≤ ∑ i in S, i :=
  by
  have := sum_le_max (Finset.image (fun i => -i) S) (-x) ?_; swap
  · intro s hs
    rw [Finset.mem_image] at hs 
    rcases hs with ⟨t, ht, rfl⟩
    exact neg_le_neg (hS' t ht)
  rw [← neg_le_neg_iff]
  have Scard : (Finset.image Neg.neg S).card = S.card :=
    by
    rw [Finset.card_image_iff]
    intro x _ y _
    exact neg_inj.1
  convert this
  · rw [Finset.sum_image]
    symm
    apply Finset.sum_neg_distrib
    intro x _ y _ h
    rwa [neg_inj] at h 
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_bij fun (a : ℤ) _ => -a
    · intro a ha
      simp only [Finset.mem_Ioc, neg_le_neg_iff]
      rw [Finset.mem_Ico] at ha 
      rw [Scard]
      cases ha
      constructor <;> linarith
    · simp only [eq_self_iff_true, imp_true_iff]
    · simp only [neg_inj, imp_self, imp_true_iff, forall_const]
    · rw [Scard]
      intro b hb
      refine' ⟨-b, _, _⟩
      · simp only [Finset.mem_Ico, Finset.mem_Ioc] at hb ⊢
        cases hb; constructor <;> linarith
      · simp only [neg_neg]

theorem partd (S : Finset ℤ) (hS : ∀ s ∈ S, (1 : ℤ) ≤ s ∧ s ≤ 50) (hScard : S.card = 10) :
    ∃ A B : Finset ℤ, A.card = 5 ∧ B.card = 5 ∧ A ≠ B ∧ A ≤ S ∧ B ≤ S ∧ ∑ i in A, i = ∑ j in B, j :=
  by
  -- consider possibilities for subset of S with card 5
  let P := Finset.powersetLen 5 S
  -- consider possibilities for sum
  let F := Finset.Icc (15 : ℤ) 240
  have hFP : F.card * 1 < P.card :=
    by
    simp only [Finset.card_powersetLen 5 S, hScard, Int.card_Icc, mul_one]
  let g : Finset ℤ → ℤ := fun x => ∑ i in x, i
  have hg : ∀ p : Finset ℤ, p ∈ P → g p ∈ F :=
    by
    intro p hp
    simp only [Finset.mem_Icc]
    rw [Finset.mem_powersetLen] at hp 
    constructor
    · convert min_le_sum p 1 fun s hs => (hS s (hp.1 hs)).1
      rw [hp.2]
      rfl
    · convert sum_le_max p 50 fun s hs => (hS s (hp.1 hs)).2
      rw [hp.2]
      rfl
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hFP
  dsimp at this 
  rcases this with ⟨y, _, hy2⟩
  rw [Finset.one_lt_card] at hy2 
  rcases hy2 with ⟨A, hA, B, hB, hAB⟩
  rw [Finset.mem_filter] at hA hB 
  refine' ⟨A, B, _⟩
  rw [Finset.mem_powersetLen] at hA hB 
  simp [hAB, hA.1, hB.1]
  rw [hA.2, hB.2]

theorem parte (T : Finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 50) (hTcard : T.card = 9) :
    ∃ A B : Finset ℤ, A ≤ T ∧ B ≤ T ∧ Disjoint A B ∧ ∑ i in A, i = ∑ j in B, j :=
  by
  -- as long as we can find two non-empty sets A, B of the same sum, we can find two disjoint set by A\B and B\A
  suffices h : ∃ C D : Finset ℤ, C ≤ T ∧ D ≤ T ∧ C ≠ D ∧ ∑ i in C, i = ∑ j in D, j
  · -- let A = C - (C ∩ D), B = D - (C ∩ D),
    rcases h with ⟨C, D, hC, hD, _, h⟩
    let A : Finset ℤ := C \ D
    let B : Finset ℤ := D \ C
    refine' ⟨A, B, _⟩
    have hAC : A ≤ C; apply Finset.sdiff_subset
    have hBD : B ≤ D; apply Finset.sdiff_subset
    have hA : A ≤ T := le_trans hAC hC
    have hB : B ≤ T := le_trans hBD hD
    refine' ⟨hA, hB, disjoint_sdiff_sdiff, _⟩
    let X := C ∩ D
    suffices : ∑ i : ℤ in A, i + ∑ x : ℤ in X, x = ∑ j : ℤ in B, j + ∑ x : ℤ in X, x
    exact (add_left_inj (∑ x : ℤ in X, x)).mp this
    convert h
    · suffices C = A ∪ X by
        rw [this, ← Finset.sum_union]
        exact Finset.disjoint_sdiff_inter C D
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, ← and_or_left]
      tauto
    · suffices D = B ∪ X by
        rw [this, ← Finset.sum_union]
        change Disjoint B (C ∩ D)
        rw [Finset.inter_comm C D]
        exact Finset.disjoint_sdiff_inter D C
      · ext x
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, ← and_or_left]
        tauto
  · -- consider powerset of T
    let P := Finset.powerset T
    let F := Finset.Icc (0 : ℤ) 414
    have hPF : F.card * 1 < P.card :=
      by
      simp [Nat.card_Icc, Finset.card_powerset, hTcard]
    -- find a map from P to F by summing elements in P
    let g : Finset ℤ → ℤ := fun x => ∑ i in x, i
    have hg : ∀ p : Finset ℤ, p ∈ P → g p ∈ F :=
      by
      intro p hp
      simp
      rw [Finset.mem_powerset] at hp 
      constructor
      · apply Finset.sum_nonneg
        intro i hi
        exact le_trans zero_le_one (hT i (hp hi)).1
      · trans ∑ i in T, i
        · apply Finset.sum_le_sum_of_subset_of_nonneg hp
          intro i hi _
          exact le_trans zero_le_one (hT i hi).1
        · convert sum_le_max T 50 _
          · rw [hTcard]; rfl
          · intro i hi; exact (hT i hi).2
    have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hPF
    dsimp at this 
    rcases this with ⟨y, _, hy2⟩
    rw [Finset.one_lt_card] at hy2 
    rcases hy2 with ⟨C, hC, D, hD, hCD⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hC hD 
    refine' ⟨C, D, hC.1, hD.1, hCD, _⟩
    rw [hC.2, hD.2]

theorem Nat.ord_compl_eq_dvd (a b : ℕ) (h : ord_compl[2] a = ord_compl[2] b) (ha : 0 < a)
    (hab : a < b) : a ∣ b :=
  by
  -- if a = 2^k1 * p, b = 2^k2 * p
  set k1 : ℕ := a.factorization 2
  set k2 : ℕ := b.factorization 2
  rw [dvd_iff_exists_eq_mul_left]
  -- c = 2^ (k2 - k1)
  use 2 ^ (k2 - k1)
  have h02 : 0 < 2 := by norm_num
  -- because of natural division is involved, we need divisibility
  have had := Nat.ord_proj_dvd a 2
  have hbd := Nat.ord_proj_dvd b 2
  have haf := pow_pos h02 k1
  have hab : k1 ≤ k2 := by
    by_contra hc
    push_neg at hc 
    have hc' : 2 ^ k2 < 2 ^ k1 := by
      rw [pow_lt_pow_iff]
      exact hc
      norm_num
    have hak : 0 < a / 2 ^ k1 := by
      apply Nat.div_pos
      apply Nat.ord_proj_le
      exact ne_of_gt ha
      exact haf
    suffices b < a by linarith
    · have hc'' : 2 ^ k2 * (b / 2 ^ k2) < 2 ^ k1 * (a / 2 ^ k1) := by 
        rw [← h];
        apply mul_lt_mul_of_pos_right hc' hak
      rw [mul_comm (2 ^ k2) (b / 2 ^ k2), Nat.div_mul_cancel] at hc'' 
      swap; exact hbd
      rw [mul_comm (2 ^ k1) (a / 2 ^ k1), Nat.div_mul_cancel] at hc'' 
      exact hc''
      exact had
  have := Nat.pow_div hab h02
  rw [← this]
  -- again we need divisibility to proceed
  have hkd := pow_dvd_pow 2 hab
  rw [mul_comm, ← Nat.mul_div_assoc _ hkd, mul_comm a (2 ^ k2), Nat.mul_div_assoc]
  swap; exact had
  rw [h, mul_comm, Nat.div_mul_cancel hbd]

theorem partf (T : Finset ℕ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 200) (hTcard : T.card = 101) :
    ∃ a b : ℕ, a ∈ T ∧ b ∈ T ∧ a ≠ b ∧ a ∣ b :=
  by
  -- claim : every t can be written as 2^k * q for which q is odd, using ord_compl[2] t
  let Q : Finset ℕ := (Finset.Icc 1 200).filter Odd
  have hQcard : Q.card = 100 :=
    by
    -- Show that it equals (finset.Iio 100).map \<\la n, 2 * n + 1, proof_of_injectivity_here\>
    have hQ :
      Q =
        (Finset.Iio 100).map
          ⟨fun n => 2 * n + 1, by
            intro a b hab
            simpa [add_left_inj, mul_eq_mul_left_iff, bit0_eq_zero, Nat.one_ne_zero,
              or_false_iff] using hab⟩ :=
      by
      dsimp
      rw [le_antisymm_iff]
      constructor
      · intro x hx
        simp only [Finset.mem_map, Finset.mem_Iio, Function.Embedding.coeFn_mk, exists_prop,
          Nat.one_le_cast, Finset.mem_filter, Finset.mem_Icc, Nat.odd_iff_not_even] at hx ⊢
        refine' ⟨(x - 1) / 2, _, _⟩
        · rcases hx with ⟨⟨h1, h2⟩, h3⟩
          zify at h2 ⊢
          rw [Int.ediv_lt_iff_lt_mul]
          rw [Nat.cast_sub]
          simp
          linarith
          linarith
          norm_num
        · rcases hx with ⟨⟨h1, h2⟩, h3⟩
          rw [← Nat.odd_iff_not_even] at h3 
          unfold Odd at h3 
          rcases h3 with ⟨k, rfl⟩
          simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero, mul_eq_zero, false_or,
            add_tsub_cancel_right, zero_lt_two, Nat.mul_div_right]
      · intro x hx
        simp only [Finset.mem_map, Finset.mem_Iio, Function.Embedding.coeFn_mk, exists_prop,
          Nat.one_le_cast, Finset.mem_filter, Finset.mem_Icc, Nat.odd_iff_not_even] at hx ⊢
        rcases hx with ⟨a, ⟨h1, h2⟩⟩
        refine' ⟨⟨_, _⟩, _⟩
        · rw [← h2]
          linarith
        · rw [← h2]
          linarith
        · intro h
          rw [Nat.even_iff, ← h2, Nat.mul_comm, Nat.mul_add_mod a 2 1] at h 
          simp [Nat.one_mod, Nat.one_ne_zero] at h
    rw [hQ]
    simp only [Nat.card_Iio, Finset.card_map]
  have hTO : Q.card * 1 < T.card := by rw [hQcard, hTcard]; norm_num
  -- find a map from T to Q, by considering corresponding 'q'
  let f : ℕ → ℕ := fun z => ord_compl[2] z
  have f_def (z : ℕ) : f z = ord_compl[2] z := rfl
  have hf : ∀ t ∈ T, f t ∈ Q := by
    intro t ht
    change ord_compl[2] t ∈ Q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.odd_iff_not_even]
    have ht0 : t ≠ 0 := by
      specialize hT t ht
      cases' hT with hT1 hT2
      linarith
    refine' ⟨⟨_, _⟩, _⟩
    · rw [Nat.one_le_div_iff]
      · apply Nat.ord_proj_le 2 ht0
      · exact Nat.ord_proj_pos t 2
    · apply Nat.div_le_of_le_mul
      have h1 := Nat.ord_proj_pos t 2
      rw [← Nat.succ_le_iff] at h1 
      exact le_mul_of_one_le_of_le h1 (hT t ht).2
    · simp only [even_iff_two_dvd, Nat.not_dvd_ord_compl Nat.prime_two ht0, not_false_iff]
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hTO
  dsimp at this 
  rcases this with ⟨y, hy1, hy2⟩
  rw [Finset.one_lt_card] at hy2 
  rcases hy2 with ⟨a, ha, b, hb, hab⟩
  by_cases a < b
  · refine' ⟨a, b, _⟩
    simp only [hab, Ne.def, not_false_iff, true_and_iff]
    rw [Finset.mem_filter] at ha hb 
    simp only [ha.1, hb.1, true_and_iff]
    have ha0 : 0 < a := by
      specialize hT a ha.1
      cases' hT with h1 h2
      linarith
    suffices f a = f b by
      apply Nat.ord_compl_eq_dvd
      exact this
      exact ha0
      exact h
    · refine ha.2.trans ?_
      rw [f_def, hb.2]
  · have h2 : b < a := by push_neg at h; exact Nat.lt_of_le_of_ne h hab.symm
    refine' ⟨b, a, _⟩
    simp only [Ne.symm hab, Ne.def, not_false_iff, true_and_iff]
    rw [Finset.mem_filter] at ha hb 
    simp only [ha.1, hb.1, true_and_iff]
    have hb0 : 0 < b := by
      specialize hT b hb.1
      cases' hT with h1 h2
      linarith
    suffices f b = f a by
      apply Nat.ord_compl_eq_dvd
      exact this
      exact hb0
      exact h2
    · rw [f_def, f_def, ha.2, hb.2]

end Chapter19.Exercise05
