module

public import PaperP1.Analysis.RelativeRamareRemainder
public import PaperP1.Analysis.NarrowPrimeBands

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowRectangleWeight
open Finset PaperP1 PrimeDivisorWeights
open scoped Classical

def test (X H p m : ℕ) : Prop :=
  (X : ℝ) ≤ (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) ∧
    (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) < 2*(X : ℝ)

def weight (X H : ℕ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ factors P n, if test X H p (n/p) then 1/((count P (n/p)+1 : ℕ) : ℝ) else 0

def boundary (X H : ℕ) : Finset ℕ :=
  (Ico X (4*X)).filter (fun n ↦ (n : ℝ) < NarrowPrimeBands.growth H*(X : ℝ) ∨
    2*(X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < 2*NarrowPrimeBands.growth H*(X : ℝ))

theorem weight_nonneg (X H : ℕ) (P : Finset ℕ) (n : ℕ) : 0 ≤ weight X H P n := by
  apply sum_nonneg
  intro p hp
  split_ifs <;> positivity

theorem weight_le_full (X H : ℕ) (P : Finset ℕ) (n : ℕ) : weight X H P n ≤ RamareWeights.weight P n := by
  apply sum_le_sum
  intro p hp
  split_ifs
  · exact le_rfl
  · positivity

theorem weight_le_one (X H : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    weight X H P n ≤ 1 := (weight_le_full X H P n).trans (RamareWeights.weight_le_one P hP n)

theorem test_product_bounds (X H p m : ℕ) (hX : 0 < X) (hH : 2 ≤ H) (hp : 1 ≤ p)
    (ht : test X H p m) : (X : ℝ) ≤ ((p*m : ℕ) : ℝ) ∧
      ((p*m : ℕ) : ℝ) < 2*NarrowPrimeBands.growth H*(X : ℝ) := by
  have hab := NarrowPrimeBands.index_bounds H p (by omega) hp
  have hg : 0 < NarrowPrimeBands.growth H := by unfold NarrowPrimeBands.growth; positivity
  have hm : (0 : ℝ) < m := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hu := NarrowPrimeBands.anchor_pos H (NarrowPrimeBands.index H p)
    have hh := ht.1
    by_contra hh'
    have hm0 : (m : ℝ)=0 := le_antisymm (le_of_not_gt hh') (Nat.cast_nonneg m)
    rw [hm0,zero_mul] at hh
    linarith
  constructor
  · rw [Nat.cast_mul]
    exact ht.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hab.1 hm.le])
  · rw [Nat.cast_mul]
    calc
      (p : ℝ)*(m : ℝ) < NarrowPrimeBands.growth H*
          ((m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p)) := by
        have hh := mul_lt_mul_of_pos_left hab.2 hm
        nlinarith only [hh]
      _ < NarrowPrimeBands.growth H*(2*(X : ℝ)) := mul_lt_mul_of_pos_left ht.2 hg
      _ = _ := by ring

theorem test_middle (X H p m : ℕ) (hH : 2 ≤ H) (hp : 1 ≤ p)
    (hl : NarrowPrimeBands.growth H*(X : ℝ) ≤ ((p*m : ℕ) : ℝ))
    (hr : ((p*m : ℕ) : ℝ) < 2*(X : ℝ)) : test X H p m := by
  have hab := NarrowPrimeBands.index_bounds H p (by omega) hp
  have hg : 0 < NarrowPrimeBands.growth H := by unfold NarrowPrimeBands.growth; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [Nat.cast_mul] at hl hr
  constructor
  · have hh := mul_le_mul_of_nonneg_left hab.2.le hm
    have hcancel : NarrowPrimeBands.growth H*(X : ℝ) ≤
        NarrowPrimeBands.growth H*((m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p)) := by
      nlinarith only [hl,hh]
    nlinarith only [hcancel,hg]
  · have hh := mul_le_mul_of_nonneg_left hab.1 hm
    nlinarith only [hh,hr]

theorem weight_middle (X H : ℕ) (hH : 2 ≤ H) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (hl : NarrowPrimeBands.growth H*(X : ℝ) ≤ (n : ℝ)) (hr : (n : ℝ) < 2*(X : ℝ)) :
    weight X H P n=RamareWeights.weight P n := by
  apply sum_congr rfl
  intro p hp
  have he := Nat.mul_div_cancel' (mem_filter.mp hp).2
  rw [ite_eq_left (test_middle X H p (n/p) hH (hP p (mem_filter.mp hp).1).one_le
    (by simpa only [he] using hl) (by simpa only [he] using hr))]

theorem weight_above (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hn : 2*NarrowPrimeBands.growth H*(X : ℝ) ≤ (n : ℝ)) : weight X H P n=0 := by
  apply sum_eq_zero
  intro p hp
  have ht : ¬test X H p (n/p) := by
    intro ht
    have hh := (test_product_bounds X H p (n/p) hX hH (hP p (mem_filter.mp hp).1).one_le ht).2
    rw [Nat.mul_div_cancel' (mem_filter.mp hp).2] at hh
    linarith
  exact ite_eq_right ht

theorem weight_outside_boundary (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hn : n ∈ Ico X (4*X)) (hnot : n ∉ boundary X H) :
    weight X H P n=(if n ∈ Ico X (2*X) then RamareWeights.weight P n else 0) := by
  have hb : ¬((n : ℝ) < NarrowPrimeBands.growth H*(X : ℝ) ∨
      2*(X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < 2*NarrowPrimeBands.growth H*(X : ℝ)) := by
    intro hh
    exact hnot (mem_filter.mpr ⟨hn,hh⟩)
  by_cases hi : n < 2*X
  · rw [ite_eq_left (mem_Ico.mpr ⟨(mem_Ico.mp hn).1,hi⟩)]
    apply weight_middle X H hH P hP n
    · exact le_of_not_gt (fun hh ↦ hb (Or.inl hh))
    · exact_mod_cast hi
  · rw [ite_eq_right (by simp only [mem_Ico]; omega)]
    apply weight_above X H hX hH P hP n
    apply le_of_not_gt
    intro hh
    apply hb
    exact Or.inr ⟨by exact_mod_cast (show 2*X ≤ n by omega),hh⟩
end PaperP1.NarrowRectangleWeight
