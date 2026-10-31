module

public import PaperP1.Arithmetic.WeightedPrimeSum

/-! # An arbitrary finite prime set with a logarithmic budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicPrimeBudget

open Finset PaperP1.DefectCounting PaperP1.WeightedPrimeSum

def budgetConstant : ℝ := smallPrimeConstant + 1

theorem budgetConstant_pos : 0 < budgetConstant := by
  unfold budgetConstant smallPrimeConstant
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  linarith

theorem primeBudgetSum_mul_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Y σ : ℝ) (hY : 1 < Y) (hσ : 0 ≤ σ) (hσ3 : σ ≤ 3 / 4)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ Y) :
    (∑ p ∈ P, (p : ℝ) ^ (-σ)) * Real.log Y ≤ budgetConstant * Y ^ (1 - σ) := by
  let low := P.filter fun p ↦ p ≤ Nat.floor Y
  let high := P.filter fun p ↦ ¬p ≤ Nat.floor Y
  have hYpos : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log Y := (Real.log_pos hY).le
  have hlow : low ⊆ smallPrimesUpTo (Nat.floor Y) := by
    intro p hp
    obtain ⟨hp, hcut⟩ := mem_filter.mp hp
    exact mem_smallPrimesUpTo.mpr ⟨hP p hp, hcut⟩
  have hlowBound : (∑ p ∈ low, (p : ℝ) ^ (-σ)) * Real.log Y ≤
      smallPrimeConstant * Y ^ (1 - σ) := by
    calc
      _ ≤ primeSum (Nat.floor Y) σ * Real.log Y :=
        mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg hlow
          (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)) hlogY
      _ ≤ _ := primeSum_mul_log_le_uniform Y σ hYpos hσ hσ3
  have hterm (p : ℕ) (hp : p ∈ high) :
      (p : ℝ) ^ (-σ) * Real.log Y ≤ Y ^ (-σ) * Real.log p := by
    obtain ⟨hp, hcut⟩ := mem_filter.mp hp
    have hpY : Y < (p : ℝ) := by
      by_contra h
      exact hcut ((Nat.le_floor_iff hYpos.le).mpr (by linarith))
    calc
      _ ≤ Y ^ (-σ) * Real.log Y := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hYpos hpY.le (by linarith)) hlogY
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log hYpos hpY.le)
        (Real.rpow_nonneg hYpos.le _)
  have hhighBudget : (∑ p ∈ high, Real.log p) ≤ Y := by
    apply le_trans _ hbudget
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p hp _ ↦ Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le))
  have hhighBound : (∑ p ∈ high, (p : ℝ) ^ (-σ)) * Real.log Y ≤ Y ^ (1 - σ) := by
    calc
      _ = ∑ p ∈ high, (p : ℝ) ^ (-σ) * Real.log Y := by rw [sum_mul]
      _ ≤ ∑ p ∈ high, Y ^ (-σ) * Real.log p := sum_le_sum hterm
      _ = Y ^ (-σ) * ∑ p ∈ high, Real.log p := (mul_sum _ _ _).symm
      _ ≤ Y ^ (-σ) * Y := mul_le_mul_of_nonneg_left hhighBudget (Real.rpow_nonneg hYpos.le _)
      _ = Y ^ (1 - σ) := by
        calc
          _ = Y ^ (-σ) * Y ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hYpos]; congr 1; ring
  have hsplit : (∑ p ∈ low, (p : ℝ) ^ (-σ)) + (∑ p ∈ high, (p : ℝ) ^ (-σ)) =
      ∑ p ∈ P, (p : ℝ) ^ (-σ) := sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit, add_mul]
  calc
    _ ≤ smallPrimeConstant * Y ^ (1 - σ) + Y ^ (1 - σ) := add_le_add hlowBound hhighBound
    _ = _ := by unfold budgetConstant; ring

theorem primeBudgetSum_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Y σ : ℝ) (hY : 1 < Y) (hσ : 0 ≤ σ) (hσ3 : σ ≤ 3 / 4)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ Y) :
    (∑ p ∈ P, (p : ℝ) ^ (-σ)) ≤ budgetConstant * Y ^ (1 - σ) / Real.log Y := by
  exact (le_div_iff₀ (Real.log_pos hY)).mpr
    (primeBudgetSum_mul_log_le P hP Y σ hY hσ hσ3 hbudget)

theorem primeBudgetEuler_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Y σ : ℝ) (hY : 1 < Y) (hσ : 0 ≤ σ) (hσ3 : σ ≤ 3 / 4)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ Y) :
    (∏ p ∈ P, (1 + (p : ℝ) ^ (-σ))) ≤
      Real.exp (budgetConstant * Y ^ (1 - σ) / Real.log Y) := by
  calc
    _ ≤ Real.exp (∑ p ∈ P, (p : ℝ) ^ (-σ)) :=
      Real.prod_one_add_le_exp_sum _ (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ _ := Real.exp_le_exp.mpr (primeBudgetSum_le P hP Y σ hY hσ hσ3 hbudget)

end PaperP1.LogarithmicPrimeBudget
