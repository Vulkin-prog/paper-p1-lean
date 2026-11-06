module

public import PaperP1.Analysis.ReciprocalFrequencyWeights
public import PaperP1.Analysis.TranslatedFrequencyTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LocalizedFrequencyBudget
open Finset PaperP1
open scoped Classical

theorem near_sup_bound (F : ℝ → ℂ) (hF : Continuous F) (m R u : ℝ)
    (hLocal : ∀ t : ℝ, |t| ≤ R+1 → ‖F t‖ ≤ m) (hu : |u| ≤ R) :
    PrimeUnitMean.localSquareSup F u ≤ m^2 := by
  obtain ⟨t,ht,he⟩ := PrimeUnitMean.local_sup_attained F hF u
  rw [he]
  have hT : |t| ≤ R+1 := by
    have hU := abs_le.mp hu
    exact abs_le.mpr ⟨by linarith only [hU.1,ht.1],by linarith only [hU.2,ht.2]⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (hLocal t hT) 2

theorem budget_bound (F : ℝ → ℂ) (hF : Continuous F) (M m R : ℝ) (hR : 0 < R)
    (hGlobal : ∀ t : ℝ, ‖F t‖ ≤ M)
    (hLocal : ∀ t : ℝ, |t| ≤ R+1 → ‖F t‖ ≤ m) (K : ℕ) :
    PrimeUnitMean.frequencyBudget F K ≤ 5*m^2+4*M^2/R := by
  let S := range (2*K+1)
  let N : Finset ℕ := S.filter (fun j : ℕ ↦ |(j : ℝ)-(K : ℝ)| ≤ R)
  let T : Finset ℕ := S.filter (fun j : ℕ ↦ R < |(j : ℝ)-(K : ℝ)|)
  have hNear : (∑ j ∈ N, PrimeUnitMean.localSquareSup F ((j : ℝ)-(K : ℝ))/
      (1+((j : ℝ)-(K : ℝ))^2)) ≤ 5*m^2 := by
    calc
      _ ≤ ∑ j ∈ N, m^2/(1+((j : ℝ)-(K : ℝ))^2) := by
        apply sum_le_sum
        intro j hj
        exact div_le_div_of_nonneg_right (near_sup_bound F hF m R _ hLocal (mem_filter.mp hj).2) (by positivity)
      _ = m^2*(∑ j ∈ N, 1/(1+((j : ℝ)-(K : ℝ))^2)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (ReciprocalFrequencyWeights.finite_weight_bound N K) (sq_nonneg m)
        nlinarith only [hh]
  have hTail : (∑ j ∈ T, PrimeUnitMean.localSquareSup F ((j : ℝ)-(K : ℝ))/
      (1+((j : ℝ)-(K : ℝ))^2)) ≤ 4*M^2/R := by
    have hWeights := TranslatedFrequencyTail.finite_bound T K R hR
      (fun j hj ↦ (mem_filter.mp hj).2.le)
    calc
      _ ≤ ∑ j ∈ T, M^2/(1+((j : ℝ)-(K : ℝ))^2) := by
        apply sum_le_sum
        intro j hj
        exact div_le_div_of_nonneg_right (ReciprocalFrequencyWeights.local_sup_bound F hF M hGlobal _) (by positivity)
      _ = M^2*(∑ j ∈ T, 1/(1+((j : ℝ)-(K : ℝ))^2)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      _ ≤ M^2*(4/R) := mul_le_mul_of_nonneg_left hWeights (sq_nonneg M)
      _ = _ := by ring
  have hSplit : PrimeUnitMean.frequencyBudget F K=
      (∑ j ∈ N, PrimeUnitMean.localSquareSup F ((j : ℝ)-(K : ℝ))/(1+((j : ℝ)-(K : ℝ))^2))+
      (∑ j ∈ T, PrimeUnitMean.localSquareSup F ((j : ℝ)-(K : ℝ))/(1+((j : ℝ)-(K : ℝ))^2)) := by
    unfold PrimeUnitMean.frequencyBudget N T S
    rw [sum_filter,sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    by_cases hh : |(j : ℝ)-(K : ℝ)| ≤ R
    · simp [hh,not_lt_of_ge hh]
    · simp [hh,lt_of_not_ge hh]
  rw [hSplit]
  exact add_le_add hNear hTail
end PaperP1.LocalizedFrequencyBudget
