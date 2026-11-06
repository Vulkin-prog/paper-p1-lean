module

public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Analysis.ActualEulerBand

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FrequencyBudgetMonotone
open Finset Nat PaperP1
open scoped Classical

theorem frequencyBudget_mono (F : ℝ → ℂ) (hF : Continuous F) (K M : ℕ) (hKM : K ≤ M) :
    PrimeUnitMean.frequencyBudget F K ≤ PrimeUnitMean.frequencyBudget F M := by
  let S := (range (2*K+1)).image (fun j ↦ j+(M-K))
  let g := fun j : ℕ ↦ PrimeUnitMean.localSquareSup F ((j : ℝ)-(M : ℝ))/(1+((j : ℝ)-(M : ℝ))^2)
  have hS : S ⊆ range (2*M+1) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    have hb := mem_range.mp hj
    exact mem_range.mpr (by omega)
  have he : PrimeUnitMean.frequencyBudget F K=∑ j ∈ S, g j := by
    unfold PrimeUnitMean.frequencyBudget
    rw [sum_image (fun i _hi j _hj hij ↦ Nat.add_right_cancel hij)]
    apply sum_congr rfl
    intro j hj
    have hc : ((j+(M-K) : ℕ) : ℝ)-(M : ℝ)=(j : ℝ)-(K : ℝ) := by
      rw [Nat.cast_add,Nat.cast_sub hKM]
      ring
    dsimp only [g]
    rw [hc]
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hS (fun j _hj _hnot ↦
    div_nonneg (PrimeUnitMean.local_sup_nonneg F hF _) (by positivity))

theorem cutoff_mono (X Y : ℕ) (hX : 2 ≤ X) (hXY : X ≤ Y) :
    ActualEulerBand.frequencyCutoff X ≤ ActualEulerBand.frequencyCutoff Y := by
  unfold ActualEulerBand.frequencyCutoff
  apply Nat.ceil_mono
  change (Real.log (X : ℝ))^10 ≤ (Real.log (Y : ℝ))^10
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXYR : (X : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hXY
  have hlog := Real.log_le_log hXp hXYR
  exact pow_le_pow_left₀ (Real.log_natCast_nonneg X) hlog 10
end PaperP1.FrequencyBudgetMonotone
