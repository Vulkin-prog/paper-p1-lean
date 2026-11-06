module

public import PaperP1.Analysis.ActualGaussianMeanComparison
public import PaperP1.Arithmetic.OrdinarySmoothIndicator
public import PaperP1.Analysis.ScaledGaussianKernel


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothGaussianPopulation
open Finset PaperP1 OddPrimePivot GaussianOverlap GaussianLaplaceKernel ScaledGaussianKernel
open scoped Classical

def population (N Y : ℕ) : Finset ℕ := (Ico N (4*N)).filter fun n ↦ largestPrimeFactor n ≤ Y

theorem population_positive (N Y : ℕ) (hN : 0 < N) : ∀ n ∈ population N Y, 0 < n := by
  intro n hn
  exact hN.trans_le (mem_Ico.mp (mem_filter.mp hn).1).1

theorem smoothed_eq (N Y : ℕ) (hN : 0 < N) (b X : ℝ) (hX : 0 < X) :
    ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) b (-Real.log X) =
      ∑ n ∈ population N Y, (1/(n : ℝ))*heat b (Real.log ((n : ℝ)/X)) := by
  rw [ActualGaussianMeanComparison.smoothed,GaussianSmoothedEnergy.smoothed,population,sum_filter]
  apply sum_congr rfl
  intro n hn
  have hn0 : n≠0 := by have hh := (mem_Ico.mp hn).1; omega
  have hnP : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hArg : (-Real.log X)-(-Real.log (n : ℝ))=Real.log ((n : ℝ)/X) := by
    rw [Real.log_div hnP.ne' hX.ne']
    ring
  rw [hArg]
  by_cases hSmooth : largestPrimeFactor n ≤ Y
  · simp [OrdinarySmoothIndicator.value,hn0,hSmooth]
  · simp [OrdinarySmoothIndicator.value,hn0,hSmooth]

theorem subpopulation_lower (N Y : ℕ) (hN : 0 < N) (I : Finset ℕ) (hI : I ⊆ population N Y)
    (X δ : ℝ) (hX : 0 < X) (hδ : 0 < δ)
    (hNear : ∀ n ∈ I, |Real.log ((n : ℝ)/X)| ≤ δ) :
    (I.card : ℝ)*(prefactor 1*Real.exp (-1))/(δ*(4*(N : ℝ))) ≤
      ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) (δ^2) (-Real.log X) := by
  have hNP : 0 < (N : ℝ) := by exact_mod_cast hN
  have hK : 0 < prefactor 1*Real.exp (-1) := mul_pos (prefactor_pos 1 (by norm_num)) (Real.exp_pos _)
  rw [smoothed_eq N Y hN (δ^2) X hX]
  calc
    _ = ∑ _n ∈ I, (prefactor 1*Real.exp (-1))/(δ*(4*(N : ℝ))) := by
      rw [sum_const,nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ I, (1/(n : ℝ))*heat (δ^2) (Real.log ((n : ℝ)/X)) := by
      apply sum_le_sum
      intro n hn
      have hnS := hI hn
      have hnP : 0 < (n : ℝ) := by exact_mod_cast population_positive N Y hN n hnS
      have hnTop : (n : ℝ) ≤ 4*(N : ℝ) := by
        have hh := (mem_Ico.mp (mem_filter.mp hnS).1).2.le
        exact_mod_cast hh
      have hRecip : 1/(4*(N : ℝ)) ≤ 1/(n : ℝ) :=
        div_le_div_of_nonneg_left zero_le_one hnP hnTop
      have hHeat := heat_lower δ (Real.log ((n : ℝ)/X)) hδ (hNear n hn)
      calc
        _ = (1/(4*(N : ℝ)))*(prefactor 1*Real.exp (-1)/δ) := by ring
        _ ≤ _ := mul_le_mul hRecip hHeat (by positivity) (by positivity)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hI (fun n hn hni ↦
      mul_nonneg (by positivity) (heat_nonneg _ _ (sq_pos_of_pos hδ)))

end PaperP1.SmoothGaussianPopulation
