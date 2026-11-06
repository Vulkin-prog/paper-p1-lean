module

public import PaperP1.Analysis.GaussianLocalizationBudget
public import PaperP1.Analysis.LogarithmicWindowCells
public import PaperP1.Analysis.SmoothGaussianPopulation


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothGaussianWindowUpper
open Finset PaperP1 OddPrimePivot GaussianOverlap GaussianLaplaceKernel SmoothGaussianPopulation
open scoped Classical

theorem window_bound (N Y j h : ℕ) (hN : 2 ≤ N) (hj : j ∈ Ico N (2*N))
    (hh : 6 ≤ h) (hhN : h ≤ N) (hFew : ((Ico j (j+h)).filter fun n ↦ largestPrimeFactor n ≤ Y).card ≤ 1)
    (δ X : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hXL : (j : ℝ)+(h : ℝ)/2 ≤ X) (hXR : X ≤ (j : ℝ)+(h : ℝ)/2+1) :
    ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) (δ^2) (-Real.log X) ≤
      (prefactor 1/((N : ℝ)*δ))*(1+
        Real.exp (-((h : ℝ)/(12*(N : ℝ)))^2/(8*δ^2))*
          LogarithmicGaussianSum.constant*(4*(N : ℝ)*δ+1)) := by
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hNN : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hjL : (N : ℝ) ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
  have hjR : (j : ℝ) < 2*(N : ℝ) := by exact_mod_cast (mem_Ico.mp hj).2
  have hhR : (6 : ℝ) ≤ h := by exact_mod_cast hh
  have hhNR : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hX : 0 < X := by linarith only [hNP,hjL,hXL,hhR]
  have hXTop : X ≤ 4*(N : ℝ) := by linarith only [hXR,hjR,hhNR,hNN]
  let S := population N Y
  let I := S ∩ Ico j (j+h)
  have hIS : I ⊆ S := inter_subset_left
  have hCard : I.card ≤ 1 := by
    have hSub : I ⊆ (Ico j (j+h)).filter fun n ↦ largestPrimeFactor n ≤ Y := by
      intro n hn
      obtain ⟨hnS,hnW⟩ := mem_inter.mp hn
      exact mem_filter.mpr ⟨hnW,(mem_filter.mp hnS).2⟩
    exact (card_le_card hSub).trans hFew
  have ha : ∀ n ∈ S, 0 ≤ 1/(n : ℝ) ∧ 1/(n : ℝ) ≤ 1/(N : ℝ) := by
    intro n hn
    have hnL := (mem_Ico.mp (mem_filter.mp hn).1).1
    exact ⟨by positivity,div_le_div_of_nonneg_left zero_le_one hNP (by exact_mod_cast hnL)⟩
  have hAway : ∀ n ∈ S \ I, (h : ℝ)/(12*(N : ℝ)) ≤ |Real.log ((n : ℝ)/X)| := by
    intro n hn
    have hnS := (Finset.mem_sdiff.mp hn).1
    have hnNot : n ∉ Ico j (j+h) := by
      intro hnW
      exact (Finset.mem_sdiff.mp hn).2 (mem_inter.mpr ⟨hnS,hnW⟩)
    have hGap := LogarithmicWindowCells.outside_window_gap j h n hh X hXL hXR hnNot
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast population_positive N Y (by omega) n hnS
    have hnTop : (n : ℝ) ≤ 4*(N : ℝ) := by
      exact_mod_cast (mem_Ico.mp (mem_filter.mp hnS).1).2.le
    have hLog := LogarithmicWindowCells.log_ratio_lower (4*(N : ℝ)) X (n : ℝ) hX hnPos hXTop hnTop
    calc
      _ = ((h : ℝ)/3)/(4*(N : ℝ)) := by ring
      _ ≤ |(n : ℝ)-X|/(4*(N : ℝ)) := div_le_div_of_nonneg_right hGap (by positivity)
      _ ≤ _ := hLog
  have hLoc := GaussianLocalizationBudget.localization S I hIS (fun n ↦ 1/(n : ℝ))
    (1/(N : ℝ)) X δ ((h : ℝ)/(12*(N : ℝ))) (by positivity) hX hδ hδ1 (by positivity)
    (population_positive N Y (by omega)) ha hCard hAway
  have hPref : 0 ≤ prefactor 1/δ := by positivity [prefactor_pos 1 (by norm_num)]
  have hC := LogarithmicGaussianSum.constant_pos
  have hCenter : δ*X+1 ≤ 4*(N : ℝ)*δ+1 := by nlinarith only [hXTop,hδ]
  have hTailFactor : 0 ≤ Real.exp (-((h : ℝ)/(12*(N : ℝ)))^2/(8*δ^2))*
      (1/(N : ℝ))*(prefactor 1/δ)*LogarithmicGaussianSum.constant := by positivity
  rw [smoothed_eq N Y (by omega) (δ^2) X hX]
  calc
    _ ≤ (1/(N : ℝ))*(prefactor 1/δ)+
        Real.exp (-((h : ℝ)/(12*(N : ℝ)))^2/(8*δ^2))*
        (1/(N : ℝ))*(prefactor 1/δ)*LogarithmicGaussianSum.constant*(δ*X+1) := hLoc
    _ ≤ (1/(N : ℝ))*(prefactor 1/δ)+
        Real.exp (-((h : ℝ)/(12*(N : ℝ)))^2/(8*δ^2))*
        (1/(N : ℝ))*(prefactor 1/δ)*LogarithmicGaussianSum.constant*(4*(N : ℝ)*δ+1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hCenter hTailFactor)
    _ = _ := by ring

end PaperP1.SmoothGaussianWindowUpper
