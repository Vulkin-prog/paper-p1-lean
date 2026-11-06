module

public import PaperP1.Analysis.GaussianLogarithmicScales
public import PaperP1.Analysis.UniformGaussianFrequencyEnergy


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianExtendedFrequencyEnergy
open Finset Filter MeasureTheory PaperP1 GaussianLogarithmicScales
open scoped Classical

theorem polynomial_split (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    DirichletPolynomialMeanValue.value (Ico N (4*N)) a t =
      DirichletPolynomialMeanValue.value (Ico N (2*N)) a t+
      DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  have hh := sum_Ico_consecutive
    (fun n : ℕ ↦ a n/(n : ℂ)*LogarithmicPhase.phase (-Real.log (n : ℝ)) t)
    (show N ≤ 2*N by omega) (show 2*N ≤ 4*N by omega)
  simpa only [show 2*(2*N)=4*N by omega] using hh.symm

theorem energy_split (N : ℕ) (a : ℕ → ℂ) (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    (∫ t : ℝ, GaussianDifferenceWeights.weight b c t*
      ‖DirichletPolynomialMeanValue.value (Ico N (4*N)) a t‖^2) ≤
      2*(∫ t : ℝ, GaussianDifferenceWeights.weight b c t*
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a t‖^2)+
      2*(∫ t : ℝ, GaussianDifferenceWeights.weight b c t*
        ‖DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t‖^2) := by
  have hWhole := GaussianDifferenceWeights.weighted_integrable (Ico N (4*N)) a b c hb hbc
  have hOne := GaussianDifferenceWeights.weighted_integrable (Ico N (2*N)) a b c hb hbc
  have hTwo := GaussianDifferenceWeights.weighted_integrable (Ico (2*N) (2*(2*N))) a b c hb hbc
  have hRight : Integrable (fun t ↦ 2*(GaussianDifferenceWeights.weight b c t*
      ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a t‖^2)+
      2*(GaussianDifferenceWeights.weight b c t*
      ‖DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t‖^2)) :=
    (hOne.const_mul 2).add (hTwo.const_mul 2)
  have hBound : (∫ t : ℝ, GaussianDifferenceWeights.weight b c t*
      ‖DirichletPolynomialMeanValue.value (Ico N (4*N)) a t‖^2) ≤
      ∫ t : ℝ, 2*(GaussianDifferenceWeights.weight b c t*
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a t‖^2)+
        2*(GaussianDifferenceWeights.weight b c t*
        ‖DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t‖^2) := by
    apply integral_mono_ae hWhole hRight
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [polynomial_split]
    have hNorm := norm_add_le
      (DirichletPolynomialMeanValue.value (Ico N (2*N)) a t)
      (DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t)
    have hSq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    have hTri : ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a t+
        DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t‖^2 ≤
        2*‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a t‖^2+
        2*‖DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t‖^2 := by
      nlinarith only [hSq,sq_nonneg (‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a t‖-
        ‖DirichletPolynomialMeanValue.value (Ico (2*N) (2*(2*N))) a t‖)]
    have hh := mul_le_mul_of_nonneg_left hTri (GaussianDifferenceWeights.weight_nonneg b c t)
    nlinarith only [hh]
  rw [integral_add (hOne.const_mul 2) (hTwo.const_mul 2),integral_const_mul,integral_const_mul] at hBound
  exact hBound

theorem uniform_bound (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      (∫ t : ℝ, GaussianDifferenceWeights.weight (shortWidth D N) (longWidth N) t*
        ‖DirichletPolynomialMeanValue.value (Ico N (4*N)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := UniformGaussianFrequencyEnergy.dyadic_uniform_bound D hD (ε/4) (by positivity)
  obtain ⟨NO,hOrder⟩ := eventually_atTop.mp (eventual_order D hD)
  refine ⟨max NB NO,by omega,?_⟩
  intro N hN f hf
  have hOne := hBound N (by omega) N le_rfl (by omega) f hf
  have hTwo := hBound N (by omega) (2*N) (by omega) le_rfl f hf
  have hSplit := energy_split N (fun n ↦ (f n : ℂ)) (shortWidth D N) (longWidth N)
    (shortWidth_pos D hD N (by omega)) (hOrder N (by omega))
  linarith only [hSplit,hOne,hTwo]

end PaperP1.GaussianExtendedFrequencyEnergy
