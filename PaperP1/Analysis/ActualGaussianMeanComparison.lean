module

public import PaperP1.Analysis.GaussianSmoothedEnergy
public import PaperP1.Analysis.GaussianExtendedFrequencyEnergy
public import PaperP1.Analysis.GaussianLogarithmicScales


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualGaussianMeanComparison
open Finset Filter MeasureTheory PaperP1 GaussianLogarithmicScales
open scoped Classical

def smoothed (N : ℕ) (f : ℕ → ℝ) (b u : ℝ) : ℝ :=
  GaussianSmoothedEnergy.smoothed (Ico N (4*N)) (fun n ↦ f n/(n : ℝ))
    (fun n ↦ -Real.log (n : ℝ)) b u

theorem polynomial_eq (N : ℕ) (f : ℕ → ℝ) (t : ℝ) :
    GaussianExponentialSums.polynomial (Ico N (4*N)) (fun n ↦ ((f n/(n : ℝ) : ℝ) : ℂ))
      (fun n ↦ -Real.log (n : ℝ)) t =
    DirichletPolynomialMeanValue.value (Ico N (4*N)) (fun n ↦ (f n : ℂ)) t := by
  simp only [GaussianExponentialSums.polynomial,DirichletPolynomialMeanValue.value,
    Complex.ofReal_div,Complex.ofReal_natCast]

theorem difference_integrable (N : ℕ) (f : ℕ → ℝ) (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Integrable (fun u ↦ (smoothed N f b u-smoothed N f c u)^2) :=
  GaussianSmoothedEnergy.difference_integrable _ _ _ b c hb hc

theorem energy_identity (N : ℕ) (f : ℕ → ℝ) (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (∫ u : ℝ, (smoothed N f b u-smoothed N f c u)^2) =
      (∫ t : ℝ, GaussianDifferenceWeights.weight b c t*
        ‖DirichletPolynomialMeanValue.value (Ico N (4*N)) (fun n ↦ (f n : ℂ)) t‖^2)/(2*Real.pi) := by
  change (∫ u : ℝ, (GaussianSmoothedEnergy.smoothed (Ico N (4*N)) (fun n ↦ f n/(n : ℝ))
    (fun n ↦ -Real.log (n : ℝ)) b u-
    GaussianSmoothedEnergy.smoothed (Ico N (4*N)) (fun n ↦ f n/(n : ℝ))
    (fun n ↦ -Real.log (n : ℝ)) c u)^2) = _
  rw [GaussianSmoothedEnergy.difference_parseval _ _ _ b c hb hc]
  simp_rw [polynomial_eq]
  rfl

theorem uniform_bound (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      (∫ u : ℝ, (smoothed N f (shortWidth D N) u-smoothed N f (longWidth N) u)^2) ≤ ε := by
  obtain ⟨N₀,hN₀,hBound⟩ := GaussianExtendedFrequencyEnergy.uniform_bound D hD
    ((2*Real.pi)*ε) (by positivity)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN f hf
  rw [energy_identity N f (shortWidth D N) (longWidth N)
    (shortWidth_pos D hD N (by omega)) (longWidth_pos N (by omega))]
  exact (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by
    simpa only [mul_comm] using hBound N hN f hf)

end PaperP1.ActualGaussianMeanComparison
