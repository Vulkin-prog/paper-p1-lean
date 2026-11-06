module

public import PaperP1.Analysis.MultiplicativeShortAverage
public import PaperP1.Analysis.CenteredLogarithmicSampling
public import PaperP1.Analysis.CentralDirichletLowerBound

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CentralMeanSquareObstruction
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

theorem central_interval_lower (N : ℕ) (hN : 0 < N) :
    (1/16 : ℝ) ≤ ∫ t in -(1/2 : ℝ)..(1/2 : ℝ),
      ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖^2 := by
  have hc : Continuous (fun t ↦ ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖^2) :=
    (GaussianExponentialSums.polynomial_continuous _ _ _).norm.pow 2
  have hh := intervalIntegral.integral_mono_on (μ := volume) (f := fun _t : ℝ ↦ (1/16 : ℝ))
    (by norm_num : -(1/2 : ℝ) ≤ 1/2) (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    (fun t ht ↦ by
      have hn := CentralDirichletLowerBound.central_norm_lower N hN t (abs_le.mpr ⟨ht.1,ht.2⟩)
      nlinarith only [hn])
  norm_num only [intervalIntegral.integral_const,show (1/2 : ℝ)- -(1/2)=1 by norm_num,one_smul] at hh
  exact hh

theorem full_interval_lower (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 1/2 ≤ T) :
    (1/16 : ℝ) ≤ ∫ t in -T..T,
      ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖^2 := by
  have hc : Continuous (fun t ↦ ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖^2) :=
    (GaussianExponentialSums.polynomial_continuous _ _ _).norm.pow 2
  exact (central_interval_lower N hN).trans
    (intervalIntegral.integral_mono_interval (by linarith : -T ≤ -(1/2 : ℝ))
      (by norm_num : -(1/2 : ℝ) ≤ 1/2) hT
      (Filter.Eventually.of_forall (fun t ↦ sq_nonneg _)) (hc.intervalIntegrable (-T) T))

theorem no_unrestricted_vanishing (T : ℕ → ℝ) (hT : ∀ᶠ N : ℕ in atTop, 1/2 ≤ T N) :
    ¬Tendsto (fun N : ℕ ↦ ∫ t in -(T N)..T N,
      ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖^2) atTop (nhds 0) := by
  intro hh
  have hsmall := hh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/32))
  obtain ⟨N,hN,hTN,hs⟩ := ((eventually_ge_atTop 1).and (hT.and hsmall)).exists
  have hl := full_interval_lower N (by omega) (T N) hTN
  linarith only [hl,hs]

theorem constant_mean_difference (N j h : ℕ) (hN : 0 < N) (hh : 0 < h) :
    MultiplicativeShortAverage.shortMean (fun _ ↦ (1 : ℝ)) j h-
      MultiplicativeShortAverage.longMean (fun _ ↦ (1 : ℝ)) N=0 := by
  have hc : (Ico N (2*N)).card=N := by simp only [Nat.card_Ico]; omega
  simp [MultiplicativeShortAverage.shortMean,MultiplicativeShortAverage.longMean,hc,
    Nat.ne_of_gt hN,Nat.ne_of_gt hh]

theorem constant_square_zero (N h : ℕ) (hN : 0 < N) (hh : 0 < h) :
    (∑ j ∈ Ico N (2*N), (MultiplicativeShortAverage.shortMean (fun _ ↦ (1 : ℝ)) j h-
      MultiplicativeShortAverage.longMean (fun _ ↦ (1 : ℝ)) N)^2)=0 := by
  simp_rw [constant_mean_difference N _ h hN hh]
  simp
end PaperP1.CentralMeanSquareObstruction
