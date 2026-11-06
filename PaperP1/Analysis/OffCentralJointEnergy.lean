module

public import PaperP1.Analysis.FirstGoodFullPolynomial
public import PaperP1.Analysis.FixedPowerNarrowGeometry
public import PaperP1.Analysis.FixedPowerJointRectangle
public import PaperP1.Analysis.PrecisionPowerRectangleApproximation


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.OffCentralJointEnergy
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∫ t in FixedPowerJointRectangle.region N (fun n ↦ (f n : ℂ)) T T₀,
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨a,ha,hab,H₀,hH₀,NA,hNA,hApprox⟩ := PrecisionPowerRectangleApproximation.precision_choice (ε/4) (by positivity)
  obtain ⟨H,hH,hWide,hOrder⟩ := FixedPowerNarrowGeometry.width_exists a ha H₀
  obtain ⟨T₀,hT₀,NR,hNR,hRectangle⟩ := FixedPowerJointRectangle.uniform_bound a (1/32) ha
    (by norm_num) H hH hOrder (ε/4) (by positivity)
  refine ⟨T₀,hT₀,max 2 (max NA NR),by omega,?_⟩
  intro N hN f hf T hT hTN
  have hNP : 0 < N := by omega
  have hTP : 0 < T := by linarith only [hT]
  let fC : ℕ → ℂ := fun n ↦ (f n : ℂ)
  have hfC : ∀ n, 0 < n → ‖fC n‖ ≤ 1 := by
    intro n hn
    simpa only [fC,Complex.norm_real,Real.norm_eq_abs] using
      FinitePrimeDirichletTruncation.real_hom_bound f hf n (Nat.ne_of_gt hn)
  have hMultiply : ∀ m n, fC (m*n)=fC m*fC n := by
    intro m n
    dsimp only [fC]
    rw [map_mul,Complex.ofReal_mul]
  have hWideUnit : ∀ n ∈ Ico N (4*N), ‖fC n‖ ≤ 1 := fun n hn ↦ hfC n (hNP.trans_le (mem_Ico.mp hn).1)
  have hError := hApprox H hWide N (by omega) fC hMultiply hWideUnit T hTP hTN
  have hRectangleBound := hRectangle N (by omega) (TwoPrimeBandPopulation.first N)
    (fun p hp ↦ (mem_filter.mp hp).2) f hf T hT hTN
  have hTransfer := FirstGoodFullPolynomial.restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) fC)
    (NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a (1/32) N) (TwoPrimeBandPopulation.first N) fC)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _)
    (FixedPowerJointRectangle.region N fC T T₀) (FixedPowerJointRectangle.region_measurable N fC T T₀)
    T hTP.le (fun t ht ↦ ((JointLargeFrequencyReduction.largeRegion_iff N fC T t).mp ht.1).1)
  dsimp only [fC] at hError hTransfer
  linarith only [hTransfer,hError,hRectangleBound]
end PaperP1.OffCentralJointEnergy
