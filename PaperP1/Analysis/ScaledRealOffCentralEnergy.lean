module

public import PaperP1.Analysis.UniformRealOffCentralEnergy
public import PaperP1.Analysis.ScaledFirstGoodEnergy
public import PaperP1.Analysis.ScaledIntermediateEnergy


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ScaledRealOffCentralEnergy
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem common_central_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ D : ℝ, 0 ≤ D → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ T : ℝ, 1 ≤ T →
      T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in UniformRealOffCentralEnergy.region T T₀,
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨T₀,hT₀,NJ,hNJ,hJoint⟩ := OffCentralJointEnergy.uniform_bound (ε/3) (by positivity)
  refine ⟨T₀,hT₀,?_⟩
  intro D hD
  obtain ⟨NG,hNG,hGood⟩ := ScaledFirstGoodEnergy.full_small_uniform D hD (ε/3) (by positivity)
  obtain ⟨NI,hNI,hIntermediate⟩ := ScaledIntermediateEnergy.full_small_uniform D hD (ε/3) (by positivity)
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop (max 1 D)))
  refine ⟨max 2 (max NG (max NI (max NJ NL))),by omega,?_⟩
  intro N hN f hf T hT hTime
  have hTP : 0 < T := by linarith only [hT]
  have hLog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans (hLog N (by omega))
  have hDLog : D ≤ Real.log (N : ℝ) := (le_max_right _ _).trans (hLog N (by omega))
  have hLogP : 0 < Real.log (N : ℝ) := by linarith only [hLog1]
  have hTN : T ≤ (N : ℝ) := hTime.trans ((div_le_iff₀ hLogP).mpr (by
    have hh := mul_le_mul_of_nonneg_right hDLog (Nat.cast_nonneg N)
    nlinarith only [hh]))
  let fC : ℕ → ℂ := fun n ↦ (f n : ℂ)
  have hfC : ∀ n, 0 < n → ‖fC n‖ ≤ 1 := by
    intro n hn
    simpa only [fC,Complex.norm_real,Real.norm_eq_abs] using
      FinitePrimeDirichletTruncation.real_hom_bound f hf n (Nat.ne_of_gt hn)
  have hMultiply : ∀ m n, fC (m*n)=fC m*fC n := by
    intro m n
    dsimp only [fC]
    rw [map_mul,Complex.ofReal_mul]
  have hGoodBound := hGood N (by omega) fC hMultiply hfC T hTP hTime
  have hIntermediateBound := hIntermediate N (by omega) fC hMultiply hfC T hTP hTime
  have hJointBound := hJoint N (by omega) f hf T hT hTN
  have hReduction := UniformRealOffCentralEnergy.restricted_reduction N fC T T₀
  dsimp only [fC] at hGoodBound hIntermediateBound hReduction
  linarith only [hReduction,hGoodBound,hIntermediateBound,hJointBound]

theorem uniform_bound (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ T : ℝ, 1 ≤ T →
      T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in UniformRealOffCentralEnergy.region T T₀,
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨T₀,hT₀,hBound⟩ := common_central_bound ε hε
  exact ⟨T₀,hT₀,hBound D hD⟩
end PaperP1.ScaledRealOffCentralEnergy
