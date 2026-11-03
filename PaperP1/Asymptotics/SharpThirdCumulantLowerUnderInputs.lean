module

public import PaperP1.Asymptotics.SharpThirdCancellationUnderInputs
public import PaperP1.Asymptotics.ThreeSlopePositiveActivity
public import PaperP1.Model.PositiveJointRestriction

/-! # The rational positive third activity survives in the full third factorial cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpThirdCumulantLowerUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.TripleActivityConnected
  PaperP1.ThirdRunFactorialCumulant PaperP1.PositiveMarginalRestriction

theorem error_absorption (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (N : ℝ) ^ (-43 / 30 : ℝ) ≤ ThreeSlopePositiveActivity.lowerConstant C *
        (N : ℝ) ^ (-41 / 30 : ℝ) := by
  have hc := ThreeSlopePositiveActivity.lower_constant_pos C
  obtain ⟨N₀, hf⟩ := HalfCountSchedule.factor_absorption
    (1 / ThreeSlopePositiveActivity.lowerConstant C) (-43 / 30) (1 / 15) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN
  have h := mul_le_mul_of_nonneg_left (hf N hN) hc.le
  simpa only [← mul_assoc, mul_one_div_cancel hc.ne', one_mul,
    show (-43 / 30 : ℝ) + 1 / 15 = -41 / 30 by norm_num] using h

/-- The geometry is exactly the previously inventoried input at one fixed finite cap.
The conclusions concern the actual admissible set and the full original count. -/
theorem article_14_5 (C : ℝ) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 30720)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ThreeSlopePositiveActivity.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
          positiveConnected L ((positiveGround (dyadicBlock N) L).powersetCard 3) ∧
        5 * ThreeSlopePositiveActivity.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
          thirdFactorialCumulant (positiveGround (dyadicBlock N) L) L ∧
        5 * ThreeSlopePositiveActivity.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
          thirdFactorialCumulant (dyadicBlock N) L) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hc⟩ := SharpThirdCancellationUnderInputs.uniform_cancellation C
    (1 / 15) (by norm_num)
  rw [show (1 / 15 : ℝ) / 2048 = 1 / 30720 by norm_num] at hc
  obtain ⟨NP, _hNP, hp⟩ := ThreeSlopePositiveActivity.source_positive_lower C
  obtain ⟨NE, he⟩ := error_absorption C
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NC, _hNC, hc⟩ := hc hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NP (max NE NC)), by omega, ?_⟩
  intro N hN L hband
  let G := positiveGround (dyadicBlock N) L
  have hpos := hp N (by omega) L hband
  have hgap := (hc N (by omega) L hband G (positiveGround_subset _ _)
    (fun _ hx ↦ marginal_positive hx)).2.2.2.1
  have hgap' : |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| ≤
      (N : ℝ) ^ (-43 / 30 : ℝ) := by convert hgap using 1; norm_num
  have herror := he N (by omega)
  have hlower : 5 * ThreeSlopePositiveActivity.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
      thirdFactorialCumulant G L := by
    have hleft := (abs_le.mp hgap').1
    change ThreeSlopePositiveActivity.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
      positiveConnected L (G.powersetCard 3) at hpos
    linarith only [hleft, hpos, herror]
  refine ⟨hpos, hlower, ?_⟩
  rw [PositiveJointRestriction.third_restrict (subset_refl (dyadicBlock N))]
  exact hlower

end PaperP1.SharpThirdCumulantLowerUnderInputs
