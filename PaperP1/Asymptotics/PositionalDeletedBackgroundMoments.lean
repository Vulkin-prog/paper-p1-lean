module

public import PaperP1.Asymptotics.PolynomialWeightedFieldRate
public import PaperP1.Asymptotics.PositionalBackgroundMoments
public import PaperP1.Asymptotics.PositionalDeletionTransferUnderInputs

/-! # Joint moment control for the actual erased laws and their independent background -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletedBackgroundMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalDeletedFields
  PaperP1.PolynomialWeightedFieldRate

theorem uniform_bound (r : ℕ) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
      let U := PositionalMarkedPairExpansion.background (dyadicBlock N) E
        (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
      MomentBounds (onceLaw E (dyadicBlock N) L) U r ((N : ℝ) ^ δ) ∧
      MomentBounds (isolatedLaw E (dyadicBlock N) L) U r ((N : ℝ) ^ δ) := by
  obtain ⟨NA, _hNA, ha⟩ := PositionalDeletionTransferUnderInputs.uniform_original_moments r C δ hδ
  obtain ⟨B, _hB, NB, _hNB, hb⟩ := PositionalBackgroundMoments.uniform_bound r C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption B 0 δ hδ
  refine ⟨3 + NA + NB + NF, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  have hA := ha N (by omega) L hband (dyadicBlock N) Subset.rfl E
  have hU := hb N (by omega) L hband (8 * (L + 1) : ℕ)
  have hB : B ≤ (N : ℝ) ^ δ := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  constructor
  · exact
      { left_nonneg := (onceLaw_isProbability E (dyadicBlock N) L).1
        right_nonneg := hU.1.1
        left_summable := hA.1.1
        right_summable := hU.2.1
        left_bound := hA.1.2
        right_bound := hU.2.2.trans hB }
  · exact
      { left_nonneg := (isolatedLaw_isProbability E (dyadicBlock N) L).1
        right_nonneg := hU.1.1
        left_summable := hA.2.1
        right_summable := hU.2.1
        left_bound := hA.2.2
        right_bound := hU.2.2.trans hB }

end PaperP1.PositionalDeletedBackgroundMoments
