module

public import PaperP1.Model.ChosenRelationCore
public import PaperP1.Model.RelationCoreMomentRatio

/-! # A sublinear original family retains positive rank in its chosen small core -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCoreRankRetention

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.ChosenRelationCore

theorem rank_retained (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hsize : (I.card : ℝ) ≤ (L : ℝ) / 960)
    (hhigh : (L : ℝ) / 60 < (runCompatibleNullity L I : ℝ)) :
    (L : ℝ) / 120 < (runRelativeNullity L (core L I) : ℝ) := by
  have h := (properties L hL I).2.2.2.1
  have hcost : 8 * (I.card - (core L I).card) ≤ 8 * I.card :=
    Nat.mul_le_mul_left 8 (Nat.sub_le _ _)
  have hbudget : runCompatibleNullity L I ≤ runRelativeNullity L (core L I) + 8 * I.card := by omega
  have hbudgetR : (runCompatibleNullity L I : ℝ) ≤
      (runRelativeNullity L (core L I) : ℝ) + 8 * I.card := by exact_mod_cast hbudget
  linarith only [hbudgetR, hsize, hhigh]

theorem size_two (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hsize : (I.card : ℝ) ≤ (L : ℝ) / 960)
    (hhigh : (L : ℝ) / 60 < (runCompatibleNullity L I : ℝ)) : 2 ≤ (core L I).card := by
  have hrank := rank_retained L hL I hsize hhigh
  by_contra hcard
  have hz := PaperP1.RetainedNullity.nullity_card_le_one (fun x ↦ squareClassSpace x L)
    (core L I) (by omega)
  change runRelativeNullity L (core L I) = 0 at hz
  rw [hz, Nat.cast_zero] at hrank
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  linarith

theorem small_core_properties (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hsize : (I.card : ℝ) ≤ (L : ℝ) / 960)
    (hhigh : (L : ℝ) / 60 < (runCompatibleNullity L I : ℝ))
    (hlarge : 256 < I.card) (hsmall : (core L I).card < 256) :
    2 ≤ (core L I).card ∧ core L I ⊂ I ∧
      infiniteJointMoment L (core L I) ≤ 2 * infiniteCenteredCoefficient L (core L I) := by
  have hp := properties L hL I
  refine ⟨size_two L hL I hsize hhigh, ?_, ?_⟩
  · apply ssubset_iff_subset_ne.mpr
    refine ⟨hp.1, ?_⟩
    intro heq
    have hcard := congrArg Finset.card heq
    omega
  · exact PaperP1.RelationCoreMomentRatio.ten_core_ratio L (core L I) hL hp.2.2.1 (by omega) hp.2.1

end PaperP1.SmallCoreRankRetention
