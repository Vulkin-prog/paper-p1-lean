module

public import PaperP1.Model.CanonicalRunComponents
public import PaperP1.Affine.FinitePartImage

/-! # Original infinite-model moments are unchanged by finite-part reindexing -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePartMoments

open PaperP1.Model.InfiniteStarts PaperP1.Probability

variable {B : Finset ℕ}

theorem joint_image (L : ℕ) (C : Finset B) :
    infiniteJointMoment L (FinitePartImage.image C) =
      infiniteFamilyJointMoment L (fun i : C ↦ i.val.val) := by
  rw [infiniteJointMoment_eq_family_subtype]
  unfold infiniteFamilyJointMoment
  congr 1
  funext ω
  exact (FinitePartImage.prod_equiv C
    (fun x ↦ (indicatorValue (infiniteStartIndicator x L ω) : ℝ))).symm

theorem centered_image (L : ℕ) (C : Finset B) :
    infiniteCenteredCoefficient L (FinitePartImage.image C) =
      infiniteFamilyCenteredMoment L (fun i : C ↦ i.val.val) := by
  rw [infiniteCenteredCoefficient_eq_family_subtype]
  unfold infiniteFamilyCenteredMoment
  congr 1
  funext ω
  exact (FinitePartImage.prod_equiv C
    (fun x ↦ (indicatorValue (infiniteStartIndicator x L ω) : ℝ) - infiniteMarginal x L)).symm

end PaperP1.FinitePartMoments
