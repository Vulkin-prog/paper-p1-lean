module

public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Affine.RelativeIntersectionNullity

/-! # An exact source joint factor times heterogeneous independent targets and their actual relative rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExtensionJointFactor

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem exact_of_positive (L : ℕ) (hL : 0 < L) (E A : Finset ℕ) (hEA : Disjoint E A)
    (hq : 0 < infiniteJointMoment L (E ∪ A)) :
    infiniteJointMoment L (E ∪ A) = infiniteJointMoment L E *
      ((∏ x ∈ A, infiniteMarginal x L) *
        (2 ^ MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) E)
          (fun x ↦ squareClassSpace x L) A : ℝ)) := by
  have hqE : 0 < infiniteJointMoment L E :=
    hq.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L subset_union_left)
  have hfull := infiniteJointMoment_exact_of_pos ((E ∪ A).sup fun x ↦ x + L) L (E ∪ A) hL
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq
  have hsource := infiniteJointMoment_exact_of_pos (E.sup fun x ↦ x + L) L E hL
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hqE
  rw [hfull, hsource, prod_union hEA, MinimalRelativeRelations.source_union_identity _ E A hEA, pow_add]
  ring

theorem upper_bound (L : ℕ) (hL : 0 < L) (E A : Finset ℕ) (hEA : Disjoint E A) :
    infiniteJointMoment L (E ∪ A) ≤ infiniteJointMoment L E *
      ((∏ x ∈ A, infiniteMarginal x L) *
        (2 ^ MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) E)
          (fun x ↦ squareClassSpace x L) A : ℝ)) := by
  by_cases hq : 0 < infiniteJointMoment L (E ∪ A)
  · exact (exact_of_positive L hL E A hEA hq).le
  · apply (le_of_not_gt hq).trans
    exact mul_nonneg (infiniteJointMoment_nonneg L E)
      (mul_nonneg (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        (pow_nonneg (by norm_num) _))

end PaperP1.ExtensionJointFactor
