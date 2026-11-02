module

public import PaperP1.Combinatorics.ClosePairs
public import PaperP1.Model.CompatibleWindowOverlap
public import PaperP1.Model.JointTupleSupport
public import PaperP1.Model.ContactPairMass

/-! # Positive actual close-pair seeds are exact endpoint contacts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactFamilySeeds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem positive_exact {L x y : ℕ} (hL : 0 < L) (hxy : x < y) (hyL : y ≤ x + L)
    (hq : 0 < infiniteJointMoment L {x, y}) : y = x + L := by
  have hsep := CompatibleWindowOverlap.compatible_pair_separated (ne_of_lt hxy) hL hq
  rcases hsep with h | h <;> omega

theorem positive_cover (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    (ClosePairs.pairs G L).filter (fun e ↦ infiniteJointMoment L e ≠ 0) ⊆
      G.image (fun x ↦ {x, x + L}) := by
  classical
  intro e he
  obtain ⟨he, hq⟩ := mem_filter.mp he
  obtain ⟨x, y, hx, _hy, hxy, hyL, rfl⟩ := ClosePairs.data G L e he
  have hy := positive_exact hL hxy hyL
    (lt_of_le_of_ne (infiniteJointMoment_nonneg L {x, y}) (Ne.symm hq))
  exact mem_image.mpr ⟨x, hx, by rw [hy]⟩

theorem joint_sum_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    (∑ e ∈ ClosePairs.pairs G L, infiniteJointMoment L e) ≤
      ∑ x ∈ G, infiniteJointMoment L {x, x + L} := by
  classical
  calc
    _ = ∑ e ∈ (ClosePairs.pairs G L).filter (fun e ↦ infiniteJointMoment L e ≠ 0), infiniteJointMoment L e := by
      symm
      apply sum_subset (filter_subset _ _)
      intro e he hnot
      by_contra hne
      exact hnot (mem_filter.mpr ⟨he, hne⟩)
    _ ≤ ∑ e ∈ G.image (fun x ↦ {x, x + L}), infiniteJointMoment L e :=
      sum_le_sum_of_subset_of_nonneg (positive_cover G L hL) (fun e _ _ ↦ infiniteJointMoment_nonneg L e)
    _ ≤ _ := sum_image_le_of_nonneg (fun e _ ↦ infiniteJointMoment_nonneg L e)

theorem prescribed_contact (L : ℕ) (hL : 0 < L) (x : ℕ) :
    PrescribedTupleMass.joint L (fun _ ↦ Affine.startRhs L) (ContactPairMass.pair x (x + L)) =
      infiniteJointMoment L {x, x + L} := by
  rw [JointTupleSupport.prescribed_eq_support _ hL]
  congr 1
  simp [FiniteFamilyEnumeration.tupleSet, ContactPairMass.pair, Finset.univ_fin2]

end PaperP1.ContactFamilySeeds
