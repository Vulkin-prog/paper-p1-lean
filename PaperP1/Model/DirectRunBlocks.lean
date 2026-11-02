module

public import PaperP1.Affine.DisjointBlockNullity
public import PaperP1.Affine.FinitePartPreimage
public import PaperP1.Model.FinitePartMoments
public import PaperP1.Model.PositiveMarginalRestriction
public import PaperP1.Model.ConnectedWindowFamilies

/-! # Exact original-model factorization across two direct, possibly internally dependent blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectRunBlocks

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem additive_iff_spaces (L : ℕ) (e f : Finset ℕ) (hef : Disjoint e f) :
    runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f ↔
      Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) f) :=
  DisjointBlockNullity.additive_iff_disjoint (fun x ↦ squareClassSpace x L) e f hef

theorem exists_partition (L : ℕ) (e f : Finset ℕ) (he : e.Nonempty) (hf : f.Nonempty)
    (hef : Disjoint e f)
    (hnull : runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f) :
    ∃ (P : Finpartition (univ : Finset ↥(e ∪ f))) (C D : Finset ↥(e ∪ f)),
      RelationDirectPartition (fun i : ↥(e ∪ f) ↦ squareClassSpace i.val L) P ∧
      P.parts = {C, D} ∧ C ≠ D ∧ FinitePartImage.image C = e ∧ FinitePartImage.image D = f := by
  classical
  let I := e ∪ f
  let S := fun i : I ↦ squareClassSpace i.val L
  let C := FinitePartPreimage.part I e
  let D := FinitePartPreimage.part I f
  have hC : C.Nonempty := FinitePartPreimage.part_nonempty I e subset_union_left he
  have hD : D.Nonempty := FinitePartPreimage.part_nonempty I f subset_union_right hf
  have hCD : Disjoint C D := FinitePartPreimage.parts_disjoint I e f hef
  have hcover : C ∪ D = univ := FinitePartPreimage.parts_union I e f rfl
  have hCe : FinitePartImage.image C = e := FinitePartPreimage.image_part I e subset_union_left
  have hDf : FinitePartImage.image D = f := FinitePartPreimage.image_part I f subset_union_right
  have hspaces : Disjoint (span S C) (span S D) := by
    dsimp only [S]
    rw [FinitePartPreimage.span_image (fun x ↦ squareClassSpace x L) C,
      FinitePartPreimage.span_image (fun x ↦ squareClassSpace x L) D, hCe, hDf]
    exact (additive_iff_spaces L e f hef).mp hnull
  let P := DisjointBlockNullity.twoPartPartition C D hC hD hCD hcover
  have hne : C ≠ D := by
    intro h
    obtain ⟨i, hi⟩ := hC
    exact disjoint_left.mp hCD hi (h ▸ hi)
  refine ⟨P, C, D, DisjointBlockNullity.twoPartPartition_respects S C D hC hD hCD hcover hspaces,
    ?_, hne, hCe, hDf⟩
  exact pair_comm _ _

set_option maxHeartbeats 1000000 in
theorem centered_factor_positive (L : ℕ) (hL : 0 < L) (e f : Finset ℕ)
    (he : e.Nonempty) (hf : f.Nonempty) (hef : Disjoint e f)
    (hnull : runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f)
    (hp : ∀ x ∈ e ∪ f, 0 < infiniteMarginal x L) :
    infiniteCenteredCoefficient L (e ∪ f) =
      infiniteCenteredCoefficient L e * infiniteCenteredCoefficient L f := by
  classical
  let I := e ∪ f
  let M := I.sup fun x ↦ x + L
  obtain ⟨P, C, D, hP, hparts, hCD, hCe, hDf⟩ := exists_partition L e f he hf hef hnull
  have hcut (i : I) : i.val + L ≤ M := le_sup (f := fun x ↦ x + L) i.property
  calc
    _ = infiniteFamilyCenteredMoment L (fun i : I ↦ i.val) := infiniteCenteredCoefficient_eq_family_subtype L I
    _ = ∏ E : P.parts, infiniteFamilyCenteredMoment L (fun i : E.val ↦ i.val.val) :=
      infiniteFamilyCenteredMoment_partition M L (fun i : I ↦ i.val) hL hcut
        (fun i ↦ hp i.val i.property) P hP
    _ = ∏ E : P.parts, infiniteCenteredCoefficient L (FinitePartImage.image E.val) := by
      apply prod_congr rfl
      intro E _
      exact (FinitePartMoments.centered_image L E.val).symm
    _ = ∏ E ∈ P.parts, infiniteCenteredCoefficient L (FinitePartImage.image E) :=
      prod_coe_sort P.parts (fun E : Finset I ↦ infiniteCenteredCoefficient L (FinitePartImage.image E))
    _ = _ := by rw [hparts, prod_pair hCD, hCe, hDf]

theorem centered_factor (L : ℕ) (hL : 0 < L) (e f : Finset ℕ)
    (he : e.Nonempty) (hf : f.Nonempty) (hef : Disjoint e f)
    (hnull : runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f) :
    infiniteCenteredCoefficient L (e ∪ f) =
      infiniteCenteredCoefficient L e * infiniteCenteredCoefficient L f := by
  classical
  by_cases hp : ∀ x ∈ e ∪ f, 0 < infiniteMarginal x L
  · exact centered_factor_positive L hL e f he hf hef hnull hp
  · push Not at hp
    obtain ⟨x, hx, hpx⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hpx
      (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    rw [PositiveMarginalRestriction.zero_centered L (e ∪ f) x hx hz]
    rcases mem_union.mp hx with hxe | hxf
    · rw [PositiveMarginalRestriction.zero_centered L e x hxe hz, zero_mul]
    · rw [PositiveMarginalRestriction.zero_centered L f x hxf hz, mul_zero]

theorem not_connected (L : ℕ) (e f : Finset ℕ) (he : e.Nonempty) (hf : f.Nonempty)
    (hef : Disjoint e f)
    (hnull : runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f) :
    ¬ConnectedWindowFamilies.Connected L (e ∪ f) := by
  classical
  let I := e ∪ f
  let S := fun i : I ↦ squareClassSpace i.val L
  let C := FinitePartPreimage.part I e
  let D := FinitePartPreimage.part I f
  have hCe : FinitePartImage.image C = e := FinitePartPreimage.image_part I e subset_union_left
  have hDf : FinitePartImage.image D = f := FinitePartPreimage.image_part I f subset_union_right
  have hspaces : Disjoint (span S C) (span S D) := by
    dsimp only [S]
    rw [FinitePartPreimage.span_image (fun x ↦ squareClassSpace x L) C,
      FinitePartPreimage.span_image (fun x ↦ squareClassSpace x L) D, hCe, hDf]
    exact (additive_iff_spaces L e f hef).mp hnull
  exact DisjointBlockNullity.cut_not_connected S C D
    (FinitePartPreimage.part_nonempty I e subset_union_left he)
    (FinitePartPreimage.part_nonempty I f subset_union_right hf)
    (FinitePartPreimage.parts_disjoint I e f hef)
    (FinitePartPreimage.parts_union I e f rfl) hspaces

end PaperP1.DirectRunBlocks
