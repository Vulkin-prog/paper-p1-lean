module

public import PaperP1.Arithmetic.AsymmetricEnvelopeRank
public import PaperP1.Asymptotics.AsymmetricComponentHostData

/-! # Actual target components split into original-window defects and nontrivial free components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricTargetComponents

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEnvelopeGraph
  PaperP1.AsymmetricEnvelopeRank PaperP1.AsymmetricComponentOffsets
  PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution
  PaperP1.TwoBlockComponentSquares

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def components (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  PinnedTargetRestriction.components (largePrimeGraph (start x R) (start y R) H)
    (pins x y L H R hnew hamb old) (targetPositions L H R hnew hamb)

def isolated (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (components x y L H R hnew hamb old).filter fun c ↦ Fintype.card c.supp = 1

def defective (y L H : ℕ) : Finset (Fin (L + 1)) :=
  univ.filter fun i ↦ DefectivePredicate.HDefective (10 * (H + 1)) (startCompleteVertexLabel y L i)

theorem mem_components (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ components x y L H R hnew hamb old ↔
      ¬ComponentPinned _ (pins x y L H R hnew hamb old) c ∧
        ∃ i : Fin (L + 1), (largePrimeGraph (start x R) (start y R) H).connectedComponentMk
          (Sum.inr (targetIndex L H R hnew hamb i)) = c := by
  rw [components, PinnedTargetRestriction.mem_components]
  constructor
  · rintro ⟨hfree, v, hv, he⟩
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hv
    exact ⟨hfree, i, he⟩
  · rintro ⟨hfree, i, he⟩
    exact ⟨hfree, _, mem_image.mpr ⟨i, mem_univ _, rfl⟩, he⟩

theorem support_eq_vertices (x y H R : ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    PinnedTargetBudget.support _ c = vertices (start x R) (start y R) H c := by
  ext v
  change v ∈ PinnedTargetBudget.support _ c ↔ v ∈ MediumPrimeColumns.componentVertices _ c
  rw [PinnedTargetBudget.mem_support, MediumPrimeColumns.mem_componentVertices]

theorem intersection_eq_right {x y L H R : ℕ} (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c) :
    PinnedTargetBudget.support _ c ∩ targetPositions L H R hnew hamb =
      ((vertices (start x R) (start y R) H c).toRight).image Sum.inr := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvC, hvT⟩ := mem_inter.mp hv
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hvT
    rw [support_eq_vertices] at hvC
    exact mem_image.mpr ⟨_, mem_toRight.mpr hvC, rfl⟩
  · intro hv
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    have hvC := mem_toRight.mp hj
    have hcomp := (MediumPrimeColumns.mem_componentVertices _ c _).mp hvC
    obtain ⟨i, hi⟩ := new_index_of_unpinned hnew hamb old c hfree j hcomp
    refine mem_inter.mpr ⟨?_, mem_image.mpr ⟨i, mem_univ _, congrArg Sum.inr hi⟩⟩
    rw [support_eq_vertices]
    exact hvC

theorem intersection_card {x y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c) :
    (PinnedTargetBudget.support _ c ∩ targetPositions L H R hnew hamb).card = (right x y H R c).card := by
  rw [intersection_eq_right hnew hamb old c hfree, card_image_of_injective _ Sum.inr_injective, right_card hy]

theorem componentCount_le (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    componentCount x y L H R hnew hamb old ≤
      (AsymmetricComponentHostData.nontrivial x y L H R hnew hamb old).card + (isolated x y L H R hnew hamb old).card := by
  have hsub : components x y L H R hnew hamb old ⊆
      AsymmetricComponentHostData.nontrivial x y L H R hnew hamb old ∪ isolated x y L H R hnew hamb old := by
    intro c hc
    obtain ⟨hfree, _hi⟩ := (mem_components x y L H R hnew hamb old c).mp hc
    have hp : 0 < Fintype.card c.supp := Fintype.card_pos_iff.mpr ⟨⟨c.out, c.out_eq⟩⟩
    by_cases htwo : 2 ≤ Fintype.card c.supp
    · exact mem_union_left _ ((AsymmetricComponentHostData.mem_nontrivial x y L H R hnew hamb old c).mpr ⟨hfree, htwo⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hc, by omega⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

theorem defective_of_isolated {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hc : c ∈ isolated x y L H R hnew hamb old) (i : Fin (L + 1))
    (hi : (largePrimeGraph (start x R) (start y R) H).connectedComponentMk
      (Sum.inr (targetIndex L H R hnew hamb i)) = c) :
    DefectivePredicate.HDefective (10 * (H + 1)) (startCompleteVertexLabel y L i) := by
  obtain ⟨hcT, hsize⟩ := mem_filter.mp hc
  have hfree := ((mem_components x y L H R hnew hamb old c).mp hcT).1
  have horig := original_unpinned hnew hamb old c hfree
  have hD := isDefective_of_isolatedUnpinnedComponent
    (by have hh := start_ge_two hx; omega) (by have hh := start_ge_two hy; omega) ⟨horig, hsize⟩
  have he : Sum.inr (targetIndex L H R hnew hamb i) = c.out := by
    have hh := (Fintype.card_le_one_iff.mp hsize.le)
      (⟨Sum.inr (targetIndex L H R hnew hamb i), hi⟩ : c.supp) ⟨c.out, c.out_eq⟩
    exact congrArg Subtype.val hh
  have hDv : IsDefective (start x R) (start y R) H (Sum.inr (targetIndex L H R hnew hamb i)) := he.symm ▸ hD
  have hn := (LargePrimeComponentArithmetic.isDefective_iff_intrinsic _).mp hDv
  simpa only [twoStartCompleteVertexLabel, target_label hy hnew hamb] using hn

theorem isolated_card {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    (isolated x y L H R hnew hamb old).card ≤ (defective y L H).card := by
  have hsub : isolated x y L H R hnew hamb old ⊆ (defective y L H).image
      (fun i ↦ (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inr (targetIndex L H R hnew hamb i))) := by
    intro c hc
    have hcT := (mem_filter.mp hc).1
    obtain ⟨_hfree, i, hi⟩ := (mem_components x y L H R hnew hamb old c).mp hcT
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, defective_of_isolated hx hy hnew hamb old c hc i hi⟩, hi⟩
  exact (card_le_card hsub).trans card_image_le

theorem loss_le_defects_add_components {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) :
    AsymmetricEvenLoss.loss H old y L ≤ (defective y L H).card +
      (AsymmetricComponentHostData.nontrivial x y L H R hnew hamb old).card := by
  have hrank := loss_le_components hx hy hnew hamb old hold
  have hbudget := componentCount_le x y L H R hnew hamb old
  have hiso := isolated_card hx hy hnew hamb old
  omega

end PaperP1.AsymmetricTargetComponents
