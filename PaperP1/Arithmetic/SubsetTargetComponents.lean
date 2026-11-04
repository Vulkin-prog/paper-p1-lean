module

public import PaperP1.Arithmetic.SubsetEnvelopeRank
public import PaperP1.Asymptotics.SubsetComponentHostData
public import PaperP1.Arithmetic.AsymmetricTargetComponents

/-! # Actual target components split into two-subset components and real defective values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetTargetComponents

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEnvelopeGraph PaperP1.SubsetEnvelopeGraph
  PaperP1.SubsetEnvelopeRank PaperP1.AsymmetricComponentOffsets PaperP1.LargePrimeGraph
  PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution PaperP1.LargePrimeOccurrences

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def components (x y H R : ℕ) (U V : Finset ℕ) :=
  PinnedTargetRestriction.components (largePrimeGraph (start x R) (start y R) H)
    (SubsetEnvelopeGraph.pins x y H R U V) (targets y H R V)

def isolated (x y H R : ℕ) (U V : Finset ℕ) :=
  (components x y H R U V).filter fun c ↦ Fintype.card c.supp = 1

def defective (y H R : ℕ) (V : Finset ℕ) : Finset (Fin (H + 1)) :=
  univ.filter fun j ↦ startCompleteVertexLabel (start y R) H j ∈ V ∧
    DefectivePredicate.HDefective (10 * (H + 1)) (startCompleteVertexLabel (start y R) H j)

theorem mem_components (x y H R : ℕ) (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ components x y H R U V ↔ ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c ∧
      ∃ j : Fin (H + 1), startCompleteVertexLabel (start y R) H j ∈ V ∧
        (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inr j) = c := by
  rw [components, PinnedTargetRestriction.mem_components]
  constructor
  · rintro ⟨hfree, v, hv, hvc⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    exact ⟨hfree, j, (mem_filter.mp hj).2, hvc⟩
  · rintro ⟨hfree, j, hj, hcomp⟩
    exact ⟨hfree, Sum.inr j, mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, rfl⟩, hcomp⟩

theorem intersection_eq_right {x y H R : ℕ} (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c) :
    PinnedTargetBudget.support _ c ∩ targets y H R V =
      ((TwoBlockComponentSquares.vertices (start x R) (start y R) H c).toRight).image Sum.inr := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvC, hvT⟩ := mem_inter.mp hv
    obtain ⟨j, _hj, rfl⟩ := mem_image.mp hvT
    rw [AsymmetricTargetComponents.support_eq_vertices] at hvC
    exact mem_image.mpr ⟨j, mem_toRight.mpr hvC, rfl⟩
  · intro hv
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    have hvC := mem_toRight.mp hj
    have hcomp := (MediumPrimeColumns.mem_componentVertices _ c _).mp hvC
    have hmem := SubsetEnvelopeGraph.new_mem_of_unpinned U V c hfree j hcomp
    refine mem_inter.mpr ⟨?_, mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hmem⟩, rfl⟩⟩
    rw [AsymmetricTargetComponents.support_eq_vertices]
    exact hvC

theorem intersection_card {x y H R : ℕ} (hy : R < y) (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c) :
    (PinnedTargetBudget.support _ c ∩ targets y H R V).card = (right x y H R c).card := by
  rw [intersection_eq_right U V c hfree, card_image_of_injective _ Sum.inr_injective, right_card hy]

theorem componentCount_le (x y H R : ℕ) (U V : Finset ℕ) :
    componentCount x y H R U V ≤ (SubsetComponentHostData.nontrivial x y H R U V).card + (isolated x y H R U V).card := by
  have hsub : components x y H R U V ⊆ SubsetComponentHostData.nontrivial x y H R U V ∪ isolated x y H R U V := by
    intro c hc
    have hfree := ((mem_components x y H R U V c).mp hc).1
    have hp : 0 < Fintype.card c.supp := Fintype.card_pos_iff.mpr ⟨⟨c.out, c.out_eq⟩⟩
    by_cases htwo : 2 ≤ Fintype.card c.supp
    · exact mem_union_left _ ((SubsetComponentHostData.mem_nontrivial x y H R U V c).mpr ⟨hfree, htwo⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hc, by omega⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

theorem defective_of_isolated {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hc : c ∈ isolated x y H R U V) (j : Fin (H + 1))
    (hj : (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inr j) = c) :
    DefectivePredicate.HDefective (10 * (H + 1)) (startCompleteVertexLabel (start y R) H j) := by
  obtain ⟨hcT, hsize⟩ := mem_filter.mp hc
  have hfree := ((mem_components x y H R U V c).mp hcT).1
  have horig := SubsetEnvelopeGraph.original_unpinned U V c hfree
  have hD := isDefective_of_isolatedUnpinnedComponent (by have hh := start_ge_two hx; omega)
    (by have hh := start_ge_two hy; omega) ⟨horig, hsize⟩
  have he : Sum.inr j = c.out := by
    have hh := (Fintype.card_le_one_iff.mp hsize.le) (⟨Sum.inr j, hj⟩ : c.supp) ⟨c.out, c.out_eq⟩
    exact congrArg Subtype.val hh
  have hDv : IsDefective (start x R) (start y R) H (Sum.inr j) := he.symm ▸ hD
  have hn := (LargePrimeComponentArithmetic.isDefective_iff_intrinsic _).mp hDv
  simpa only [twoStartCompleteVertexLabel] using hn

theorem isolated_card {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ) :
    (isolated x y H R U V).card ≤ (defective y H R V).card := by
  have hsub : isolated x y H R U V ⊆ (defective y H R V).image
      (fun j ↦ (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inr j)) := by
    intro c hc
    obtain ⟨_hfree, j, hjV, hj⟩ := (mem_components x y H R U V c).mp (mem_filter.mp hc).1
    exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hjV, defective_of_isolated hx hy U V c hc j hj⟩, hj⟩
  exact (card_le_card hsub).trans card_image_le

theorem defective_card_le_values {y H R : ℕ} (hy : R < y) (V : Finset ℕ) :
    (defective y H R V).card ≤ (V.filter (DefectivePredicate.HDefective (10 * (H + 1)))).card := by
  have hinj := startCompleteVertexLabel_injective (x := start y R) (L := H)
    (by have hh := start_ge_two hy; omega)
  have hsub : (defective y H R V).image (startCompleteVertexLabel (start y R) H) ⊆
      V.filter (DefectivePredicate.HDefective (10 * (H + 1))) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    exact mem_filter.mpr (mem_filter.mp hj).2
  exact (card_image_of_injective _ hinj).symm.trans_le (card_le_card hsub)

theorem loss_le_defects_add_components {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (hU : U ⊆ Ico (x - R) (x - R + (H + 1))) (hV : V ⊆ Ico (y - R) (y - R + (H + 1))) :
    SubsetEvenLoss.loss H U V ≤ (defective y H R V).card + (SubsetComponentHostData.nontrivial x y H R U V).card := by
  have hrank := loss_le_components hx hy U V hU hV
  have hbudget := componentCount_le x y H R U V
  have hiso := isolated_card (H := H) hx hy U V
  omega

end PaperP1.SubsetTargetComponents
