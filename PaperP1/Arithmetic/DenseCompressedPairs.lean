module

public import PaperP1.Arithmetic.CompressedTargetCenters

/-! # Actual dense exact-unit target pairs inject into their compressed centers at each offset pattern -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseCompressedPairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

def atOffsets (N a b L : ℕ) (i j : Fin (L + 1)) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (DyadicEndpointPairs.sourcePairs N a b L i j).filter fun xy ↦
    η * L ≤ (Module.finrank F₂ ↥(W ⊓ (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)) : ℝ)

def pairs (N a b L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦
    (NormalizedUnitCount.units a b xy.1 xy.2 L).Nonempty ∧
      η * L ≤ (Module.finrank F₂ ↥(W ⊓ (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)) : ℝ)

theorem mem_pairs (N a b L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) (xy : ℕ × ℕ) :
    xy ∈ pairs N a b L W η ↔ xy.1 ∈ dyadicBlock N ∧ xy.2 ∈ dyadicBlock N ∧
      (NormalizedUnitCount.units a b xy.1 xy.2 L).Nonempty ∧
      η * L ≤ (Module.finrank F₂ ↥(W ⊓ (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)) : ℝ) := by
  classical
  simp only [pairs, mem_filter, mem_product]
  tauto

theorem cover (N a b L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) :
    pairs N a b L W η ⊆ univ.biUnion
      (fun ij : Fin (L + 1) × Fin (L + 1) ↦ atOffsets N a b L ij.1 ij.2 W η) := by
  classical
  intro xy hxy
  obtain ⟨hx, hy, hunit, hdense⟩ := (mem_pairs N a b L W η xy).mp hxy
  obtain ⟨ij, hu⟩ := hunit
  apply mem_biUnion.mpr
  refine ⟨ij, mem_univ _, mem_filter.mpr ⟨?_, hdense⟩⟩
  exact DyadicEndpointPairs.mem_sourcePairs.mpr ⟨hx, hy, NormalizedUnitCount.mem_units.mp hu⟩

theorem offset_card_le {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) :
    (atOffsets N a b L i j W η).card ≤ (CompressedTargetCenters.denseCenters N a b L i j W η).card := by
  classical
  apply card_le_card_of_injOn (CompressedSourceBlocks.anchor b L i)
  · intro xy hxy
    obtain ⟨hsource, hdense⟩ := mem_filter.mp hxy
    apply (CompressedTargetCenters.mem_dense_centers N a b L i j W η _).mpr
    refine ⟨mem_image.mpr ⟨xy, hsource, rfl⟩, ?_⟩
    rw [CompressedSourceBlocks.space_eq hN ha hb i j hsource]
    exact hdense
  · intro xy hxy uv huv heq
    exact DyadicEndpointPairs.first_anchor_injective (by omega) ha hb i j
      (mem_filter.mp hxy).1 (mem_filter.mp huv).1 heq

theorem finite_card_bound {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) :
    (pairs N a b L W η).card ≤
      ∑ ij : Fin (L + 1) × Fin (L + 1), (CompressedTargetCenters.denseCenters N a b L ij.1 ij.2 W η).card := by
  classical
  calc
    _ ≤ (univ.biUnion (fun ij : Fin (L + 1) × Fin (L + 1) ↦ atOffsets N a b L ij.1 ij.2 W η)).card :=
      card_le_card (cover N a b L W η)
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), (atOffsets N a b L ij.1 ij.2 W η).card := card_biUnion_le
    _ ≤ _ := sum_le_sum fun ij _ ↦ offset_card_le hN ha hb ij.1 ij.2 W η

end PaperP1.DenseCompressedPairs
