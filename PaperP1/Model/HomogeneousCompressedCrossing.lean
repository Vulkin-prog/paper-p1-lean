module

public import PaperP1.Model.HomogeneousBlockIntersection

/-! # A homogeneous source/target crossing on the actual normalized compressed block -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousCompressedCrossing

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.SubspaceFamilyRank
  PaperP1.AsymmetricEvenLoss PaperP1.HomogeneousRunMass

theorem finite_bound {N a b L H : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ DyadicEndpointPairs.sourcePairs N a b L i j)
    (z : ℕ) (hcross : 0 < AsymmetricJointWeight.crossRank xy.1 xy.2 z L) :
    probability L {xy.1, xy.2, z} ≤
      2 * (probability L {xy.1, xy.2} * probability L {z}) *
        ((2 ^ loss H (CompressedSourceBlocks.block N a b L i j (CompressedSourceBlocks.anchor b L i xy)) z L : ℝ) - 1) := by
  have hspan : span (fun x ↦ squareClassSpace x L) {xy.1, xy.2} = squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
    rw [span_insert]
    simp [span]
  have hspace : span (fun x ↦ squareClassSpace x L) {xy.1, xy.2} =
      FiniteEvenSquareClasses.space (CompressedSourceBlocks.block N a b L i j (CompressedSourceBlocks.anchor b L i xy)) := by
    rw [hspan, CompressedSourceBlocks.space_eq hN ha hb i j hxy]
  have hcross' : 0 < Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) {xy.1, xy.2} ⊓ squareClassSpace z L) := by
    rw [hspan]
    exact hcross
  have hset : ({xy.1, xy.2} : Finset ℕ) ∪ {z} = {xy.1, xy.2, z} := by
    ext v
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  simpa only [hset] using HomogeneousBlockIntersection.crossing L H {xy.1, xy.2}
    (CompressedSourceBlocks.block N a b L i j (CompressedSourceBlocks.anchor b L i xy)) z hspace hcross'

end PaperP1.HomogeneousCompressedCrossing
