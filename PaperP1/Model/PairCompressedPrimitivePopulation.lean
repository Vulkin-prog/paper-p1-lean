module

public import PaperP1.Model.PairCompressedPrimitiveFamilies
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Actual ordered populations and unit-offset covers after pair compression -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedPrimitivePopulation

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PairCompressedPrimitiveFamilies
  PaperP1.FixedChannelSourceGeometry PaperP1.DyadicEndpointPairs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def targets (N L t : ℕ) : Finset (Fin t → ℕ) :=
  Fintype.piFinset fun _ ↦ RegularStarts.regularStarts N L

def points (N a b L t : ℕ) : Finset ((ℕ × ℕ) × (Fin t → ℕ)) :=
  ((unitSources N a b L) ×ˢ targets N L t).filter fun p ↦
    Function.Injective p.2 ∧ Primitive p.1 L p.2

def fixedPoints (N a b L t : ℕ) (i j : Fin (L + 1)) :
    Finset ((ℕ × ℕ) × (Fin t → ℕ)) :=
  ((sourcePairs N a b L i j) ×ˢ targets N L t).filter fun p ↦
    Function.Injective p.2 ∧ Primitive p.1 L p.2

def mass (N a b L t : ℕ) : ℝ :=
  ∑ p ∈ points N a b L t, HomogeneousRunMass.probability L (family p.1 p.2)

theorem mem_points {N a b L t : ℕ} {p : (ℕ × ℕ) × (Fin t → ℕ)} :
    p ∈ points N a b L t ↔ p.1 ∈ unitSources N a b L ∧
      (∀ i, p.2 i ∈ RegularStarts.regularStarts N L) ∧
      Function.Injective p.2 ∧ Primitive p.1 L p.2 := by
  simp only [points, mem_filter, mem_product, targets, Fintype.mem_piFinset, and_assoc]

theorem mem_fixedPoints {N a b L t : ℕ} {i j : Fin (L + 1)}
    {p : (ℕ × ℕ) × (Fin t → ℕ)} :
    p ∈ fixedPoints N a b L t i j ↔ p.1 ∈ sourcePairs N a b L i j ∧
      (∀ k, p.2 k ∈ RegularStarts.regularStarts N L) ∧
      Function.Injective p.2 ∧ Primitive p.1 L p.2 := by
  simp only [fixedPoints, mem_filter, mem_product, targets, Fintype.mem_piFinset, and_assoc]

theorem offsets_cover (N a b L t : ℕ) : points N a b L t ⊆
    univ.biUnion fun ij : Fin (L + 1) × Fin (L + 1) ↦ fixedPoints N a b L t ij.1 ij.2 := by
  intro p hp
  obtain ⟨hsource, hz, hinj, hprim⟩ := mem_points.mp hp
  obtain ⟨hblock, u, hu⟩ := mem_filter.mp hsource
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact mem_biUnion.mpr ⟨u, mem_univ _, mem_fixedPoints.mpr
    ⟨mem_sourcePairs.mpr ⟨hx, hy, PaperP1.NormalizedUnitCount.mem_units.mp hu⟩, hz, hinj, hprim⟩⟩

theorem sum_le_offsets (N a b L t : ℕ) (w : ((ℕ × ℕ) × (Fin t → ℕ)) → ℝ)
    (hw : ∀ p, 0 ≤ w p) :
    (∑ p ∈ points N a b L t, w p) ≤
      ∑ ij : Fin (L + 1) × Fin (L + 1), ∑ p ∈ fixedPoints N a b L t ij.1 ij.2, w p := by
  exact (sum_le_sum_of_subset_of_nonneg (offsets_cover N a b L t)
    (fun p _ _ ↦ hw p)).trans (GraphStarWeights.sum_biUnion_le_nonneg univ _ w hw)

end PaperP1.PairCompressedPrimitivePopulation
