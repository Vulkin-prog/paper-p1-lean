module

public import PaperP1.Model.CompressedPrimitiveHomogeneousBounds
public import PaperP1.Combinatorics.GraphStarWeights

/-! # All-cardinality primitive target sets with an actual unit source pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelCompressedPrimitiveSets

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedChannelSourceGeometry PaperP1.DyadicEndpointPairs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def targets (N L s : ℕ) (xy : ℕ × ℕ) : Finset (Finset ℕ) :=
  (RegularStarts.regularStarts N L).powerset.filter fun A ↦
    s ≤ A.card ∧ PairPrimitiveCompression.Primitive L {xy.1, xy.2} A

def weight (L : ℕ) (w : ℝ) (xy : ℕ × ℕ) (A : Finset ℕ) : ℝ :=
  w ^ (A.card + 2) * HomogeneousRunMass.probability L ({xy.1, xy.2} ∪ A)

def mass (N a b L s : ℕ) (w : ℝ) : ℝ :=
  ∑ xy ∈ unitSources N a b L, ∑ A ∈ targets N L s xy, weight L w xy A

def points (N a b L s : ℕ) : Finset ((ℕ × ℕ) × Finset ℕ) :=
  ((unitSources N a b L) ×ˢ (RegularStarts.regularStarts N L).powerset).filter fun p ↦
    s ≤ p.2.card ∧ PairPrimitiveCompression.Primitive L {p.1.1, p.1.2} p.2

def fixedMass (N a b L s : ℕ) (w : ℝ) (i j : Fin (L + 1)) : ℝ :=
  ∑ xy ∈ sourcePairs N a b L i j, ∑ A ∈ targets N L s xy, weight L w xy A

theorem mem_targets {N L s : ℕ} {xy : ℕ × ℕ} {A : Finset ℕ} :
    A ∈ targets N L s xy ↔ A ⊆ RegularStarts.regularStarts N L ∧
      s ≤ A.card ∧ PairPrimitiveCompression.Primitive L {xy.1, xy.2} A := by
  simp only [targets, mem_filter, mem_powerset]

theorem mem_points {N a b L s : ℕ} {p : (ℕ × ℕ) × Finset ℕ} :
    p ∈ points N a b L s ↔ p.1 ∈ unitSources N a b L ∧
      p.2 ⊆ RegularStarts.regularStarts N L ∧ s ≤ p.2.card ∧
      PairPrimitiveCompression.Primitive L {p.1.1, p.1.2} p.2 := by
  simp only [points, mem_filter, mem_product, mem_powerset, and_assoc]

theorem mass_eq_points (N a b L s : ℕ) (w : ℝ) :
    mass N a b L s w = ∑ p ∈ points N a b L s, weight L w p.1 p.2 := by
  simp only [mass, targets, points, sum_filter, sum_product]

theorem weight_nonneg (L : ℕ) (w : ℝ) (hw : 0 ≤ w) (xy : ℕ × ℕ) (A : Finset ℕ) :
    0 ≤ weight L w xy A := mul_nonneg (pow_nonneg hw _) (HomogeneousRunMass.probability_pos L _).le

theorem mass_le_offsets (N a b L s : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    mass N a b L s w ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), fixedMass N a b L s w ij.1 ij.2 := by
  let f := fun xy : ℕ × ℕ ↦ ∑ A ∈ targets N L s xy, weight L w xy A
  have hf : ∀ xy, 0 ≤ f xy := fun xy ↦ sum_nonneg fun A _ ↦ weight_nonneg L w hw xy A
  have hcover : unitSources N a b L ⊆ univ.biUnion
      (fun ij : Fin (L + 1) × Fin (L + 1) ↦ sourcePairs N a b L ij.1 ij.2) := by
    intro xy hxy
    obtain ⟨hblock, ij, hij⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    exact mem_biUnion.mpr ⟨ij, mem_univ _, mem_sourcePairs.mpr
      ⟨hx, hy, PaperP1.NormalizedUnitCount.mem_units.mp hij⟩⟩
  exact (sum_le_sum_of_subset_of_nonneg hcover (fun xy _ _ ↦ hf xy)).trans
    (GraphStarWeights.sum_biUnion_le_nonneg univ _ f hf)

end PaperP1.ChannelCompressedPrimitiveSets
