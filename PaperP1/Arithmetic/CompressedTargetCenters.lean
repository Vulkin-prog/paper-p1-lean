module

public import PaperP1.Arithmetic.CompressedSourceBlocks

/-! # Actual compressed centers of a fixed channel, their bounded width and their literal dense population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedTargetCenters

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.DyadicEndpointPairs
  PaperP1.CompressedSourceBlocks

local instance compressedCentersPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def centers (N a b L : ℕ) (i j : Fin (L + 1)) : Finset ℕ :=
  (sourcePairs N a b L i j).image (anchor b L i)

def denseCenters (N a b L : ℕ) (i j : Fin (L + 1)) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) : Finset ℕ := by
  classical
  exact (centers N a b L i j).filter fun X ↦
    η * L ≤ (Module.finrank F₂ ↥(W ⊓ FiniteEvenSquareClasses.space (block N a b L i j X)) : ℝ)

def allDenseCenters (N a b L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) : Finset ℕ :=
  univ.biUnion fun ij : Fin (L + 1) × Fin (L + 1) ↦ denseCenters N a b L ij.1 ij.2 W η

theorem mem_dense_centers (N a b L : ℕ) (i j : Fin (L + 1)) (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ) (X : ℕ) :
    X ∈ denseCenters N a b L i j W η ↔ X ∈ centers N a b L i j ∧
      η * L ≤ (Module.finrank F₂ ↥(W ⊓ FiniteEvenSquareClasses.space (block N a b L i j X)) : ℝ) := by
  classical
  exact mem_filter

theorem block_width {N a b L X : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (i j : Fin (L + 1)) {n : ℕ} (hn : n ∈ block N a b L i j X) :
    ((n : ℤ) - X).natAbs ≤ b * (L + 1) := by
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hsource, hanchor⟩ := mem_filter.mp hxy
  have habs := source_abs_bound hN hab i j hsource hnu
  rw [hanchor, Int.abs_eq_natAbs] at habs
  have hnat : ((n : ℤ) - X).natAbs ≤ b * L := by exact_mod_cast habs
  exact hnat.trans (Nat.mul_le_mul_left b (Nat.le_succ L))

theorem center_bounds {N a b L X : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hb : 0 < b)
    (i j : Fin (L + 1)) (hX : X ∈ centers N a b L i j) :
    (1 / 2 : ℝ) * N ≤ X ∧ (X : ℝ) ≤ (3 * (b : ℝ)) * N := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hX
  have hx := (mem_sourcePairs.mp hxy).1
  have hraw := (OriginalWindowValueBounds.values_geometry N L xy.1 hN (mem_Ico.mp hx) hLN
    (startCompleteVertexLabel xy.1 L i) (NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩)).1
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlo := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg (α := ℝ) (startCompleteVertexLabel xy.1 L i))
  have hhi := mul_le_mul_of_nonneg_left hraw.2 (Nat.cast_nonneg (α := ℝ) b)
  unfold anchor
  push_cast
  exact ⟨hraw.1.trans (by simpa only [one_mul] using hlo), by nlinarith only [hhi]⟩

theorem actual_pair_mem {N a b L x y : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) (hxy : (x, y) ∈ sourcePairs N a b L i j)
    (W : Submodule F₂ (ℕ →₀ F₂)) (η : ℝ)
    (hdense : η * L ≤ (Module.finrank F₂ ↥(W ⊓ FiniteEvenSquareClasses.space
      (NormalizedWindowSets.union a b x y L)) : ℝ)) :
    anchor b L i (x, y) ∈ allDenseCenters N a b L W η := by
  apply mem_biUnion.mpr
  refine ⟨(i, j), mem_univ _, (mem_dense_centers N a b L i j W η _).mpr ⟨?_, ?_⟩⟩
  · exact mem_image.mpr ⟨(x, y), hxy, rfl⟩
  · rw [block_eq (by omega : 0 < N) ha hb i j hxy]
    exact hdense

end PaperP1.CompressedTargetCenters
