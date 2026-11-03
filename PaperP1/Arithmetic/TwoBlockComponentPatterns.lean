module

public import PaperP1.Arithmetic.TwoBlockComponentSquares
public import PaperP1.Arithmetic.PositiveLineOffsetRoots
public import PaperP1.Arithmetic.SplitRadicalPatternPool
public import PaperP1.Arithmetic.SplitRadicalPointHeight

/-! # Literal offset sets, integer roots and smooth patterns of actual two-window components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoBlockComponentPatterns

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeOccurrences
  PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution
  PaperP1.DefectivePredicate PaperP1.TwoBlockComponentSquares PaperP1.PositiveLineOffsetRoots
  PaperP1.SplitRadicalPointHeight

def leftOffsets (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) : Finset ℤ :=
  integerOffsets (vertices x y L c).toLeft

def rightOffsets (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) : Finset ℤ :=
  integerOffsets (vertices x y L c).toRight

theorem left_card (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    (leftOffsets x y L c).card = (vertices x y L c).toLeft.card :=
  card_image_of_injective _ (integerOffset_injective L)

theorem right_card (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    (rightOffsets x y L c).card = (vertices x y L c).toRight.card :=
  card_image_of_injective _ (integerOffset_injective L)

theorem integerOffset_bound {L : ℕ} (u : Fin (L + 1)) : (integerOffset u).natAbs ≤ L + 1 := by
  have habs : |integerOffset u| ≤ ((L + 1 : ℕ) : ℤ) := by
    rw [abs_le]
    have hu := u.isLt
    dsimp [integerOffset]
    constructor <;> omega
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

theorem left_bound {x y L : ℕ} (c : (largePrimeGraph x y L).ConnectedComponent)
    (z : ℤ) (hz : z ∈ leftOffsets x y L c) : z.natAbs ≤ L + 1 := by
  obtain ⟨u, _, rfl⟩ := mem_image.mp hz
  exact integerOffset_bound u

theorem right_bound {x y L : ℕ} (c : (largePrimeGraph x y L).ConnectedComponent)
    (z : ℤ) (hz : z ∈ rightOffsets x y L c) : z.natAbs ≤ L + 1 := by
  obtain ⟨u, _, rfl⟩ := mem_image.mp hz
  exact integerOffset_bound u

theorem vertices_disjoint {x y L : ℕ} (c d : (largePrimeGraph x y L).ConnectedComponent) (hne : c ≠ d) :
    Disjoint (vertices x y L c) (vertices x y L d) := by
  apply disjoint_left.mpr
  intro v hvc hvd
  exact hne (((MediumPrimeColumns.mem_componentVertices _ c v).mp hvc).symm.trans
    ((MediumPrimeColumns.mem_componentVertices _ d v).mp hvd))

theorem left_disjoint {x y L : ℕ} (c d : (largePrimeGraph x y L).ConnectedComponent) (hne : c ≠ d) :
    Disjoint (leftOffsets x y L c) (leftOffsets x y L d) := by
  rw [leftOffsets, leftOffsets, integerOffsets, integerOffsets, disjoint_image (integerOffset_injective L)]
  apply disjoint_left.mpr
  intro u huc hud
  exact disjoint_left.mp (vertices_disjoint c d hne) (mem_toLeft.mp huc) (mem_toLeft.mp hud)

theorem right_disjoint {x y L : ℕ} (c d : (largePrimeGraph x y L).ConnectedComponent) (hne : c ≠ d) :
    Disjoint (rightOffsets x y L c) (rightOffsets x y L d) := by
  rw [rightOffsets, rightOffsets, integerOffsets, integerOffsets, disjoint_image (integerOffset_injective L)]
  apply disjoint_left.mpr
  intro u huc hud
  exact disjoint_left.mp (vertices_disjoint c d hne) (mem_toRight.mp huc) (mem_toRight.mp hud)

theorem start_product {x L : ℕ} (hx : 1 ≤ x) (P : Finset (Fin (L + 1))) :
    ((∏ u ∈ P, startCompleteVertexLabel x L u : ℕ) : ℤ) = integerProduct (integerOffsets P) (x : ℤ) := by
  rw [Nat.cast_prod, integerProduct, integerOffsets, prod_image (integerOffset_injective L).injOn]
  apply prod_congr rfl
  intro u _
  rw [startCompleteVertexLabel_eq_offset (by omega : 0 < x)]
  dsimp [integerOffset]
  omega

theorem product_eq {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent) :
    (product x y L c : ℤ) = integerProduct (leftOffsets x y L c) (x : ℤ) *
      integerProduct (rightOffsets x y L c) (y : ℤ) := by
  rw [product, prod_sum_eq_prod_toLeft_mul_prod_toRight, Nat.cast_mul]
  simp only [twoStartCompleteVertexLabel]
  rw [start_product hx, start_product hy]
  rfl

theorem square_roots {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent) (j : ℤ) (hj : rightOffsets x y L c = {j}) :
    ∃ w : ℤ, w ^ 2 = (((oddPrimeSupport (product x y L c)).prod id : ℕ) : ℤ) *
      integerProduct (leftOffsets x y L c) (x : ℤ) * ((y : ℤ) + j) := by
  have hs := square_prescription hx hy c
  have hsingle : integerProduct {j} (y : ℤ) = (y : ℤ) + j := by simp only [integerProduct, prod_singleton]
  rw [product_eq (by omega : 1 ≤ x) (by omega : 1 ≤ y), hj, hsingle] at hs
  obtain ⟨w, hw⟩ := hs
  refine ⟨w, ?_⟩
  simpa only [pow_two, mul_assoc] using hw.symm

end PaperP1.TwoBlockComponentPatterns
