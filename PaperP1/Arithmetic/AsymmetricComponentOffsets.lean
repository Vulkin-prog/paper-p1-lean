module

public import PaperP1.Arithmetic.AsymmetricEnvelopeGraph
public import PaperP1.Arithmetic.TwoBlockComponentPatterns

/-! # Literal component offsets referred to the original unequal-block centres

Unused envelope vertices are pinned. Thus every free old root lies in
the prescribed old set and every free new root lies in the actual window.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricComponentOffsets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEnvelopeGraph
  PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution
  PaperP1.LargePrimeOccurrences PaperP1.TwoBlockComponentSquares PaperP1.SplitRadicalPointHeight
  PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def offset (x H R : ℕ) (i : Fin (H + 1)) : ℤ :=
  (startCompleteVertexLabel (start x R) H i : ℤ) - x

def left (x y H R : ℕ) (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) : Finset ℤ :=
  (vertices (start x R) (start y R) H c).toLeft.image (offset x H R)

def right (x y H R : ℕ) (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) : Finset ℤ :=
  (vertices (start x R) (start y R) H c).toRight.image (offset y H R)

theorem offset_injective {x H R : ℕ} (hx : R < x) : Function.Injective (offset x H R) := by
  intro i j he
  apply startCompleteVertexLabel_injective (x := start x R) (L := H) (by have hh := start_ge_two hx; omega)
  have hh : (startCompleteVertexLabel (start x R) H i : ℤ) = startCompleteVertexLabel (start x R) H j := by
    dsimp [offset] at he
    omega
  exact_mod_cast hh

theorem left_card {x y H R : ℕ} (hx : R < x)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    (left x y H R c).card = (vertices (start x R) (start y R) H c).toLeft.card :=
  card_image_of_injective _ (offset_injective hx)

theorem right_card {x y H R : ℕ} (hy : R < y)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    (right x y H R c).card = (vertices (start x R) (start y R) H c).toRight.card :=
  card_image_of_injective _ (offset_injective hy)

theorem total_card {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    (left x y H R c).card + (right x y H R c).card = (vertices (start x R) (start y R) H c).card := by
  rw [left_card hx, right_card hy, card_toLeft_add_card_toRight]

theorem left_disjoint {x y H R : ℕ} (hx : R < x)
    (c d : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) (hne : c ≠ d) :
    Disjoint (left x y H R c) (left x y H R d) := by
  rw [left, left, disjoint_image (offset_injective hx)]
  apply disjoint_left.mpr
  intro i hic hid
  exact disjoint_left.mp (TwoBlockComponentPatterns.vertices_disjoint c d hne) (mem_toLeft.mp hic) (mem_toLeft.mp hid)

theorem right_disjoint {x y H R : ℕ} (hy : R < y)
    (c d : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) (hne : c ≠ d) :
    Disjoint (right x y H R c) (right x y H R d) := by
  rw [right, right, disjoint_image (offset_injective hy)]
  apply disjoint_left.mpr
  intro i hic hid
  exact disjoint_left.mp (TwoBlockComponentPatterns.vertices_disjoint c d hne) (mem_toRight.mp hic) (mem_toRight.mp hid)

theorem original_unpinned {x y L H R : ℕ} (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c) :
    ¬ComponentPinned _ (pinnedVertices (start x R) (start y R) H) c := by
  rintro ⟨v, hv, he⟩
  exact hfree ⟨v, mem_union_left _ (mem_union_left _ hv), he⟩

theorem nonempty {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hsize : 2 ≤ Fintype.card c.supp) : (left x y H R c).Nonempty ∧ (right x y H R c).Nonempty := by
  obtain ⟨i, j, hi, hj⟩ := LargePrimeComponentArithmetic.nontrivial_component_meets_both_blocks
    (by have hh := start_ge_two hx; omega) (by have hh := start_ge_two hy; omega) c hsize
  exact ⟨⟨_, mem_image.mpr ⟨i, mem_toLeft.mpr ((MediumPrimeColumns.mem_componentVertices _ c _).mpr hi), rfl⟩⟩,
    ⟨_, mem_image.mpr ⟨j, mem_toRight.mpr ((MediumPrimeColumns.mem_componentVertices _ c _).mpr hj), rfl⟩⟩⟩

theorem left_bound {x y L H R : ℕ} (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ))
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c)
    (z : ℤ) (hz : z ∈ left x y H R c) : z.natAbs ≤ R := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  have hcomp := (MediumPrimeColumns.mem_componentVertices _ c _).mp (mem_toLeft.mp hi)
  have hmem := old_mem_of_unpinned hnew hamb old c hfree i hcomp
  have hh : |offset x H R i| ≤ (R : ℤ) := hold _ hmem
  rw [Int.abs_eq_natAbs] at hh
  exact_mod_cast hh

theorem right_bound {x y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c)
    (z : ℤ) (hz : z ∈ right x y H R c) : z.natAbs ≤ R := by
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
  have hcomp := (MediumPrimeColumns.mem_componentVertices _ c _).mp (mem_toRight.mp hj)
  obtain ⟨i, he⟩ := new_index_of_unpinned hnew hamb old c hfree j hcomp
  have hval : startCompleteVertexLabel (start y R) H j = startCompleteVertexLabel y L i := by
    rw [← he, target_label hy hnew hamb]
  have hh : |offset y H R j| ≤ (R : ℤ) := by
    rw [offset, hval, startCompleteVertexLabel_eq_offset (by omega : 0 < y)]
    have hi := i.isLt
    apply abs_le.mpr
    constructor <;> omega
  rw [Int.abs_eq_natAbs] at hh
  exact_mod_cast hh

theorem start_product {x H R : ℕ} (hx : R < x) (P : Finset (Fin (H + 1))) :
    ((∏ i ∈ P, startCompleteVertexLabel (start x R) H i : ℕ) : ℤ) =
      integerProduct (P.image (offset x H R)) (x : ℤ) := by
  rw [Nat.cast_prod, integerProduct, prod_image (offset_injective hx).injOn]
  apply prod_congr rfl
  intro i _
  dsimp [offset]
  ring

theorem product_eq {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    (product (start x R) (start y R) H c : ℤ) = integerProduct (left x y H R c) (x : ℤ) *
      integerProduct (right x y H R c) (y : ℤ) := by
  rw [product, prod_sum_eq_prod_toLeft_mul_prod_toRight, Nat.cast_mul]
  simp only [twoStartCompleteVertexLabel]
  rw [start_product hx, start_product hy]
  rfl

theorem square_roots {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    ∃ w : ℤ, w ^ 2 = (((oddPrimeSupport (product (start x R) (start y R) H c)).prod id : ℕ) : ℤ) *
      integerProduct (left x y H R c) (x : ℤ) * integerProduct (right x y H R c) (y : ℤ) := by
  have hs := square_prescription (start_ge_two hx) (start_ge_two hy) c
  rw [product_eq hx hy] at hs
  obtain ⟨w, hw⟩ := hs
  exact ⟨w, by simpa only [pow_two, mul_assoc] using hw.symm⟩

theorem coefficient_support {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c) :
    oddPrimeSupport (product (start x R) (start y R) H c) ⊆ DefectCounting.smallPrimesUpTo (10 * (H + 1)) :=
  TwoBlockComponentSquares.support (start_ge_two hx) (start_ge_two hy) c (original_unpinned hnew hamb old c hfree)

end PaperP1.AsymmetricComponentOffsets
