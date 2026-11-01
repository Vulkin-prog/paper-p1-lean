module

public import PaperP1.Combinatorics.ThreeBlockComponents
public import PaperP1.Arithmetic.TwoPointSquareClasses
public import PaperP1.Affine.TwoWindowLabels

/-! # The actual three-window valuation rows, before and after a cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeBlockCoordinates

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ColoredPrimeConstraints PaperP1.CoverGraphResolution

local instance threeBlockCoordinateTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

abbrev Vertex (L : ℕ) := Fin 3 × Fin (L + 1)

def label (X : Fin 3 → ℕ) (L : ℕ) (v : Vertex L) : ℕ := startCompleteVertexLabel (X v.1) L v.2

def data (X : Fin 3 → ℕ) (L : ℕ) (v : Vertex L) (p : ℕ) : F₂ := parityVec (label X L v) p

def rows (X : Fin 3 → ℕ) (L H : ℕ) (p : LargePrime H) : Finset (Vertex L) :=
  univ.filter (fun v ↦ data X L v p.val = 1)

theorem mem_rows {X : Fin 3 → ℕ} {L H : ℕ} {p : LargePrime H} {v : Vertex L} :
    v ∈ rows X L H p ↔ data X L v p.val = 1 := by simp only [rows, mem_filter, mem_univ, true_and]

theorem row_color_injective {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (p : LargePrime H) :
    Set.InjOn Prod.fst (↑(rows X L H p) : Set (Vertex L)) := by
  intro v hv w hw hcolor
  apply Prod.ext hcolor
  have hv1 := mem_rows.mp hv
  have hw1 := mem_rows.mp hw
  have hv0 : parityVec (startCompleteVertexLabel (X v.1) L v.2) p.val ≠ 0 := by
    change data X L v p.val ≠ 0
    rw [hv1]
    exact one_ne_zero
  have hw0 : parityVec (startCompleteVertexLabel (X v.1) L w.2) p.val ≠ 0 := by
    rw [hcolor]
    change data X L w p.val ≠ 0
    rw [hw1]
    exact one_ne_zero
  exact PaperP1.Affine.parityVec_ne_zero_unique_in_start (hX v.1) (lt_of_le_of_lt hH p.property.2) hv0 hw0

theorem rows_card_le_three {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (p : LargePrime H) :
    (rows X L H p).card ≤ 3 := by
  have h := card_le_card_of_injOn Prod.fst (fun _ _ ↦ mem_univ _) (row_color_injective hX hH p)
  simpa only [card_univ, Fintype.card_fin] using h

theorem row_equation (X : Fin 3 → ℕ) (L H : ℕ) (p : LargePrime H) (f : Vertex L → F₂) :
    parityMap (data X L) f p.val = ∑ v ∈ rows X L H p, f v := by
  change (∑ v, f v * data X L v p.val) = _
  rw [rows, sum_filter]
  apply sum_congr rfl
  intro v _
  by_cases h : data X L v p.val = 1
  · simp only [h, mul_one, ite_true]
  · have hz : data X L v p.val = 0 := (show ∀ z : F₂, z ≠ 1 → z = 0 by decide) _ h
    simp [hz]

theorem nonprime_data (X : Fin 3 → ℕ) (L : ℕ) (p : ℕ) (hp : ¬p.Prime) (v : Vertex L) : data X L v p = 0 := by
  simp only [data, parityVec_apply, Nat.factorization_eq_zero_of_not_prime _ hp, Nat.cast_zero]

def relativeSpace (X : Fin 3 → ℕ) (L : ℕ) : Submodule F₂ (Vertex L → F₂) :=
  LinearMap.ker (parityMap (data X L)) ⊓ LinearMap.ker (blockMap Prod.fst)

theorem relativeSpace_le_rows (X : Fin 3 → ℕ) (L H : ℕ) : relativeSpace X L ≤ rowSolutions (rows X L H) := by
  intro f hf p
  have h := congrFun hf.1 p.val
  change parityMap (data X L) f p.val = 0 at h
  rw [row_equation X L H p f] at h
  exact h

theorem blockMap_eq_sum (L : ℕ) (f : Vertex L → F₂) (i : Fin 3) :
    blockMap Prod.fst f i = ∑ j : Fin (L + 1), f (i, j) := by
  change (∑ v ∈ univ.filter (fun v : Vertex L ↦ v.1 = i), f v) = _
  rw [sum_filter, Fintype.sum_prod_type]
  change (∑ x : Fin 3, ∑ j : Fin (L + 1), if x = i then f (x, j) else 0) = _
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, ite_true]

def blockClass (X : Fin 3 → ℕ) (L : ℕ) (f : Vertex L → F₂) (i : Fin 3) : ℕ →₀ F₂ :=
  vertexParityMap (X i) L (fun j ↦ f (i, j))

theorem blockClass_mem {X : Fin 3 → ℕ} {L : ℕ} {f : Vertex L → F₂}
    (hf : blockMap Prod.fst f = 0) (i : Fin 3) : blockClass X L f i ∈ squareClassSpace (X i) L := by
  have hsum := congrFun hf i
  rw [blockMap_eq_sum] at hsum
  change (∑ j, f (i, j)) = 0 at hsum
  let w : LinearMap.ker (startVertexSum L) := ⟨fun j ↦ f (i, j), hsum⟩
  exact ⟨w, rfl⟩

theorem sum_blockClass_eq_zero {X : Fin 3 → ℕ} {L : ℕ} {f : Vertex L → F₂}
    (hf : parityMap (data X L) f = 0) : (∑ i : Fin 3, blockClass X L f i) = 0 := by
  apply Finsupp.ext
  intro p
  change (∑ i : Fin 3, blockClass X L f i) p = 0
  have h := congrFun hf p
  change (∑ v : Vertex L, f v * data X L v p) = 0 at h
  rw [Fintype.sum_prod_type] at h
  simpa only [blockClass, vertexParityMap_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    data, label] using h

theorem blockClass_zero_of_vanishing {X : Fin 3 → ℕ} {L : ℕ} {f : Vertex L → F₂} {i : Fin 3}
    (hf : ∀ j, f (i, j) = 0) : blockClass X L f i = 0 := by
  have hfun : (fun j ↦ f (i, j)) = 0 := funext hf
  change vertexParityMap (X i) L (fun j ↦ f (i, j)) = 0
  rw [hfun, map_zero]

theorem block_zero_of_class_zero {X : Fin 3 → ℕ} {L : ℕ} {f : Vertex L → F₂}
    (hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L))
    (hblocks : blockMap Prod.fst f = 0) (i : Fin 3) (hi : blockClass X L f i = 0) :
    ∀ j, f (i, j) = 0 := by
  have hsum := congrFun hblocks i
  rw [blockMap_eq_sum] at hsum
  change (∑ j, f (i, j)) = 0 at hsum
  let w : LinearMap.ker (startVertexSum L) := ⟨fun j ↦ f (i, j), hsum⟩
  have hw : evenSquareClassMap (X i) L w = evenSquareClassMap (X i) L 0 := by
    rw [map_zero]
    change blockClass X L f i = 0
    exact hi
  have hz := congrArg Subtype.val (hinj i hw)
  exact congrFun hz

end PaperP1.ThreeBlockCoordinates
