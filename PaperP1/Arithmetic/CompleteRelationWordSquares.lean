module

public import PaperP1.Arithmetic.CompleteRelationWordEmbedding
public import PaperP1.Arithmetic.BiquadraticWordNorm

/-! # Actual complete relations give actual square-valued offset word polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompleteRelationWordSquares

open Finset Polynomial PaperP1.Arithmetic PaperP1.Affine PaperP1.ShortBasisActualSpace
  PaperP1.CompleteRelationWordEmbedding PaperP1.CurveWordMap PaperP1.FormalWordPolynomials
  PaperP1.LargePrimeOccurrences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : CommRing ℤ[X][X] := inferInstance

def blockProduct (x L : ℕ) (w : Fin (L + 1) → F₂) : ℕ :=
  ∏ i ∈ selected w, startCompleteVertexLabel x L i

def physicalProduct (x y L : ℕ) (w : completeRelationCode x y L) : ℕ :=
  blockProduct x L (firstPhysical x y L w) * blockProduct y L (secondPhysical x y L w)

theorem label_cast_offset (x L : ℕ) (hx : 1 ≤ x) (i : Fin (L + 1)) :
    (startCompleteVertexLabel x L i : ℤ) = (x : ℤ) + offset L i := by
  rw [startCompleteVertexLabel_eq_offset (by omega)]
  simp only [Nat.cast_add, Nat.cast_sub hx, Nat.cast_one, offset]
  ring

theorem offset_product (x L : ℕ) (hx : 1 ≤ x) (w : Fin (L + 1) → F₂) :
    (∏ u ∈ (offsetMap L w).support, ((x : ℤ) + u)) = (blockProduct x L w : ℤ) := by
  rw [offsetMap_support, prod_map]
  unfold blockProduct
  push_cast
  apply prod_congr rfl
  intro i _hi
  exact (label_cast_offset x L hx i).symm

theorem word_evaluation_product (x y L : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (w : completeRelationCode x y L) :
    (wordOver ℤ (wordMap x y L w).1.support (wordMap x y L w).2.support).evalEval (x : ℤ) (y : ℤ) =
      (physicalProduct x y L w : ℤ) := by
  rw [BiquadraticWordNorm.word_evaluation]
  change (∏ u ∈ (offsetMap L (firstPhysical x y L w)).support, ((x : ℤ) + u)) *
    (∏ v ∈ (offsetMap L (secondPhysical x y L w)).support, ((y : ℤ) + v)) = _
  rw [offset_product x L hx, offset_product y L hy]
  simp only [physicalProduct, Nat.cast_mul]

theorem selected_pair_parity (x y L : ℕ) (w : completeRelationCode x y L) :
    (∑ i ∈ selected (firstPhysical x y L w), parityVec (startCompleteVertexLabel x L i)) +
      (∑ i ∈ selected (secondPhysical x y L w), parityVec (startCompleteVertexLabel y L i)) = 0 := by
  have hp := ((mem_completeRelationCode w.val).mp w.property).1
  have hsplit : pairVertexParityMap x y L w.val =
      vertexParityMap x L (firstPhysical x y L w) + vertexParityMap y L (secondPhysical x y L w) := by
    change (∑ v : Occurrence L, w.val v • parityVec (twoStartCompleteVertexLabel x y L v)) =
      (∑ i, w.val (Sum.inl i) • parityVec (startCompleteVertexLabel x L i)) +
        ∑ i, w.val (Sum.inr i) • parityVec (startCompleteVertexLabel y L i)
    simp only [Fintype.sum_sum_type, twoStartCompleteVertexLabel]
  rw [hsplit, vertexParityMap_eq_selected_sum, vertexParityMap_eq_selected_sum] at hp
  exact hp

theorem physicalProduct_square (x y L : ℕ) (w : completeRelationCode x y L) :
    IsSquare (physicalProduct x y L w) := by
  classical
  by_cases hz : physicalProduct x y L w = 0
  · rw [hz]
    exact IsSquare.zero
  have hl : blockProduct x L (firstPhysical x y L w) ≠ 0 := (mul_ne_zero_iff.mp hz).1
  have hr : blockProduct y L (secondPhysical x y L w) ≠ 0 := (mul_ne_zero_iff.mp hz).2
  have hl' : ∀ i ∈ selected (firstPhysical x y L w), startCompleteVertexLabel x L i ≠ 0 :=
    prod_ne_zero_iff.mp hl
  have hr' : ∀ i ∈ selected (secondPhysical x y L w), startCompleteVertexLabel y L i ≠ 0 :=
    prod_ne_zero_iff.mp hr
  apply (parityVec_eq_zero_iff_isSquare hz).mp
  rw [physicalProduct, parityVec_mul hl hr]
  simp only [blockProduct]
  rw [parityVec_prod _ _ hl', parityVec_prod _ _ hr']
  exact selected_pair_parity x y L w

theorem word_evaluation_square (x y L : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (w : completeRelationCode x y L) :
    IsSquare ((wordOver ℤ (wordMap x y L w).1.support (wordMap x y L w).2.support).evalEval
      (x : ℤ) (y : ℤ)) := by
  rw [word_evaluation_product x y L hx hy]
  obtain ⟨r, hr⟩ := physicalProduct_square x y L w
  exact ⟨(r : ℤ), by exact_mod_cast hr⟩

theorem wordBasis_square (x y L : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (cert : Certificate x y L)
    (i : cert.index) :
    IsSquare ((wordOver ℤ (wordBasis x y L cert i).val.1.support
      (wordBasis x y L cert i).val.2.support).evalEval (x : ℤ) (y : ℤ)) := by
  change IsSquare ((wordOver ℤ (((cert.basis.map (wordEquiv x y L cert)) i).val).1.support
    (((cert.basis.map (wordEquiv x y L cert)) i).val).2.support).evalEval (x : ℤ) (y : ℤ))
  rw [Module.Basis.map_apply]
  exact word_evaluation_square x y L hx hy (cert.basis i).val

theorem wordSpace_square (x y L : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (cert : Certificate x y L)
    (w : wordSpace x y L cert) :
    IsSquare ((wordOver ℤ w.val.1.support w.val.2.support).evalEval (x : ℤ) (y : ℤ)) := by
  obtain ⟨r, _hr, he⟩ := Submodule.mem_map.mp w.property
  rw [← he]
  exact word_evaluation_square x y L hx hy r

end PaperP1.CompleteRelationWordSquares
