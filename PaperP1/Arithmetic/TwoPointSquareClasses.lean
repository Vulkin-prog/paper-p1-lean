module

public import PaperP1.Arithmetic.EvenSquareClasses
public import Mathlib.Algebra.Field.ZMod

/-! # Two proportional pairs force a common even square class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoPointSquareClasses

open Finset PaperP1.Arithmetic PaperP1.Affine

local instance twoPointPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def pairWord (L : ℕ) (u v : Fin (L + 1)) : Fin (L + 1) → F₂ :=
  Pi.single u 1 + Pi.single v 1

theorem pairWord_even (L : ℕ) (u v : Fin (L + 1)) :
    startVertexSum L (pairWord L u v) = 0 := by
  rw [pairWord, map_add]
  simp only [startVertexSum_apply, Fintype.sum_pi_single']
  decide

def pairSelection (L : ℕ) (u v : Fin (L + 1)) : LinearMap.ker (startVertexSum L) :=
  ⟨pairWord L u v, pairWord_even L u v⟩

theorem pairSelection_ne_zero (L : ℕ) (u v : Fin (L + 1)) (huv : u ≠ v) :
    pairSelection L u v ≠ 0 := by
  intro h
  have hu := congrArg (fun w : LinearMap.ker (startVertexSum L) ↦ w.val u) h
  have hzero : (1 : F₂) = 0 := by
    simpa only [pairSelection, pairWord, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne huv, add_zero, ZeroMemClass.coe_zero, Pi.zero_apply] using hu
  exact one_ne_zero hzero

theorem pairSelection_image (x L : ℕ) (u v : Fin (L + 1)) :
    evenSquareClassMap x L (pairSelection L u v) =
      parityVec (startCompleteVertexLabel x L u) + parityVec (startCompleteVertexLabel x L v) := by
  change vertexParityMap x L (Pi.single u 1 + Pi.single v 1) = _
  rw [map_add]
  simp only [vertexParityMap, Fintype.linearCombination_apply_single, one_smul]

theorem pair_class_mem (x L : ℕ) (u v : Fin (L + 1)) :
    parityVec (startCompleteVertexLabel x L u) + parityVec (startCompleteVertexLabel x L v) ∈
      squareClassSpace x L := by
  exact ⟨pairSelection L u v, pairSelection_image x L u v⟩

theorem injective_evenMap_of_rank (x L : ℕ)
    (hrank : Module.finrank F₂ (squareClassSpace x L) = L) :
    Function.Injective (evenSquareClassMap x L) := by
  have heven : Module.finrank F₂ (LinearMap.ker (startVertexSum L)) = L := by
    simpa only [Module.finrank_fin_fun] using (startBoundaryEquivEven L).finrank_eq.symm
  have h := (evenSquareClassMap x L).finrank_range_add_finrank_ker
  change Module.finrank F₂ (squareClassSpace x L) +
    Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) = _ at h
  rw [hrank, heven] at h
  have hzero : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)

theorem pair_class_ne_zero (x L : ℕ)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (u v : Fin (L + 1)) (huv : u ≠ v) :
    parityVec (startCompleteVertexLabel x L u) + parityVec (startCompleteVertexLabel x L v) ≠ 0 := by
  rw [← pairSelection_image]
  intro hzero
  have h : pairSelection L u v = 0 := hinj (hzero.trans (map_zero _).symm)
  exact pairSelection_ne_zero L u v huv h

theorem binary_neg_eq_self (w : ℕ →₀ F₂) : -w = w := by
  rw [← neg_one_smul F₂, show (-1 : F₂) = 1 by decide, one_smul]

theorem parity_pair_eq_of_cross_product {n₁ n₂ m₁ m₂ : ℕ}
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (hcross : n₁ * m₂ = n₂ * m₁) :
    parityVec n₁ + parityVec n₂ = parityVec m₁ + parityVec m₂ := by
  have h := congrArg parityVec hcross
  rw [parityVec_mul hn₁ hm₂, parityVec_mul hn₂ hm₁] at h
  have hsub : parityVec n₁ - parityVec n₂ = parityVec m₁ - parityVec m₂ :=
    sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h)
  simpa only [sub_eq_add_neg, binary_neg_eq_self] using hsub

theorem no_proportional_pairs (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (u₁ u₂ v₁ v₂ : Fin (L + 1)) (hu : u₁ ≠ u₂)
    (hcross : startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
      startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁) : False := by
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hnx (u : Fin (L + 1)) : startCompleteVertexLabel x L u ≠ 0 := by
    rw [startCompleteVertexLabel_eq_offset hxpos]
    omega
  have hny (v : Fin (L + 1)) : startCompleteVertexLabel y L v ≠ 0 := by
    rw [startCompleteVertexLabel_eq_offset hypos]
    omega
  have heq := parity_pair_eq_of_cross_product (hnx u₁) (hnx u₂) (hny v₁) (hny v₂) hcross
  have hmemx := pair_class_mem x L u₁ u₂
  have hmemy := pair_class_mem y L v₁ v₂
  rw [← heq] at hmemy
  have hzero := (Submodule.disjoint_def.mp hdirect) _ hmemx hmemy
  exact pair_class_ne_zero x L hinj u₁ u₂ hu hzero

end PaperP1.TwoPointSquareClasses
