module

public import PaperP1.Arithmetic.RawEvenProfileComparison

/-! # Enlarging the actual raw windows charges only the added coordinates

New relations are charged to actual hosts at the larger width. This
avoids a correction supported on the entire ambient pair square.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawWindowExtension

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RawPairRelationRank
  PaperP1.RawEvenProfileComparison PaperP1.LargePrimeOccurrences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem range_monotone {x y L Q : ℕ} (hx : 0 < x) (hy : 0 < y) (hLQ : L ≤ Q) :
    LinearMap.range (pairVertexParityMap x y L) ≤ LinearMap.range (pairVertexParityMap x y Q) := by
  change LinearMap.range (Fintype.linearCombination F₂ (fun i ↦ parityVec (twoStartCompleteVertexLabel x y L i))) ≤
    LinearMap.range (Fintype.linearCombination F₂ (fun i ↦ parityVec (twoStartCompleteVertexLabel x y Q i)))
  rw [Fintype.range_linearCombination, Fintype.range_linearCombination]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
    refine ⟨Sum.inl (Fin.castLE (by omega : L + 1 ≤ Q + 1) i), ?_⟩
    simp only [twoStartCompleteVertexLabel, startCompleteVertexLabel_eq_offset hx, Fin.val_castLE]
  | inr i =>
    refine ⟨Sum.inr (Fin.castLE (by omega : L + 1 ≤ Q + 1) i), ?_⟩
    simp only [twoStartCompleteVertexLabel, startCompleteVertexLabel_eq_offset hy, Fin.val_castLE]

theorem rank_extension {x y L Q : ℕ} (hx : 0 < x) (hy : 0 < y) (hLQ : L ≤ Q) :
    fullRank x y Q ≤ fullRank x y L + 2 * (Q - L) := by
  have hsmall := (pairVertexParityMap x y L).finrank_range_add_finrank_ker
  have hbig := (pairVertexParityMap x y Q).finrank_range_add_finrank_ker
  have hrange := Submodule.finrank_mono (range_monotone hx hy hLQ)
  have hd (R : ℕ) : Module.finrank F₂ (Occurrence R → F₂) = 2 * (R + 1) := by
    simp only [Occurrence, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hd L] at hsmall
  rw [hd Q] at hbig
  unfold fullRank
  omega

theorem weight_extension {x y L Q : ℕ} (hx : 0 < x) (hy : 0 < y) (hLQ : L ≤ Q) :
    (2 ^ fullRank x y Q : ℝ) - 1 ≤ (2 : ℝ) ^ (2 * (Q - L)) *
      (((2 ^ fullRank x y L : ℝ) - 1) + if fullRank x y Q ≠ 0 then 1 else 0) := by
  by_cases hh : fullRank x y Q = 0
  · rw [hh, pow_zero, sub_self, ite_eq_right (by simp), add_zero]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
  · rw [ite_eq_left hh]
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (rank_extension hx hy hLQ)
    rw [pow_add] at hp
    nlinarith only [hp]

theorem finite_extension {L Q : ℕ} (F : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ F, 0 < xy.1 ∧ 0 < xy.2) (hLQ : L ≤ Q) :
    (∑ xy ∈ F, ((2 ^ fullRank xy.1 xy.2 Q : ℝ) - 1)) ≤ (2 : ℝ) ^ (2 * (Q - L)) *
      ((∑ xy ∈ F, ((2 ^ fullRank xy.1 xy.2 L : ℝ) - 1)) + (rawHosts F Q).card) := by
  classical
  have hh := sum_le_sum (fun xy (hxy : xy ∈ F) ↦ weight_extension (hpos xy hxy).1 (hpos xy hxy).2 hLQ)
  rw [← mul_sum, sum_add_distrib] at hh
  have hhosts : (∑ xy ∈ F, if fullRank xy.1 xy.2 Q ≠ 0 then (1 : ℝ) else 0) =
      (rawHosts F Q).card := by
    rw [← sum_filter]
    simp only [rawHosts, sum_const, nsmul_eq_mul, mul_one]
  rwa [hhosts] at hh

end PaperP1.RawWindowExtension
