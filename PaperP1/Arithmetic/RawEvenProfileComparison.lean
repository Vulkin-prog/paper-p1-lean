module

public import PaperP1.Arithmetic.SourcePairKernelComparison

/-! # Full raw-value profile versus the actual even-relation profile

The two block parity equations cost at most two dimensions. Their
positive weighted comparison charges the extra constant only to actual
raw-relation hosts, rather than every pair in the ambient square.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawEvenProfileComparison

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedPairRankLoss
  PaperP1.RawPairRelationRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def rawParityConstraint (x y L : ℕ) : LinearMap.ker (pairVertexParityMap x y L) →ₗ[F₂] (F₂ × F₂) :=
  ((pairLeftSum L).prod (pairRightSum L)).comp (LinearMap.ker (pairVertexParityMap x y L)).subtype

def completeEquivParityKer (x y L : ℕ) : completeRelationCode x y L ≃ₗ[F₂]
    LinearMap.ker (rawParityConstraint x y L) where
  toFun w := by
    refine ⟨⟨w.val, w.property.1⟩, ?_⟩
    apply Prod.ext
    · exact w.property.2.1
    · exact w.property.2.2
  invFun w := by
    refine ⟨w.val.val, w.val.property, ?_, ?_⟩
    · exact congrArg Prod.fst (LinearMap.mem_ker.mp w.property)
    · exact congrArg Prod.snd (LinearMap.mem_ker.mp w.property)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem full_rank_le_loss_add_two (x y L : ℕ) : fullRank x y L ≤ pairLoss x y L + 2 := by
  have hdim := (rawParityConstraint x y L).finrank_range_add_finrank_ker
  have hrange := Submodule.finrank_le (LinearMap.range (rawParityConstraint x y L))
  have htarget : Module.finrank F₂ (F₂ × F₂) = 2 := by
    simp only [Module.finrank_prod, Module.finrank_self]
  rw [htarget] at hrange
  have hker := (completeEquivParityKer x y L).finrank_eq
  rw [PaperP1.SourcePairKernelComparison.complete_rank_eq_loss] at hker
  unfold fullRank
  omega

theorem weight_le (x y L : ℕ) :
    (2 ^ fullRank x y L : ℝ) - 1 ≤
      4 * ((2 ^ pairLoss x y L : ℝ) - 1) + if fullRank x y L ≠ 0 then 3 else 0 := by
  by_cases hh : fullRank x y L = 0
  · rw [hh, pow_zero, sub_self, ite_eq_right (by simp)]
    have hp : (1 : ℝ) ≤ 2 ^ pairLoss x y L := one_le_pow₀ (by norm_num)
    linarith only [hp]
  · rw [ite_eq_left hh]
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (full_rank_le_loss_add_two x y L)
    rw [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num] at hp
    linarith only [hp]

def rawHosts (F : Finset (ℕ × ℕ)) (L : ℕ) : Finset (ℕ × ℕ) :=
  F.filter fun xy ↦ fullRank xy.1 xy.2 L ≠ 0

theorem finite_profile (F : Finset (ℕ × ℕ)) (L : ℕ) :
    (∑ xy ∈ F, ((2 ^ fullRank xy.1 xy.2 L : ℝ) - 1)) ≤
      4 * (∑ xy ∈ F, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) + 3 * (rawHosts F L).card := by
  classical
  have hh := sum_le_sum (fun xy (_hxy : xy ∈ F) ↦ weight_le xy.1 xy.2 L)
  rw [sum_add_distrib, ← mul_sum] at hh
  have hhosts : (∑ xy ∈ F, if fullRank xy.1 xy.2 L ≠ 0 then (3 : ℝ) else 0) =
      3 * (rawHosts F L).card := by
    rw [← sum_filter]
    simp only [rawHosts, sum_const, nsmul_eq_mul, mul_comm]
  rwa [hhosts] at hh

end PaperP1.RawEvenProfileComparison
