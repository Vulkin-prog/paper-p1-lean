module

public import PaperP1.Arithmetic.RawPairRelationRank
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # The arithmetic source rank includes local kernels and is bounded by the raw value kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairKernelComparison

open PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedPairRankLoss

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem local_rank_identity (x L : ℕ) :
    Module.finrank F₂ (squareClassSpace x L) +
      Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) = L := by
  have h := (evenSquareClassMap x L).finrank_range_add_finrank_ker
  have heven : Module.finrank F₂ (LinearMap.ker (startVertexSum L)) = L := by
    simpa only [Module.finrank_fin_fun] using (startBoundaryEquivEven L).finrank_eq.symm
  rw [heven] at h
  exact h

theorem complete_rank_eq_loss (x y L : ℕ) :
    Module.finrank F₂ (completeRelationCode x y L) = pairLoss x y L := by
  rw [finrank_completeRelationCode]
  have hx := local_rank_identity x L
  have hy := local_rank_identity y L
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  unfold pairLoss
  omega

theorem loss_le_full (x y L : ℕ) : pairLoss x y L ≤ RawPairRelationRank.fullRank x y L := by
  rw [← complete_rank_eq_loss]
  exact RawPairRelationRank.complete_le_full x y L

theorem source_kernel_le_full_sum (F : Finset (ℕ × ℕ)) (L : ℕ) :
    (∑ p ∈ F, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
      ∑ p ∈ F, (2 ^ RawPairRelationRank.fullRank p.1 p.2 L : ℝ) := by
  apply Finset.sum_le_sum
  intro p _hp
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (loss_le_full p.1 p.2 L)
  linarith

end PaperP1.SourcePairKernelComparison
