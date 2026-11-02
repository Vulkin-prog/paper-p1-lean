module

public import PaperP1.Model.AlignedCumulantReduction
public import PaperP1.Asymptotics.AlignedPrincipalSigned
public import PaperP1.Asymptotics.SecondCumulantUnderBCN
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The full original pair profile reduces only to the actual nonaligned activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondCumulantNonalignedReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges

theorem uniform_bound (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 2 * beta N H L| ≤
        2 * CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
          (N : ℝ) ^ (-4 / 5 + ε) := by
  let K := 2 * (2 : ℝ) ^ C
  obtain ⟨NS, _hNS, hs⟩ := AlignedPrincipalSigned.uniform_bound C (ε / 2) D (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + K ^ 2) (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NS (max NP NF)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag : (∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2) ≤ K ^ 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    have hd := SecondCumulantUnderBCN.diagonal_bound (L := L) (by omega : 0 < N) (subset_refl (dyadicBlock N))
      (fun x hx ↦ hp N (by omega) L hband x hx)
    calc
      _ ≤ K ^ 2 / N := hd
      _ = K ^ 2 * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1
        (by linarith only [hε])) (sq_nonneg K)
  have hmain := hs N (by omega) L H hband hcut hH
  calc
    _ ≤ 2 * CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
        2 * |CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - beta N H L| +
          ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 := AlignedCumulantReduction.finite_bound N L (beta N H L)
    _ ≤ 2 * CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
        (2 + K ^ 2) * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [hmain, hdiag]
    _ ≤ 2 * CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
        (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := by
      have hh := hf N (by omega)
      linarith only [hh]
    _ = _ := by congr 2; ring

end PaperP1.SecondCumulantNonalignedReduction
