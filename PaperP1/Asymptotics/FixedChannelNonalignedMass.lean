module

public import PaperP1.Asymptotics.OriginalCompressedNonalignedMass

/-! # Retaining the denominator gain in the coarse nonaligned source mass

This is the existing four-thirds profile calculation before replacing
`1/b` by `1/3`. Its normalized fixed-channel rate is two thirds.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelNonalignedMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CompressedSourceBlocks PaperP1.DyadicEndpointPairs PaperP1.AsymmetricJointWeight
  PaperP1.OriginalCompressedNonalignedMass

theorem uniform_bound (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → channelMass N a b L ≤ (N : ℝ) ^ (-5 / 3 + 1 / (b : ℝ) + ε) := by
  let M := 2 * (2 : ℝ) ^ C
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨Nc, _hNc, hc⟩ := CompressedAsymmetricProfile.uniform_channel
    a b (2 * b + 1) ha hab.le (by omega) C (ε / 4) (by positivity)
  obtain ⟨Nq, _hNq, hq⟩ := UnitChannelPairWeights.uniform_joint C (ε / 4) a b ha hab hcop (by positivity)
  obtain ⟨Np, _hNp, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption (2 * M) (-5 / 3 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Nc (max Nq (max Np (max Ng Nf)))), by omega, ?_⟩
  intro N hN L hcrit
  have hL : 0 < L := by have hh := (hg N (by omega) L hcrit).2.2.1; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let H := (2 * b + 1) * (L + 1)
  let A := M * (N : ℝ) ^ (-3 + 1 / (b : ℝ) + ε / 4)
  have hA : 0 ≤ A := mul_nonneg hM.le (Real.rpow_nonneg hNpos.le _)
  have hcap : ∀ i j : Fin (L + 1), ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ dyadicBlock N,
      infiniteJointMoment L {xy.1, xy.2} * infiniteMarginal z L ≤ A := by
    intro i j xy hxy z hz
    calc
      _ ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 4) * (M / N) :=
        mul_le_mul (hq N (by omega) L hcrit xy (unit_source i j hxy)) (hp N (by omega) L hcrit z hz)
          (MissingBlockProbabilities.infiniteMarginal_nonneg z L) (Real.rpow_nonneg hNpos.le _)
      _ = _ := by
        dsimp [A]
        rw [show -3 + 1 / (b : ℝ) + ε / 4 = (-2 + 1 / (b : ℝ) + ε / 4) - 1 by ring,
          Real.rpow_sub hNpos, Real.rpow_one]
        ring
  have hfinite : channelMass N a b L ≤ 2 * A * CompressedAsymmetricProfile.channelProfile N a b L H := by
    rw [channelMass, CompressedAsymmetricProfile.channelProfile, mul_sum]
    exact sum_le_sum fun ij _ ↦ finite_bound (H := H) (by omega) ha (by omega) hL ij.1 ij.2 A hA (hcap ij.1 ij.2)
  have hprofile := hc N (by omega) L H hcrit le_rfl le_rfl
  calc
    _ ≤ 2 * A * (N : ℝ) ^ (4 / 3 + ε / 4) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hprofile (by positivity))
    _ = (2 * M) * (N : ℝ) ^ (-5 / 3 + 1 / (b : ℝ) + ε / 2) := by
      dsimp [A]
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hNpos,
        show (-3 + 1 / (b : ℝ) + ε / 4) + (4 / 3 + ε / 4) = -5 / 3 + 1 / (b : ℝ) + ε / 2 by ring]
      dsimp [M]
      ring
    _ ≤ _ := by
      simpa only [show (-5 / 3 + 1 / (b : ℝ) + ε / 2) + ε / 2 = -5 / 3 + 1 / (b : ℝ) + ε by ring] using hf N (by omega)


end PaperP1.FixedChannelNonalignedMass
