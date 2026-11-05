module

public import PaperP1.Asymptotics.PositionalOriginalCovariance
public import PaperP1.Model.PositionalDeletedSupport
public import PaperP1.Probability.PositionalCountCumulant

/-! # The actual deleted counts have small second factorial cumulants -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletedCountCumulant

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.PositionalDeletedFields PaperP1.PositionalCountProjection

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let G := dyadicBlock N
        let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
        |PositionalCountCumulant.scalar (projection (onceLaw E G L))| +
          |PositionalCountCumulant.scalar (projection (isolatedLaw E G L))| ≤
            (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := PositionalOriginalCovariance.uniform_bound C ε hε
  obtain ⟨NM, _hNM, hm⟩ := PositionalDeletionTransfer.uniform_original_moments 2 C 1 (by norm_num)
  refine ⟨10 + NC + NM, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  have hmoment := hm N (by omega) L hband G Subset.rfl E
  have hOnce := PositionalCountCumulant.abs_scalar_le G (onceLaw E G L)
    (onceLaw_isProbability E G L).1 (PositionalDeletedSupport.once_supported E G L) hmoment.1.1
  have hIsolated := PositionalCountCumulant.abs_scalar_le G (isolatedLaw E G L)
    (isolatedLaw_isProbability E G L).1 (PositionalDeletedSupport.isolated_supported E G L) hmoment.2.1
  exact (add_le_add hOnce hIsolated).trans (hc N (by omega) L hband)

end PaperP1.PositionalDeletedCountCumulant
