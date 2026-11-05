module

public import PaperP1.Asymptotics.UnsignedTwoChannelMainBound
public import PaperP1.Asymptotics.PositiveSeparatedSourceProfile
public import PaperP1.Model.RawEvenProfileHosts

/-! # The actual critical full-value profile from internal positive pair estimates

The full positive pair profile and raw-host bound are proved internally.
The full-value odd-parity contribution is retained exactly.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalRawValueProfile

open Finset PaperP1.Model PaperP1.RawPairRelationRank PaperP1.RawEvenProfileComparison
  PaperP1.CriticalBandScale

def mass (N L : ℕ) : ℝ :=
  ∑ xy ∈ PairSeparation.separatedHosts (dyadicBlock N) L, ((2 ^ fullRank xy.1 xy.2 L : ℝ) - 1)

theorem uniform_profile (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L ≤ (N : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨NP, _hNP, hP⟩ :=
    PaperP1.PositiveSeparatedSourceProfile.article_3_3_positive C (ε / 4) (by positivity)
  obtain ⟨NM, hM⟩ := PaperP1.UnsignedTwoChannelMainBound.uniform_main_bound C (ε / 4) (by positivity)
  obtain ⟨NH, hH⟩ := PaperP1.RawEvenProfileHosts.uniform_host_bound upperScale upperScale_pos.le (ε / 4) (by positivity)
  obtain ⟨NB, hB⟩ := critical_band_scale C
  obtain ⟨NF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 11 (3 / 2 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨max NP (max NM (max NH (max NB NF))), ?_⟩
  intro N hN L hcrit
  have hpositive := (le_abs_self _).trans (hP N (by omega) L hcrit)
  have hmain := hM N (by omega) L hcrit
  change PaperP1.PositiveSeparatedSourceProfile.mainTerm N L ≤ (N : ℝ) ^ (4 / 3 + ε / 4) at hmain
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmainpower : (N : ℝ) ^ (4 / 3 + ε / 4) ≤ (N : ℝ) ^ (3 / 2 + ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have herrorpower : (N : ℝ) ^ (6 / 5 + ε / 4) ≤ (N : ℝ) ^ (3 / 2 + ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have heven : (∑ xy ∈ PairSeparation.separatedHosts (dyadicBlock N) L,
      ((2 ^ PaperP1.NormalizedPairRankLoss.pairLoss xy.1 xy.2 L : ℝ) - 1)) ≤
      2 * (N : ℝ) ^ (3 / 2 + ε / 4) := by
    linarith only [hpositive, hmain, hmainpower, herrorpower]
  have hsub : PairSeparation.separatedHosts (dyadicBlock N) L ⊆ (dyadicBlock N) ×ˢ (dyadicBlock N) := by
    intro xy hxy
    have hh := (PairSeparation.mem_separatedHosts (dyadicBlock N) L xy).mp hxy
    exact mem_product.mpr ⟨hh.1, hh.2.1⟩
  have hhosts := hH N (by omega) L (hB N (by omega) L hcrit).2 _ hsub
  have hfinite := finite_profile (PairSeparation.separatedHosts (dyadicBlock N) L) L
  have hbound : mass N L ≤ 11 * (N : ℝ) ^ (3 / 2 + ε / 4) := by
    unfold mass
    linarith only [hfinite, heven, hhosts]
  have hf := hF N (by omega)
  simpa only [show (3 : ℝ) / 2 + ε / 4 + 3 * ε / 4 = 3 / 2 + ε by ring] using hbound.trans hf

end PaperP1.CriticalRawValueProfile
