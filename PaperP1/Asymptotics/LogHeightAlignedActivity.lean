module

public import PaperP1.Asymptotics.ZeroUnitAlignedActivity
public import PaperP1.Asymptotics.LogHeightUnitChannelActivity

/-! # Complete enlarged aligned channel activity, including zero exact units -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogHeightAlignedActivity

open PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AlignedChannelFamilies

theorem uniform_bound (b₀ : ℕ) (hb₀ : 0 < b₀) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (families N L b₀) ≤ (N : ℝ) ^ (-1 + 1 / (b₀ : ℝ) + ε) := by
  obtain ⟨NU, _hNU, hu⟩ := LogHeightUnitChannelActivity.uniform_bounds b₀ hb₀ C (ε / 2) (by positivity)
  obtain ⟨NZ, _hNZ, hz⟩ := ZeroUnitAlignedActivity.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + 1 / (b₀ : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NU (max NZ NF)), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzero : CompatibleActivitySplit.absolute L (zeroFamilies N L) ≤ (N : ℝ) ^ (-1 + 1 / (b₀ : ℝ) + ε / 2) := by
    apply (hz N (by omega) L hband).trans
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hb : (0 : ℝ) ≤ 1 / (b₀ : ℝ) := by positivity
    linarith only [hb]
  calc
    _ ≤ CompatibleActivitySplit.absolute L (LogHeightUnitChannelFamily.families N L b₀) +
        CompatibleActivitySplit.absolute L (zeroFamilies N L) := activity_bound N L b₀
    _ ≤ 2 * (N : ℝ) ^ (-1 + 1 / (b₀ : ℝ) + ε / 2) := by
      have hunit := (hu N (by omega) L hband).2
      linarith only [hunit, hzero]
    _ ≤ (N : ℝ) ^ ((-1 + 1 / (b₀ : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem all_heights_from_three (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (families N L 3) ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  simpa only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 3 = -2 / 3 by ring] using uniform_bound 3 (by decide) C ε hε

theorem source_tail_from_five (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (families N L 5) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  simpa only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 5 = -4 / 5 by ring] using uniform_bound 5 (by decide) C ε hε

end PaperP1.LogHeightAlignedActivity
