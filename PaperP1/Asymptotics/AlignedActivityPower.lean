module

public import PaperP1.Asymptotics.AlignedPrincipalActivity

/-! # The unconditional sharp coarse power of the full aligned pair population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedActivityPower

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) ≤
        (N : ℝ) ^ (-2 / 3 + ε) := by
  obtain ⟨c, k, _hc, hk, NM, _hNM, hm⟩ := PrincipalChannelEdgesPhase.positive_phase C 8
  obtain ⟨NA, _hNA, ha⟩ := AlignedPrincipalActivity.uniform_absolute C (ε / 2) 8 (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (k * CriticalBandScale.upperScale) 1 (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NM (max NA (max NG (max NP NF)))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hB := (hg N (by omega) L hband).2.2.2.2.2
  have hL : (L : ℝ) ≤ CriticalBandScale.upperScale * Real.log N :=
    (show (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ L).trans hB
  have hpoly : k * L ≤ (N : ℝ) ^ (ε / 2) :=
    (mul_le_mul_of_nonneg_left hL hk.le).trans
      (by simpa only [Real.rpow_one, mul_assoc] using hp N (by omega))
  have hphase := (hm N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl).2
  have hbeta : beta N (8 * (L + 1)) L ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) := by
    calc
      _ ≤ (k * L) * (N : ℝ) ^ (-2 / 3 : ℝ) := hphase
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hgap := (abs_le.mp (ha N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl)).2
  have hsmall : (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  calc
    _ ≤ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) := by linarith only [hgap, hbeta, hsmall]
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.AlignedActivityPower
