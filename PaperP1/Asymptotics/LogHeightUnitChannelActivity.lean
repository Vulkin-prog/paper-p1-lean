module

public import PaperP1.Model.LogHeightUnitChannelFamily
public import PaperP1.Asymptotics.LogHeightUnitChannelWeights
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The full exact-unit channel tail has mass N^(-1+1/b0+epsilon), without BCN -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogHeightUnitChannelActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.LogHeightUnitChannelFamily
  PaperP1.FixedChannelSourceGeometry

theorem uniform_bounds (b₀ : ℕ) (hb₀ : 0 < b₀) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ families N L b₀, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-1 + 1 / (b₀ : ℝ) + ε) ∧
        CompatibleActivitySplit.absolute L (families N L b₀) ≤ (N : ℝ) ^ (-1 + 1 / (b₀ : ℝ) + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NQ, _hNQ, hq⟩ := LogHeightUnitChannelWeights.uniform_joint b₀ hb₀ C δ hδ
  obtain ⟨NA, _hNA, ha⟩ := LogHeightUnitChannelWeights.uniform_coefficient b₀ hb₀ C δ hδ
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (4 * CriticalBandScale.upperScale ^ 8) 8 δ hδ
  refine ⟨max 2 (max NQ (max NA (max NS NP))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hpoly : 4 * ((L + 1 : ℕ) : ℝ) ^ 8 ≤ (N : ℝ) ^ δ := by
    calc
      _ ≤ 4 * (CriticalBandScale.upperScale * Real.log N) ^ 8 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 8) (by norm_num)
      _ = (4 * CriticalBandScale.upperScale ^ 8) * (Real.log N) ^ 8 := by ring
      _ ≤ _ := by simpa only [Real.rpow_ofNat] using hp N (by omega)
  have hsum (w : Finset ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
      (hpoint : ∀ ab ∈ channels L b₀, ∀ xy ∈ unitSources N ab.1 ab.2 L,
        w {xy.1, xy.2} ≤ (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + δ)) :
      (∑ e ∈ families N L b₀, w e) ≤ (N : ℝ) ^ (-1 + 1 / (b₀ : ℝ) + ε) := by
    calc
      _ ≤ 4 * ((L + 1 : ℕ) : ℝ) ^ 8 * N * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + δ) :=
        weighted_bound (by omega : 0 < N) w hw _ (Real.rpow_nonneg hn.le _) hpoint
      _ ≤ (N : ℝ) ^ δ * N * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + δ) := by
        have h := mul_le_mul_of_nonneg_right hpoly (by positivity : 0 ≤ (N : ℝ) * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + δ))
        simpa only [mul_assoc] using h
      _ = (N : ℝ) ^ δ * (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + δ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hn δ 1, ← Real.rpow_add hn (δ + 1) (-2 + 1 / (b₀ : ℝ) + δ)]
        congr 1
        dsimp [δ]
        ring
  constructor
  · apply hsum (fun e ↦ infiniteJointMoment L e) (infiniteJointMoment_nonneg L)
    intro ab hab xy hxy
    obtain ⟨haa, habt, hcop, hbb, hheight⟩ := channel_data hab
    exact hq N (by omega) L hband ab.1 ab.2 haa habt hcop hbb hheight xy hxy
  · apply hsum (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)
    intro ab hab xy hxy
    obtain ⟨haa, habt, hcop, hbb, hheight⟩ := channel_data hab
    exact ha N (by omega) L hband ab.1 ab.2 haa habt hcop hbb hheight xy hxy

theorem all_heights_from_three (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ families N L 3, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-2 / 3 + ε) ∧
        CompatibleActivitySplit.absolute L (families N L 3) ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  simpa only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 3 = -2 / 3 by ring] using uniform_bounds 3 (by decide) C ε hε

theorem source_tail_from_five (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ families N L 5, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        CompatibleActivitySplit.absolute L (families N L 5) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  simpa only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 5 = -4 / 5 by ring] using uniform_bounds 5 (by decide) C ε hε

end PaperP1.LogHeightUnitChannelActivity
