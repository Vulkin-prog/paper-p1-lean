module

public import PaperP1.Arithmetic.TruncatedAnchorPairs
public import PaperP1.Asymptotics.SelectedKernelCounts

/-! # Large-anchor counts with no small-prime equations on translated host intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedAnchorPairCount

open PaperP1.SelectedKernelCounts

theorem finite_factor_bound {N H U : ℕ} (T τ : ℝ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (hU : 2 ≤ U) (hUN : U ≤ N) (hT : 0 < T) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ((TruncatedAnchorPairs.bothPairs N H U T).card : ℝ) ≤
      largeFactor τ H * (N : ℝ) ^ (3 / 2 : ℝ) * T ^ (-1 / 2 + τ) := by
  have hfinite := TruncatedAnchorPairs.finite_exp_bound T τ hH hHN hU hUN hT hτ hτhalf
  have heq : 8 * H * N * Real.sqrt (3 * N) * T ^ (-1 / 2 + τ) *
      Real.exp (2 * Real.sqrt H + PowerSeriesTail.constant (1 + τ) * (H : ℝ) ^ (1 - τ)) =
      (8 * Real.sqrt 3 * H * Real.exp (2 * Real.sqrt H) *
        Real.exp (PowerSeriesTail.constant (1 + τ) * (H : ℝ) ^ (1 - τ))) *
        (N : ℝ) ^ (3 / 2 : ℝ) * T ^ (-1 / 2 + τ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.exp_add, ← ambient_sqrt N (by omega)]
    ring
  rw [heq] at hfinite
  refine hfinite.trans ?_
  unfold largeFactor
  gcongr
  exact le_add_of_nonneg_right (by norm_num)

theorem uniform_count (D τ ε : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H U : ℕ, 1 ≤ H → H ≤ N → 2 ≤ U → U ≤ N →
      (H : ℝ) ≤ D * Real.log N → ∀ T : ℝ, 0 < T →
      ((TruncatedAnchorPairs.bothPairs N H U T).card : ℝ) ≤
        (N : ℝ) ^ (3 / 2 + ε) * T ^ (-1 / 2 + τ) := by
  obtain ⟨N₀, hN₀⟩ := UniformReal.uniformSubpolynomialOn_le_rpow
    (large_factor_subpolynomial D τ hD hτ hτhalf) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN H U hH hHN hU hUN hlog T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : largeFactor τ H ≤ (N : ℝ) ^ ε := (le_abs_self _).trans (hN₀ N (by omega) H hlog)
  refine (finite_factor_bound T τ hH hHN hU hUN hT hτ hτhalf).trans ?_
  calc
    _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ (3 / 2 : ℝ)) * T ^ (-1 / 2 + τ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem critical_count (C τ ε : ℝ) (D : ℕ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H U : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ H → H ≤ D * (L + 1) → 2 ≤ U → U ≤ N →
      ∀ T : ℝ, 0 < T →
      ((TruncatedAnchorPairs.bothPairs N H U T).card : ℝ) ≤
        (N : ℝ) ^ (3 / 2 + ε) * T ^ (-1 / 2 + τ) := by
  obtain ⟨Nc, hc⟩ := uniform_count ((D : ℝ) * CriticalBandScale.upperScale) τ ε
    (mul_nonneg (Nat.cast_nonneg _) CriticalBandScale.upperScale_pos.le) hτ hτhalf hε
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C (D : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max Nc (max Ns Nw), ?_⟩
  intro N hN L H U hcrit hH hHB hU hUN T hT
  have hHN : H ≤ N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    have hh' : D * (L + 1) < N := by exact_mod_cast hh
    omega
  have hlog : (H : ℝ) ≤ ((D : ℝ) * CriticalBandScale.upperScale) * Real.log N := by
    have hHR : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hHB
    have hh := mul_le_mul_of_nonneg_left (hs N (by omega) L hcrit).2 (Nat.cast_nonneg D)
    nlinarith only [hHR, hh]
  exact hc N (by omega) H U hH hHN hU hUN hlog T hT

end PaperP1.TruncatedAnchorPairCount
