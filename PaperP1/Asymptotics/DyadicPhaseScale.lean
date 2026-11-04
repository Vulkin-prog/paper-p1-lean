module

public import PaperP1.Asymptotics.TwoThreePositivePhase
public import PaperP1.Asymptotics.CriticalChannelPowers
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Positive dyadic phase growth and negligible errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPhaseScale

open Filter PaperP1.TwoThreePositivePhase

theorem uniform_phase_lower (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      K * (N : ℝ) ^ (1 / 3 : ℝ) ≤ positiveMain L := by
  let K : ℝ := (1 / 6) * (2 : ℝ) ^ (-C / 3 - 1)
  refine ⟨K, by dsimp [K]; positivity, 2, ?_⟩
  intro N hN L hcrit
  have hB1 : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  have hword : (2 : ℝ) ^ (-C / 3 - 1) * (N : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (L / 3) := by
    simpa only [Nat.cast_ofNat] using PaperP1.CriticalChannelPowers.quotient_word_lower
      (by omega : 2 ≤ N) (by omega : 0 < 3) hcrit
  have hbase : K * (N : ℝ) ^ (1 / 3 : ℝ) ≤ (1 / 6 : ℝ) * (2 : ℝ) ^ (L / 3) := by
    have hh := mul_le_mul_of_nonneg_left hword (by norm_num : (0 : ℝ) ≤ 1 / 6)
    simpa only [K, mul_assoc] using hh
  have hcp : (1 / 6 : ℝ) ≤ ((3 : ℝ) + ((L + 1) % 3 : ℕ)) / 6 := by
    have hz := Nat.cast_nonneg (α := ℝ) ((L + 1) % 3)
    linarith only [hz]
  have hprod : (1 / 6 : ℝ) ≤ (((3 : ℝ) + ((L + 1) % 3 : ℕ)) / 6) * ((L + 1 : ℕ) : ℝ) := by
    have hh := mul_le_mul hcp hB1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ ((3 : ℝ) + ((L + 1) % 3 : ℕ)) / 6)
    simpa only [mul_one] using hh
  have hpow : (2 : ℝ) ^ (L / 3) ≤ (2 : ℝ) ^ ((L + 1) / 3) :=
    pow_le_pow_right₀ (by norm_num) (by omega : L / 3 ≤ (L + 1) / 3)
  exact hbase.trans ((mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 6)).trans
    (mul_le_mul_of_nonneg_right hprod (by positivity)))

theorem power_error_negligible (C τ η : ℝ) (hτ : τ < 4 / 3) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ τ ≤ η * ((N : ℝ) / 3 * positiveMain L) := by
  obtain ⟨K, hK, NG, hG⟩ := uniform_phase_lower C
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(4 / 3 - τ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 4 / 3 - τ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NS, hS⟩ := eventually_atTop.mp (hlim.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < η * K / 3)))
  refine ⟨max NG NS, ?_⟩
  intro N hN L hcrit
  have hp := hG N (by omega) L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsmall : (N : ℝ) ^ τ ≤ η * ((N : ℝ) / 3 * (K * (N : ℝ) ^ (1 / 3 : ℝ))) := by
    calc
      _ = (N : ℝ) ^ (-(4 / 3 - τ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_add hn]
        congr 1
        ring
      _ ≤ (η * K / 3) * (N : ℝ) ^ (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right (hS N (by omega)).le (Real.rpow_nonneg hn.le _)
      _ = _ := by
        rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by ring, Real.rpow_add hn, Real.rpow_one]
        ring
  exact hsmall.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) hη.le)

end PaperP1.DyadicPhaseScale
