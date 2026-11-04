module

public import PaperP1.Asymptotics.OneTwoChannelPhase
public import PaperP1.Asymptotics.CriticalChannelPowers
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Lower phase growth and negligible macroscopic errors

Both moving phases have a common positive square-root lower bound.
Every error with exponent below three halves is relatively negligible.
The exact lower-endpoint factor is controlled separately.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicPhaseScale

open Filter PaperP1.OneTwoChannelPhase

theorem uniform_phase_lower (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      K * (M : ℝ) ^ (1 / 2 : ℝ) ≤ positiveMain L ∧ K * (M : ℝ) ^ (1 / 2 : ℝ) ≤ signedMain L := by
  let K : ℝ := (1 / 4) * (2 : ℝ) ^ (-C / 2 - 1)
  obtain ⟨M₀, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨K, by dsimp [K]; positivity, M₀, ?_⟩
  intro M hM L hcrit
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hB1 : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  have hword : (2 : ℝ) ^ (-C / 2 - 1) * (M : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (L / 2) := by
    simpa only [Nat.cast_ofNat] using PaperP1.CriticalChannelPowers.quotient_word_lower
      (by omega : 2 ≤ M) (by omega : 0 < 2) hcrit
  have hbase : K * (M : ℝ) ^ (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (L / 2) := by
    have hh := mul_le_mul_of_nonneg_left hword (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa only [K, mul_assoc] using hh
  have hcp : (1 / 4 : ℝ) ≤ ((2 : ℝ) + ((L + 1) % 2 : ℕ)) / 4 := by
    have hz := Nat.cast_nonneg (α := ℝ) ((L + 1) % 2)
    linarith only [hz]
  have hcs : (1 / 4 : ℝ) ≤ (((L % 2 : ℕ) : ℝ) + 1) / 4 := by
    have hz := Nat.cast_nonneg (α := ℝ) (L % 2)
    linarith only [hz]
  have hpprod : (1 / 4 : ℝ) ≤ (((2 : ℝ) + ((L + 1) % 2 : ℕ)) / 4) * ((L + 1 : ℕ) : ℝ) := by
    have hh := mul_le_mul hcp hB1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ ((2 : ℝ) + ((L + 1) % 2 : ℕ)) / 4)
    simpa only [mul_one] using hh
  have hsprod : (1 / 4 : ℝ) ≤ ((((L % 2 : ℕ) : ℝ) + 1) / 4) * L := by
    have hh := mul_le_mul hcs hL1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (((L % 2 : ℕ) : ℝ) + 1) / 4)
    simpa only [mul_one] using hh
  have hpow : (2 : ℝ) ^ (L / 2) ≤ (2 : ℝ) ^ ((L + 1) / 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega : L / 2 ≤ (L + 1) / 2)
  constructor
  · exact hbase.trans ((mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans
      (mul_le_mul_of_nonneg_right hpprod (by positivity)))
  · exact hbase.trans (mul_le_mul_of_nonneg_right hsprod (by positivity))

theorem power_error_negligible (C τ η : ℝ) (hτ : τ < 3 / 2) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (M : ℝ) ^ τ ≤ η * M * positiveMain L ∧ (M : ℝ) ^ τ ≤ η * M * signedMain L := by
  obtain ⟨K, hK, MG, hG⟩ := uniform_phase_lower C
  have hlim : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (-(3 / 2 - τ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 3 / 2 - τ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨MS, hS⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (mul_pos hη hK)))
  refine ⟨max MG MS, ?_⟩
  intro M hM L hcrit
  obtain ⟨hp, hs⟩ := hG M (by omega) L hcrit
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsmall : (M : ℝ) ^ τ ≤ η * (M * (K * (M : ℝ) ^ (1 / 2 : ℝ))) := by
    calc
      _ = (M : ℝ) ^ (-(3 / 2 - τ)) * (M : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add hm]
        congr 1
        ring
      _ ≤ (η * K) * (M : ℝ) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hS M (by omega)).le (Real.rpow_nonneg hm.le _)
      _ = _ := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hm, Real.rpow_one]
        ring
  constructor
  · simpa only [mul_assoc] using hsmall.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hm.le) hη.le)
  · simpa only [mul_assoc] using hsmall.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hm.le) hη.le)

theorem lower_endpoint_small (δ η : ℝ) (hδ1 : δ < 1) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2,
      0 ≤ (M : ℝ) - 2 * (M : ℝ) ^ δ ∧ (M : ℝ) - 2 * (M : ℝ) ^ δ ≤ M ∧
      2 * (M : ℝ) ^ δ ≤ η * M := by
  have hlim : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (δ - 1)) atTop (nhds 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - δ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨M₀, h⟩ := eventually_atTop.mp (hlim.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < min (η / 2) (1 / 2))))
  refine ⟨M₀, ?_⟩
  intro M hM
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hp : (M : ℝ) ^ δ = (M : ℝ) ^ (δ - 1) * M := by
    rw [← Real.rpow_add_one hm.ne']
    congr 1
    ring
  have hsmall : (M : ℝ) ^ δ < min (η / 2) (1 / 2) * M := by
    rw [hp]
    exact mul_lt_mul_of_pos_right (h M (by omega)) hm
  have hηM := mul_le_mul_of_nonneg_right (min_le_left (η / 2) (1 / 2)) hm.le
  have hhalfM := mul_le_mul_of_nonneg_right (min_le_right (η / 2) (1 / 2)) hm.le
  have hpos := Real.rpow_nonneg hm.le δ
  exact ⟨by linarith only [hsmall, hhalfM], by linarith only [hpos], by linarith only [hsmall, hηM]⟩

end PaperP1.MacroscopicPhaseScale
