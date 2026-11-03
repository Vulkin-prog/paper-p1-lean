module

public import PaperP1.Arithmetic.PlaneSupportCover
public import PaperP1.Asymptotics.RankinCertificateCritical

/-! # The two-coordinate Rankin exponent on an arbitrary polynomial family of real planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneRankinCritical

open Finset PaperP1.OffsetFactorSupports PaperP1.CriticalBandScale PaperP1.PlaneSupportCover

theorem uniform_bound (C c : ℝ) (hc : 0 < c) (D k J : ℕ) (hk : 1 ≤ k)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (base : Fin 3 → ℕ) (planes : Finset Plane), planes.card ≤ (L + 1) ^ J →
      ((certificates base N D R (((L + 1 : ℕ) : ℝ) ^ c)
        ((N : ℝ) ^ (1 + 1 / (k : ℝ))) planes).card : ℝ) ≤
        (N : ℝ) ^ ((1 + 1 / (k : ℝ)) * (1 + (1 + ζ) / c) + ε) := by
  let D₀ : ℝ := (2 * D + 1 : ℕ)
  let s := OffsetPatternRankin.exponent c 2 ζ
  let p := (1 + 1 / (k : ℝ)) * s
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  obtain ⟨K, hK, hRankin⟩ := OffsetPatternRankin.integer_patterns c D₀ hc hD₀ 2 (by omega) ζ hζ.le
  obtain ⟨NE, he⟩ := LogPowerExponential.exponential_le_rpow K upperScale (1 - ζ) hK.le
    upperScale_pos.le (by linarith) (by linarith) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale upperScale_pos.le
    (3 * (D + 1 : ℝ) ^ 2) J (ε / 2) (by positivity)
  refine ⟨max 2 (max NE (max NG NP)), by omega, ?_⟩
  intro N hN L R hband hR base planes hplanes
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hgeom := hg N (by omega) L hband
  have hB : (2 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hgeom.2.2.1
  have hX : 1 ≤ (N : ℝ) ^ (1 + 1 / (k : ℝ)) := Real.one_le_rpow hn1 (by positivity)
  have hbase : ((2 * R + 1 : ℕ) : ℝ) ≤ D₀ * ((L + 1 : ℕ) : ℝ) := by
    have hnat : 2 * R + 1 ≤ (2 * D + 1) * (L + 1) := by nlinarith
    dsimp only [D₀]
    exact_mod_cast hnat
  have hcoef : (((2 * R + 1 : ℕ) : ℝ) ^ 2) ≤ (D₀ * ((L + 1 : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hbase 2
  have hmono := RankinCertificateCritical.weightedCount_mono (((L + 1 : ℕ) : ℝ) ^ c)
    ((N : ℝ) ^ (1 + 1 / (k : ℝ))) (((2 * R + 1 : ℕ) : ℝ) ^ 2)
    ((D₀ * ((L + 1 : ℕ) : ℝ)) ^ 2) (by positivity) hcoef
  have hr := hRankin ((L + 1 : ℕ) : ℝ) ((N : ℝ) ^ (1 + 1 / (k : ℝ))) hB hX
  have hcount : integerWeightedCount (((L + 1 : ℕ) : ℝ) ^ c)
      ((N : ℝ) ^ (1 + 1 / (k : ℝ))) (((2 * R + 1 : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) ^ (p + ε / 2) := by
    calc
      _ ≤ ((N : ℝ) ^ (1 + 1 / (k : ℝ))) ^ s * Real.exp (K * ((L + 1 : ℕ) : ℝ) ^ (1 - ζ)) := hmono.trans hr
      _ ≤ ((N : ℝ) ^ (1 + 1 / (k : ℝ))) ^ s * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left (he N (by omega) (L + 1) hgeom.2.2.2.2.2) (by positivity)
      _ = _ := by rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
  have hpoly : 3 * (D + 1 : ℝ) ^ 2 * ((L + 1 : ℕ) : ℝ) ^ J ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity : 0 ≤ 3 * (D + 1 : ℝ) ^ 2 * (L + 1 : ℝ) ^ J)]
      using hp N (by omega) L hgeom.2.2.2.2.2
  have hfactor : 3 * planes.card * (D + 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    have hpc : (planes.card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ J := by exact_mod_cast hplanes
    have hm := mul_le_mul_of_nonneg_left hpc (by positivity : 0 ≤ 3 * (D + 1 : ℝ) ^ 2)
    nlinarith [hm, hpoly]
  have hfinite := certificate_card base N D R (((L + 1 : ℕ) : ℝ) ^ c)
    ((N : ℝ) ^ (1 + 1 / (k : ℝ))) planes (by omega)
  calc
    _ ≤ (3 * planes.card * (D + 1 : ℝ) ^ 2) * (N : ℝ) ^ (p + ε / 2) := hfinite.trans
      (mul_le_mul_of_nonneg_left hcount (by positivity))
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (p + ε / 2) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hn]
      congr 1
      dsimp [p, s, OffsetPatternRankin.exponent]
      norm_num
      ring

end PaperP1.PlaneRankinCritical
