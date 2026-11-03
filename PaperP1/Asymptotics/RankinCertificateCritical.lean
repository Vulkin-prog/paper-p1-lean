module

public import PaperP1.Arithmetic.CRTSupportCover
public import PaperP1.Arithmetic.OffsetPatternRankin
public import PaperP1.Asymptotics.LogPowerExponential
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Critical-band counts of actual first-passage factor certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RankinCertificateCritical

open Finset PaperP1.OffsetFactorSupports PaperP1.CriticalBandScale

theorem weightedCount_mono (Y X a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    integerWeightedCount Y X a ≤ integerWeightedCount Y X b := by
  unfold integerWeightedCount FiniteEulerRankin.weightedCount
  exact sum_le_sum (fun A _ ↦ pow_le_pow_left₀ ha hab A.card)

theorem uniform_bound (C c : ℝ) (hc : 0 < c) (D k : ℕ) (hk : 1 ≤ k)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ base : Fin 3 → ℕ,
      ((CRTSupportCover.certificates base N D R (((L + 1 : ℕ) : ℝ) ^ c)
        ((N : ℝ) ^ (1 + 1 / (k : ℝ)))).card : ℝ) ≤
        (N : ℝ) ^ ((1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) + ε) := by
  let D₀ : ℝ := (2 * D + 1 : ℕ)
  let s := OffsetPatternRankin.exponent c 3 ζ
  let p := (1 + 1 / (k : ℝ)) * s
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  obtain ⟨K, hK, hRankin⟩ := OffsetPatternRankin.integer_patterns c D₀ hc hD₀ 3 (by omega) ζ hζ.le
  obtain ⟨NE, he⟩ := LogPowerExponential.exponential_le_rpow K upperScale (1 - ζ) hK.le
    upperScale_pos.le (by linarith) (by linarith) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((D + 1 : ℝ) ^ 3) (p + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NE (max NG NF)), by omega, ?_⟩
  intro N hN L R hband hR base
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
  have hcoef : (((2 * R + 1 : ℕ) : ℝ) ^ 3) ≤ (D₀ * ((L + 1 : ℕ) : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hbase 3
  have hmono := weightedCount_mono (((L + 1 : ℕ) : ℝ) ^ c)
    ((N : ℝ) ^ (1 + 1 / (k : ℝ))) (((2 * R + 1 : ℕ) : ℝ) ^ 3)
    ((D₀ * ((L + 1 : ℕ) : ℝ)) ^ 3) (by positivity) hcoef
  have hr := hRankin ((L + 1 : ℕ) : ℝ) ((N : ℝ) ^ (1 + 1 / (k : ℝ))) hB hX
  have hcount : integerWeightedCount (((L + 1 : ℕ) : ℝ) ^ c)
      ((N : ℝ) ^ (1 + 1 / (k : ℝ))) (((2 * R + 1 : ℕ) : ℝ) ^ 3) ≤ (N : ℝ) ^ (p + ε / 2) := by
    calc
      _ ≤ ((N : ℝ) ^ (1 + 1 / (k : ℝ))) ^ s * Real.exp (K * ((L + 1 : ℕ) : ℝ) ^ (1 - ζ)) := hmono.trans hr
      _ ≤ ((N : ℝ) ^ (1 + 1 / (k : ℝ))) ^ s * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left (he N (by omega) (L + 1) hgeom.2.2.2.2.2) (by positivity)
      _ = _ := by rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
  have hfinite := CRTSupportCover.certificate_card base N D R (((L + 1 : ℕ) : ℝ) ^ c)
    ((N : ℝ) ^ (1 + 1 / (k : ℝ))) (by omega)
  calc
    _ ≤ (D + 1 : ℝ) ^ 3 * (N : ℝ) ^ (p + ε / 2) := hfinite.trans
      (mul_le_mul_of_nonneg_left hcount (by positivity))
    _ ≤ (N : ℝ) ^ ((p + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; dsimp [p, s, OffsetPatternRankin.exponent]; norm_num; ring

end PaperP1.RankinCertificateCritical
