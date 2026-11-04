module

public import PaperP1.Asymptotics.AsymmetricDefectDensity
public import PaperP1.Arithmetic.ExpandedAsymmetricSupportEnvelope

/-! # Uniform negligible new defects on expanded comparable ranges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricDefectDensity

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricTargetComponents
  PaperP1.AsymmetricDefectDensity PaperP1.LocalDefectBound PaperP1.CriticalBandScale

theorem uniform_constant (Q Dcut : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ Dcut * (L + 1) →
      ∀ y ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ((defective y L H).card : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, Nlocal, hlocal⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2 : ℝ) ((Q + 1 : ℕ) : ℝ) lowerScale upperScale ((10 * (Dcut + 1) : ℕ) : ℝ) 1
    (by norm_num) (by positivity) lowerScale_pos upperScale_pos.le (Nat.cast_nonneg _) (by norm_num)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  refine ⟨max 2 (max Ns Nlocal), ?_⟩
  intro N hN L H hcrit hH y hy
  obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
  have hypos : 0 < y := by omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((y - 1 : ℕ) : ℝ) := by
    have hh : (N : ℝ) ≤ 2 * ((y - 1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2 * (y - 1) by omega)
    linarith only [hh]
  have hbaseUpper : ((y - 1 : ℕ) : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) * N := by
    have hyhi' : y < N + Q * N := hyhi
    have hh : y - 1 ≤ (Q + 1) * N := (Nat.sub_le y 1).trans (by nlinarith only [hyhi'])
    exact_mod_cast hh
  have hcode : ((10 * (H + 1) : ℕ) : ℝ) ≤ ((10 * (Dcut + 1) : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast AsymmetricComponentHostCount.cutoff_budget hH
  have hlength : (L : ℝ) ≤ 1 * ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
  rw [card_eq_interval hypos]
  exact hlocal N (by omega) ((L + 1 : ℕ) : ℝ) (10 * (H + 1)) (y - 1) L
    (hs N (by omega) L hcrit).1 (hs N (by omega) L hcrit).2 hcode hlength hbase hbaseUpper

theorem uniform_density (Q : ℕ) (C ε : ℝ) (Dcut : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ Dcut * (L + 1) →
      ∀ y ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ((defective y L H).card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, _hK, hK⟩ := uniform_constant Q Dcut
  obtain ⟨Nc, hc⟩ := hK C
  obtain ⟨B₀, hb⟩ := ElementaryLogGrowth.log_ge_eventually (K / ε)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  refine ⟨max Nc Ng, ?_⟩
  intro N hN L H hcrit hH y hy
  have hgeom := hg N (by omega) L hcrit
  have hlog := (div_le_iff₀ hε).mp (hb (L + 1) hgeom.2.1).1
  have hlogpos : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by have hh := hgeom.2.2.1; omega))
  have hcoef : K / Real.log ((L + 1 : ℕ) : ℝ) ≤ ε := (div_le_iff₀ hlogpos).mpr (by nlinarith only [hlog])
  calc
    _ ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := hc N (by omega) L H hcrit hH y hy
    _ = (K / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)

end PaperP1.ExpandedAsymmetricDefectDensity
