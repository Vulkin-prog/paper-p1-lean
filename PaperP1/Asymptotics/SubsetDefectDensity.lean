module

public import PaperP1.Arithmetic.SubsetTargetComponents
public import PaperP1.Asymptotics.AsymmetricDefectDensity

/-! # Actual defects in any prescribed new subset of a fixed logarithmic interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetDefectDensity

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.SubsetTargetComponents
  PaperP1.LocalDefectBound PaperP1.CriticalBandScale

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_constant (Dwidth Dcut : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      R ≤ Dwidth * (L + 1) → H ≤ Dcut * (L + 1) →
      ∀ y ∈ dyadicBlock N, ∀ V : Finset ℕ,
      (∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ((defective y H R V).card : ℝ) ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, Nlocal, hlocal⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2 : ℝ) 2 lowerScale upperScale ((10 * (Dcut + 1) : ℕ) : ℝ) ((2 * Dwidth : ℕ) : ℝ)
    (by norm_num) (by norm_num) lowerScale_pos upperScale_pos.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  obtain ⟨Nr, hr⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((2 * Dwidth : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max 2 (max Ns (max Nr Nlocal)), ?_⟩
  intro N hN L H R hcrit hR hH y hy V hV
  obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
  have hwidth : 2 * Dwidth * (L + 1) < N := by
    have hh := hr N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hRhalf : 2 * R < N := by nlinarith only [hR, hwidth]
  have hyR : R < y := by omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((y - R : ℕ) : ℝ) := by
    have hh : (N : ℝ) ≤ 2 * ((y - R : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2 * (y - R) by omega)
    linarith only [hh]
  have hbaseUpper : ((y - R : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast (show y - R ≤ 2 * N by omega)
  have hcode : ((10 * (H + 1) : ℕ) : ℝ) ≤ ((10 * (Dcut + 1) : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast AsymmetricComponentHostCount.cutoff_budget hH
  have hlength : ((2 * R : ℕ) : ℝ) ≤ ((2 * Dwidth : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    have hh : 2 * R ≤ 2 * Dwidth * (L + 1) := by nlinarith only [hR]
    exact_mod_cast hh
  have hsub : V.filter (DefectivePredicate.HDefective (10 * (H + 1))) ⊆
      defectsInInterval (10 * (H + 1)) (y - R) (2 * R) := by
    intro n hn
    obtain ⟨hnV, hnD⟩ := mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hV n hnV)
    exact mem_defectsInInterval.mpr ⟨by omega, by omega, hnD⟩
  calc
    _ ≤ ((V.filter (DefectivePredicate.HDefective (10 * (H + 1)))).card : ℝ) := by
      exact_mod_cast defective_card_le_values (H := H) hyR V
    _ ≤ ((defectsInInterval (10 * (H + 1)) (y - R) (2 * R)).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ _ := hlocal N (by omega) ((L + 1 : ℕ) : ℝ) (10 * (H + 1)) (y - R) (2 * R)
      (hs N (by omega) L hcrit).1 (hs N (by omega) L hcrit).2 hcode hlength hbase hbaseUpper

theorem uniform_density (C ε : ℝ) (Dwidth Dcut : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      R ≤ Dwidth * (L + 1) → H ≤ Dcut * (L + 1) →
      ∀ y ∈ dyadicBlock N, ∀ V : Finset ℕ,
      (∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ((defective y H R V).card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, _hK, hK⟩ := uniform_constant Dwidth Dcut
  obtain ⟨Nc, hc⟩ := hK C
  obtain ⟨B₀, hb⟩ := ElementaryLogGrowth.log_ge_eventually (K / ε)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  refine ⟨max Nc Ng, ?_⟩
  intro N hN L H R hcrit hR hH y hy V hV
  have hgeom := hg N (by omega) L hcrit
  have hlog := (div_le_iff₀ hε).mp (hb (L + 1) hgeom.2.1).1
  have hlogpos : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by have hh := hgeom.2.2.1; omega))
  have hcoef : K / Real.log ((L + 1 : ℕ) : ℝ) ≤ ε := (div_le_iff₀ hlogpos).mpr (by nlinarith only [hlog])
  calc
    _ ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := hc N (by omega) L H R hcrit hR hH y hy V hV
    _ = (K / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)

end PaperP1.SubsetDefectDensity
