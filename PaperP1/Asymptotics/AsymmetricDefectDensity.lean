module

public import PaperP1.Arithmetic.AsymmetricTargetComponents
public import PaperP1.Asymptotics.AsymmetricComponentHostCount
public import PaperP1.Coding.LocalDefectWindowScale

/-! # Actual new-window defects are uniformly negligible at the enlarged graph cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricDefectDensity

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.AsymmetricTargetComponents
  PaperP1.LocalDefectBound PaperP1.CriticalBandScale

theorem image_defective {y L H : ℕ} (hy : 0 < y) :
    (defective y L H).image (startCompleteVertexLabel y L) = defectsInInterval (10 * (H + 1)) (y - 1) L := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    apply mem_defectsInInterval.mpr
    refine ⟨?_, ?_, (mem_filter.mp hi).2⟩
    · rw [startCompleteVertexLabel_eq_offset hy]
      omega
    · rw [startCompleteVertexLabel_eq_offset hy]
      have hh := i.isLt
      omega
  · intro hn
    obtain ⟨hlo, hhi, hD⟩ := mem_defectsInInterval.mp hn
    let i : Fin (L + 1) := ⟨n - (y - 1), by omega⟩
    have he : startCompleteVertexLabel y L i = n := by
      rw [startCompleteVertexLabel_eq_offset hy]
      dsimp [i]
      omega
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, by simpa only [he] using hD⟩, he⟩

theorem card_eq_interval {y L H : ℕ} (hy : 0 < y) :
    (defective y L H).card = (defectsInInterval (10 * (H + 1)) (y - 1) L).card := by
  calc
    _ = ((defective y L H).image (startCompleteVertexLabel y L)).card :=
      (card_image_of_injective _ (startCompleteVertexLabel_injective hy)).symm
    _ = _ := congrArg Finset.card (image_defective hy)

theorem uniform_constant (Dcut : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ Dcut * (L + 1) →
      ∀ y ∈ dyadicBlock N, ((defective y L H).card : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, Nlocal, hlocal⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2 : ℝ) 2 lowerScale upperScale ((10 * (Dcut + 1) : ℕ) : ℝ) 1
    (by norm_num) (by norm_num) lowerScale_pos upperScale_pos.le (Nat.cast_nonneg _) (by norm_num)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  refine ⟨max 2 (max Ns Nlocal), ?_⟩
  intro N hN L H hcrit hH y hy
  obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
  have hypos : 0 < y := by omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((y - 1 : ℕ) : ℝ) := by
    have hh : (N : ℝ) ≤ 2 * ((y - 1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2 * (y - 1) by omega)
    linarith only [hh]
  have hbaseUpper : ((y - 1 : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast (show y - 1 ≤ 2 * N by omega)
  have hcode : ((10 * (H + 1) : ℕ) : ℝ) ≤ ((10 * (Dcut + 1) : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast AsymmetricComponentHostCount.cutoff_budget hH
  have hlength : (L : ℝ) ≤ 1 * ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
  rw [card_eq_interval hypos]
  exact hlocal N (by omega) ((L + 1 : ℕ) : ℝ) (10 * (H + 1)) (y - 1) L
    (hs N (by omega) L hcrit).1 (hs N (by omega) L hcrit).2 hcode hlength hbase hbaseUpper

theorem uniform_density (C ε : ℝ) (Dcut : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ Dcut * (L + 1) →
      ∀ y ∈ dyadicBlock N, ((defective y L H).card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, _hK, hK⟩ := uniform_constant Dcut
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

end PaperP1.AsymmetricDefectDensity
