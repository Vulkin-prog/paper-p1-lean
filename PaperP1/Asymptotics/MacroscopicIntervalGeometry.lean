module

public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Analysis.ElementaryLogGrowth
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # The literal macroscopic interval and uniform logarithmic source geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicIntervalGeometry

open Finset Filter PaperP1.CriticalBandScale

def starts (M : ℕ) (δ : ℝ) : Finset ℕ := Ico ⌈(M : ℝ) ^ δ⌉₊ M

theorem mem_starts_iff {M x : ℕ} {δ : ℝ} :
    x ∈ starts M δ ↔ (M : ℝ) ^ δ ≤ x ∧ x < M := by
  constructor
  · intro h
    have hi := mem_Ico.mp h
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hi.1), hi.2⟩
  · rintro ⟨hlo, hhi⟩
    exact mem_Ico.mpr ⟨Nat.ceil_le.mpr hlo, hhi⟩

theorem starts_pos {M x : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) (hx : x ∈ starts M δ) :
    2 ≤ x := by
  have hpow : 1 < (M : ℝ) ^ δ := Real.one_lt_rpow (by exact_mod_cast (show 1 < M by omega)) hδ
  have h : 1 < x := by exact_mod_cast hpow.trans_le (mem_starts_iff.mp hx).1
  omega

theorem log_lower {M x : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hx : x ∈ starts M δ) :
    δ * Real.log M ≤ Real.log x := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h := Real.log_le_log (Real.rpow_pos_of_pos hm δ) (mem_starts_iff.mp hx).1
  rw [Real.log_rpow hm] at h
  simpa only [mul_comm] using h

theorem uniform_geometry (C δ : ℝ) (T : ℕ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      ∀ x ∈ starts M δ, T ≤ L + 1 ∧ 8 * (L + 1) ≤ x ∧
        2 * Real.log 2 ≤ Real.log x ∧
        (δ / (2 * upperScale)) * (L + 1 : ℕ) ≤ Real.log x / 2 := by
  have hu : 0 < upperScale := upperScale_pos
  obtain ⟨MB, hB⟩ := critical_band_scale C
  obtain ⟨ML, hL⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually
    (max ((T : ℝ) / lowerScale) ((2 * Real.log 2) / δ))
  have hthin : Tendsto (fun M : ℕ ↦ Real.log M / (M : ℝ) ^ δ) atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (PaperP1.PNT.tendsto_pow_log_div_pow_atTop δ 1 hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨MS, hS⟩ := eventually_atTop.mp
    ((tendsto_order.1 hthin).2 (1 / (8 * upperScale)) (by positivity))
  refine ⟨max MB (max ML MS), ?_⟩
  intro M hM L hcrit x hx
  have hm : 2 ≤ M := by omega
  have hmpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨hBlo, hBhi⟩ := hB M (by omega) L hcrit
  have hlog := (hL M (by omega)).1
  have hroot := (mem_starts_iff.mp hx).1
  have hlogx := log_lower hm hx
  have hT : T ≤ L + 1 := by
    have hh := (div_le_iff₀ lowerScale_pos).mp ((le_max_left _ _).trans hlog)
    exact_mod_cast (show (T : ℝ) ≤ (L + 1 : ℕ) by nlinarith only [hh, hBlo])
  have hsmall := (div_lt_div_iff₀ (Real.rpow_pos_of_pos hmpos δ)
    (mul_pos (by norm_num : (0 : ℝ) < 8) upperScale_pos)).mp (hS M (by omega))
  have hbase : 8 * (L + 1) ≤ x := by
    have hh : (8 : ℝ) * (L + 1 : ℕ) ≤ x := by nlinarith only [hsmall, hBhi, hroot]
    exact_mod_cast hh
  have hlarge : 2 * Real.log 2 ≤ Real.log x := by
    have hh := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hlog)
    nlinarith only [hh, hlogx]
  have hwidth : (δ / (2 * upperScale)) * (L + 1 : ℕ) ≤ Real.log x / 2 := by
    have hh := mul_le_mul_of_nonneg_left hBhi (div_nonneg hδ.le (by positivity : (0 : ℝ) ≤ 2 * upperScale))
    have he : (δ / (2 * upperScale)) * (upperScale * Real.log M) = δ * Real.log M / 2 := by
      field_simp [hu.ne']
    rw [he] at hh
    linarith only [hh, hlogx]
  exact ⟨hT, hbase, hlarge, hwidth⟩

end PaperP1.MacroscopicIntervalGeometry
