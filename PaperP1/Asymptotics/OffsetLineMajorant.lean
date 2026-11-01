module

public import PaperP1.Arithmetic.OffsetLineCount
public import PaperP1.Asymptotics.SaturationDegrees

/-! # Uniform logarithmic and little-o budgets for the exact line majorant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLineMajorant

open Filter PaperP1.OffsetLineCount PaperP1.CriticalBandScale

def majorantConstant : ℝ := 1 + 3 / lowerScale

theorem majorantConstant_pos : 0 < majorantConstant := by
  unfold majorantConstant
  have h := lowerScale_pos
  positivity

theorem majorantConstant_eq : majorantConstant = 1 + 6 * Real.log 2 := by
  unfold majorantConstant lowerScale
  rw [div_div_eq_mul_div, div_one]
  ring

theorem log_product_le (N B : ℕ) (hN : 12 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N + 1) :
    Real.log (6 * (N : ℝ) * B) ≤ 3 * Real.log N := by
  have hB2 : B ≤ 2 * N := by omega
  have hprod : 6 * N * B ≤ N ^ 3 := by
    calc
      _ ≤ 6 * N * (2 * N) := Nat.mul_le_mul_left (6 * N) hB2
      _ = 12 * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) hN
      _ = _ := by ring
  have hprodR : 6 * (N : ℝ) * B ≤ (N : ℝ) ^ 3 := by exact_mod_cast hprod
  have hpos : 0 < 6 * (N : ℝ) * B := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    positivity
  have h := Real.log_le_log hpos hprodR
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem finite_majorant_bound (N L : ℕ) (Y : ℝ) (hN : 12 ≤ N) (hB : 2 ≤ L + 1)
    (hBN : L + 1 ≤ N + 1) (hlower : lowerScale * Real.log N ≤ ((L + 1 : ℕ) : ℝ))
    (hY : ((L + 1 : ℕ) : ℝ) ≤ Y) :
    sourceMajorant N L Y ≤ majorantConstant * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) := by
  have hBR : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < L + 1 by omega)
  have hlogB : 0 < Real.log (L + 1 : ℕ) := Real.log_pos hBR
  have hlogY : Real.log (L + 1 : ℕ) ≤ Real.log Y := Real.log_le_log (by linarith) hY
  have hMpos : 0 ≤ Real.log (6 * (N : ℝ) * ((L + 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hNR : (12 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlogs := log_product_le N (L + 1) hN (by omega) hBN
  have hlow : Real.log N ≤ ((L + 1 : ℕ) : ℝ) / lowerScale := (le_div_iff₀ lowerScale_pos).mpr (by nlinarith [hlower])
  have hone : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) := by
    apply (le_div_iff₀ hlogB).mpr
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ((L + 1 : ℕ) : ℝ))
    linarith
  unfold sourceMajorant
  have hratio : Real.log (6 * (N : ℝ) * ((L + 1 : ℕ) : ℝ)) / Real.log Y ≤
      (3 / lowerScale) * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) := by
    calc
      _ ≤ Real.log (6 * (N : ℝ) * ((L + 1 : ℕ) : ℝ)) / Real.log (L + 1 : ℕ) :=
        div_le_div_of_nonneg_left hMpos hlogB hlogY
      _ ≤ (3 * Real.log N) / Real.log (L + 1 : ℕ) := div_le_div_of_nonneg_right hlogs hlogB.le
      _ ≤ (3 * (((L + 1 : ℕ) : ℝ) / lowerScale)) / Real.log (L + 1 : ℕ) :=
        div_le_div_of_nonneg_right (by linarith) hlogB.le
      _ = _ := by ring
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) +
        (3 / lowerScale) * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) := add_le_add hone hratio
    _ = _ := by unfold majorantConstant; ring

theorem majorant_bound_eventually (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, ((L + 1 : ℕ) : ℝ) ≤ Y →
        sourceMajorant N L Y ≤ majorantConstant * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) := by
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C 2 (by norm_num)
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  refine ⟨max 12 (max Nfinite Nscale), ?_⟩
  intro N hN L hL Y hY
  obtain ⟨_, hB, hBN, _, _⟩ := hfinite N (by omega) L hL
  exact finite_majorant_bound N L Y (by omega) hB hBN (hscale N (by omega) L hL).1 hY

theorem majorant_little_o_uniform (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, ((L + 1 : ℕ) : ℝ) ≤ Y →
        sourceMajorant N L Y ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Nmajor, hmajor⟩ := majorant_bound_eventually C
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C 2 (by norm_num)
  obtain ⟨Nlog, hlog⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop (Real.exp (majorantConstant / ε) / lowerScale)))
  refine ⟨max Nmajor (max Nscale (max Nfinite Nlog)), ?_⟩
  intro N hN L hL Y hY
  have hB := (hfinite N (by omega) L hL).2.1
  have hBR : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < L + 1 by omega)
  have hlogB : 0 < Real.log (L + 1 : ℕ) := Real.log_pos hBR
  have hBexp : Real.exp (majorantConstant / ε) ≤ ((L + 1 : ℕ) : ℝ) := by
    have hH := (div_le_iff₀ lowerScale_pos).mp (hlog N (by omega))
    nlinarith [(hscale N (by omega) L hL).1]
  have hlogLower : majorantConstant / ε ≤ Real.log (L + 1 : ℕ) := by
    have h := Real.log_le_log (Real.exp_pos _) hBexp
    simpa only [Real.log_exp] using h
  have hC : majorantConstant / Real.log (L + 1 : ℕ) ≤ ε := by
    apply (div_le_iff₀ hlogB).mpr
    have h := (div_le_iff₀ hε).mp hlogLower
    nlinarith
  calc
    _ ≤ majorantConstant * ((L + 1 : ℕ) : ℝ) / Real.log (L + 1 : ℕ) := hmajor N (by omega) L hL Y hY
    _ = (majorantConstant / Real.log (L + 1 : ℕ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

end PaperP1.OffsetLineMajorant
