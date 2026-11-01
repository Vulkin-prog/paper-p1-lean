module

public import PaperP1.Asymptotics.ConditionalPoolTerm
public import PaperP1.Arithmetic.SquarePoolLower

/-! # Matching lower logarithmic scale for the conditional pool term -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalPoolLower

open Finset PaperP1.Arithmetic PaperP1.OldValuePrimeBudget PaperP1.WindowPoolCount
  PaperP1.CriticalBandScale PaperP1.ConditionalPoolTerm PaperP1.SquarePoolLower

def lowerConstant (C δ : ℝ) : ℝ := Real.exp (-((δ * C + 2) * Real.log 2)) / 2

theorem lowerConstant_pos (C δ : ℝ) : 0 < lowerConstant C δ := div_pos (Real.exp_pos _) (by norm_num)

theorem cast_sub_one_lower (T : ℕ) : (T : ℝ) - 1 ≤ ((T - 1 : ℕ) : ℝ) := by
  by_cases h : 1 ≤ T
  · rw [Nat.cast_sub h, Nat.cast_one]
  · have hT : T = 0 := by omega
    rw [hT]
    norm_num

theorem binary_factor_lower {N L : ℕ} {C δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Real.exp (-((δ * C + 2) * Real.log 2)) * (N : ℝ) ^ (-δ) ≤
      (2 ^ L : ℝ)⁻¹ * (2 : ℝ) ^ (⌊(1 - δ) * (L : ℝ)⌋₊ - 1) := by
  let T := ⌊(1 - δ) * (L : ℝ)⌋₊
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : (L : ℝ) * Real.log 2 ≤ Real.log N + C * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mp hband).2 hlogTwo.le
    rw [sub_mul, div_mul_cancel₀ _ hlogTwo.ne'] at h
    linarith
  have hfloor : (1 - δ) * (L : ℝ) < (T : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsub := cast_sub_one_lower T
  have hfloorLog := mul_le_mul_of_nonneg_right
    (show (1 - δ) * (L : ℝ) - 2 ≤ ((T - 1 : ℕ) : ℝ) by linarith) hlogTwo.le
  have hδlog := mul_le_mul_of_nonneg_left hLlog hδ
  have hexponent : -((δ * C + 2) * Real.log 2) + Real.log N * (-δ) ≤
      (((T - 1 : ℕ) : ℝ) - L) * Real.log 2 := by nlinarith
  calc
    _ = Real.exp (-((δ * C + 2) * Real.log 2) + Real.log N * (-δ)) := by
      rw [Real.exp_add, Real.rpow_def_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
    _ ≤ Real.exp ((((T - 1 : ℕ) : ℝ) - L) * Real.log 2) := Real.exp_le_exp.mpr hexponent
    _ = _ := by
      rw [sub_mul, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

theorem term_lower {N L : ℕ} {C δ : ℝ} (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (A : Finset ℕ) :
    lowerConstant C δ * (N : ℝ) ^ (1 / 2 - δ) ≤ term N L ⌊(1 - δ) * (L : ℝ)⌋₊ A := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbin := binary_factor_lower (by omega : 0 < N) hδ hband
  have hpool := poolValues_card_lower (B := L + 1) (rawValues A L) hN
  have hB : (1 : ℝ) ≤ L + 1 := by have h := Nat.cast_nonneg (α := ℝ) L; linarith
  have hprod := mul_le_mul hbin hpool (by positivity : (0 : ℝ) ≤ Real.sqrt N / 2) (by positivity)
  have hscale : Real.exp (-((δ * C + 2) * Real.log 2)) * (N : ℝ) ^ (-δ) * (Real.sqrt N / 2) =
      lowerConstant C δ * (N : ℝ) ^ (1 / 2 - δ) := by
    rw [Real.sqrt_eq_rpow, lowerConstant, sub_eq_add_neg, Real.rpow_add hNpos]
    ring
  rw [hscale] at hprod
  have hmul := mul_le_mul_of_nonneg_right hB
    (by positivity : (0 : ℝ) ≤ (2 ^ L : ℝ)⁻¹ * (2 : ℝ) ^ (⌊(1 - δ) * (L : ℝ)⌋₊ - 1) *
      (poolValues (rawValues A L) (L + 1) (3 * N)).card)
  unfold term
  nlinarith

theorem term_lower_eventually (C δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, (N : ℝ) ^ (1 / 2 - δ - ε) ≤ term N L ⌊(1 - δ) * (L : ℝ)⌋₊ A := by
  obtain ⟨N₀, hN₀⟩ := ElementaryLogGrowth.log_ge_eventually (-Real.log (lowerConstant C δ) / ε)
  refine ⟨max N₀ 2, le_max_right _ _, fun N hN L hband A ↦ ?_⟩
  obtain ⟨hlog, hN2⟩ := hN₀ N (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (N : ℝ) ^ (-ε) ≤ lowerConstant C δ := by
    rw [Real.rpow_def_of_pos hNpos]
    have h := (div_le_iff₀ hε).mp hlog
    have hexp := Real.exp_le_exp.mpr (show Real.log N * (-ε) ≤ Real.log (lowerConstant C δ) by nlinarith)
    simpa only [Real.exp_log (lowerConstant_pos C δ)] using hexp
  have hmul := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNpos.le (1 / 2 - δ))
  have hpow : (N : ℝ) ^ (-ε) * (N : ℝ) ^ (1 / 2 - δ) = (N : ℝ) ^ (1 / 2 - δ - ε) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  rw [hpow] at hmul
  exact hmul.trans (term_lower (by omega) hδ hband A)

end PaperP1.ConditionalPoolLower
