module

public import PaperP1.Arithmetic.PrimeHarmonicWindow
public import PaperP1.Arithmetic.MediumPrimeColumns

/-! # The sharp prime harmonic window at the actual medium-prime cutoffs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MediumPrimeHarmonic

open Finset PaperP1.MediumPrimeColumns PaperP1.PrimeHarmonicWindow

def windowConstant (a : ℝ) : ℝ := 2 * PrimeLogMertens.budget / a + Real.log 10

theorem windowConstant_pos (a : ℝ) (ha : 0 < a) : 0 < windowConstant a := by
  have hbudget := PrimeLogMertens.budget_pos
  have hlog : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  unfold windowConstant
  positivity

theorem log_log_shift (B : ℝ) (hB : 1 < B) :
    0 ≤ Real.log (Real.log (10 * B)) - Real.log (Real.log B) ∧
      Real.log (Real.log (10 * B)) - Real.log (Real.log B) ≤ Real.log 10 / Real.log B := by
  have hBp : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hlogtenB : 0 < Real.log (10 * B) := Real.log_pos (by linarith)
  have hlogmul : Real.log (10 * B) = Real.log 10 + Real.log B :=
    Real.log_mul (by norm_num) (ne_of_gt hBp)
  have hmono : Real.log B ≤ Real.log (10 * B) := Real.log_le_log hBp (by linarith)
  refine ⟨sub_nonneg.mpr (Real.log_le_log hlogB hmono), ?_⟩
  have h := Real.log_le_sub_one_of_pos (div_pos hlogtenB hlogB)
  rw [Real.log_div (ne_of_gt hlogtenB) (ne_of_gt hlogB)] at h
  have he : Real.log (10 * B) / Real.log B - 1 = Real.log 10 / Real.log B := by
    rw [hlogmul, add_div, div_self (ne_of_gt hlogB)]
    ring
  exact h.trans_eq he

theorem log_log_rpow (B a : ℝ) (hB : 1 < B) (ha : 0 < a) :
    Real.log (Real.log (B ^ a)) = Real.log a + Real.log (Real.log B) := by
  rw [Real.log_rpow (by linarith : 0 < B) a,
    Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.log_pos hB))]

theorem medium_primes_window (L : ℕ) (z : ℝ) :
    harmonic z ((10 * (L + 1) : ℕ) : ℝ) = ∑ p ∈ mediumPrimes L ⌊z⌋₊, 1 / (p : ℝ) := by
  rw [PrimeHarmonicWindow.harmonic, Nat.floor_natCast]
  have he : (Ioc ⌊z⌋₊ (10 * (L + 1))).filter Nat.Prime = mediumPrimes L ⌊z⌋₊ := by
    apply Finset.ext
    intro p
    rw [mem_filter, mem_Ioc, mem_mediumPrimes]
    constructor
    · rintro ⟨⟨hz, hpB⟩, hp⟩
      exact ⟨hp, hz, hpB⟩
    · rintro ⟨hp, hz, hpB⟩
      exact ⟨⟨hz, hpB⟩, hp⟩
  rw [he]

theorem medium_mem_real_cutoff (L : ℕ) (z : ℝ) (hz : 0 ≤ z) (p : ℕ) :
    p ∈ mediumPrimes L ⌊z⌋₊ ↔ p.Prime ∧ z < (p : ℝ) ∧ p ≤ 10 * (L + 1) := by
  rw [mem_mediumPrimes]
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨hp, (Nat.floor_lt hz).mp hlo, hhi⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨hp, (Nat.floor_lt hz).mpr hlo, hhi⟩

theorem finite_medium_bound (L : ℕ) (a : ℝ) (hL : 1 ≤ L) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hpower : 2 ≤ (((L + 1 : ℕ) : ℝ) ^ a)) :
    |(∑ p ∈ mediumPrimes L ⌊((L + 1 : ℕ) : ℝ) ^ a⌋₊, 1 / (p : ℝ)) - Real.log (1 / a)| ≤
      windowConstant a / Real.log ((L + 1 : ℕ) : ℝ) := by
  let B : ℝ := ((L + 1 : ℕ) : ℝ)
  have hB : 1 < B := by dsimp [B]; exact_mod_cast (show 1 < L + 1 by omega)
  have hBp : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hupper : B ^ a ≤ 10 * B :=
    (Real.rpow_le_self_of_one_le hB.le ha₁).trans (by linarith)
  have hcast : ((10 * (L + 1) : ℕ) : ℝ) = 10 * B := by dsimp [B]; push_cast; rfl
  have hwindow := finite_window_bound (B ^ a) (10 * B) hpower hupper
  have hmedium := medium_primes_window L (B ^ a)
  rw [hcast] at hmedium
  rw [hmedium] at hwindow
  let δ := Real.log (Real.log (10 * B)) - Real.log (Real.log B)
  have hδ := log_log_shift B hB
  have hformula : Real.log (Real.log (10 * B)) - Real.log (Real.log (B ^ a)) = Real.log (1 / a) + δ := by
    rw [log_log_rpow B a hB ha, Real.log_div one_ne_zero (ne_of_gt ha), Real.log_one]
    dsimp [δ]
    ring
  rw [hformula, Real.log_rpow hBp a] at hwindow
  have hδabs : |δ| ≤ Real.log 10 / Real.log B := by
    rw [abs_of_nonneg hδ.1]
    exact hδ.2
  calc
    _ = |((∑ p ∈ mediumPrimes L ⌊B ^ a⌋₊, 1 / (p : ℝ)) - (Real.log (1 / a) + δ)) + δ| := by
      congr 1
      ring
    _ ≤ |(∑ p ∈ mediumPrimes L ⌊B ^ a⌋₊, 1 / (p : ℝ)) - (Real.log (1 / a) + δ)| + |δ| := abs_add_le _ _
    _ ≤ 2 * PrimeLogMertens.budget / (a * Real.log B) + Real.log 10 / Real.log B := add_le_add hwindow hδabs
    _ = windowConstant a / Real.log B := by
      unfold windowConstant
      field_simp

theorem power_threshold (L : ℕ) (a : ℝ) (ha : 0 < a)
    (hL : ⌈(2 : ℝ) ^ (1 / a)⌉₊ ≤ L + 1) : 2 ≤ ((L + 1 : ℕ) : ℝ) ^ a := by
  have hcast : (⌈(2 : ℝ) ^ (1 / a)⌉₊ : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hL
  have hbase : (2 : ℝ) ^ (1 / a) ≤ ((L + 1 : ℕ) : ℝ) := (Nat.le_ceil _).trans hcast
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (1 / a)) hbase ha.le
  have he : ((2 : ℝ) ^ (1 / a)) ^ a = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ (ne_of_gt ha), Real.rpow_one]
  rwa [he] at h

theorem eventual_medium_bound (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      |(∑ p ∈ mediumPrimes L ⌊((L + 1 : ℕ) : ℝ) ^ a⌋₊, 1 / (p : ℝ)) - Real.log (1 / a)| ≤
        windowConstant a / Real.log ((L + 1 : ℕ) : ℝ) := by
  refine ⟨max 1 ⌈(2 : ℝ) ^ (1 / a)⌉₊, le_max_left _ _, ?_⟩
  intro L hL
  exact finite_medium_bound L a (by omega) ha ha₁ (power_threshold L a ha (by omega))

end PaperP1.MediumPrimeHarmonic
