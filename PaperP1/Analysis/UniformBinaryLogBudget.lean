module

public import PaperP1.Analysis.BinaryLogarithmicBudget

/-! # A uniform subpower bound for the actual binary logarithmic budget at every positive height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformBinaryLogBudget

open DegreeUniformAffineParameters

theorem monotone : Monotone logarithmicBudget := by
  intro M N hMN
  simp only [logarithmicBudget, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right hMN) 1

theorem absorption (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ H : ℕ, 1 ≤ H → (logarithmicBudget H : ℝ) ^ k ≤ L * (H : ℝ) ^ δ := by
  obtain ⟨N₀, _hN₀, hlarge⟩ := BinaryLogarithmicBudget.polynomial_absorption 1 k δ hδ
  let L : ℝ := 1 + (logarithmicBudget N₀ : ℝ) ^ k
  have hL : 0 < L := by dsimp [L]; positivity
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (pow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨L, hL, ?_⟩
  intro H hH
  have hroot : 1 ≤ (H : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hH) hδ.le
  by_cases hN : N₀ ≤ H
  · have hh := hlarge H hN
    have hb : (logarithmicBudget H : ℝ) ^ k ≤ (H : ℝ) ^ δ := by
      have hp0 : 0 ≤ (logarithmicBudget H : ℝ) ^ k := by positivity
      simpa only [one_mul, abs_of_nonneg hp0] using hh
    exact hb.trans (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL1)
  · have hh : (logarithmicBudget H : ℝ) ≤ (logarithmicBudget N₀ : ℝ) := by
      exact_mod_cast monotone (show H ≤ N₀ by omega)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hh k
    calc
      _ ≤ (logarithmicBudget N₀ : ℝ) ^ k := hp
      _ ≤ L := by dsimp [L]; linarith
      _ ≤ _ := le_mul_of_one_le_right hL.le hroot

end PaperP1.UniformBinaryLogBudget
