module

public import PaperP1.Analysis.UniformBinaryLogBudget
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-! # Exact exponent budgets for the single-auxiliary surface curve cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3AuxiliaryCoverExponentBudget

theorem power_identity (N : ℕ) (hN : 1 ≤ N) (a δ : ℝ) :
    ((N : ℝ) ^ (a + δ / 4)) ^ 2 * (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (δ / 4) =
      (N : ℝ) ^ (2 * a + δ) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [pow_two, ← Real.rpow_add hpos, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  congr 1
  ring

theorem family_bound (N : ℕ) (hN : 1 ≤ N) (a δ E K A : ℝ) (hδ : 0 ≤ δ)
    (hK : 0 ≤ K) (hE : E ≤ K * (N : ℝ) ^ (a + δ / 4)) (hKA : K ≤ A) :
    E ≤ A * (N : ℝ) ^ (a + δ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    E ≤ K * (N : ℝ) ^ (a + δ / 4) := hE
    _ ≤ K * (N : ℝ) ^ (a + δ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith)) hK
    _ ≤ A * (N : ℝ) ^ (a + δ) := mul_le_mul_of_nonneg_right hKA (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem exception_bound (N : ℕ) (hN : 1 ≤ N) (a δ E C K L A : ℝ)
    (hE0 : 0 ≤ E) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hE : E ≤ K * (N : ℝ) ^ (a + δ / 4))
    (hlog : (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 ≤ L * (N : ℝ) ^ (δ / 4))
    (M : ℕ) (hM : 1 / (M : ℝ) ≤ δ / 4) (hA : C * K ^ 2 * L ≤ A) :
    C * E ^ 2 * (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 *
      (N : ℝ) ^ (1 / (M : ℝ)) ≤ A * (N : ℝ) ^ (2 * a + δ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr := Real.rpow_le_rpow_of_exponent_le hNreal hM
  calc
    _ ≤ C * (K * (N : ℝ) ^ (a + δ / 4)) ^ 2 *
        (L * (N : ℝ) ^ (δ / 4)) * (N : ℝ) ^ (δ / 4) := by gcongr
    _ = (C * K ^ 2 * L) *
        (((N : ℝ) ^ (a + δ / 4)) ^ 2 * (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (δ / 4)) := by ring
    _ = (C * K ^ 2 * L) * (N : ℝ) ^ (2 * a + δ) := by rw [power_identity N hN]
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end PaperP1.P3AuxiliaryCoverExponentBudget
