module

public import PaperP1.Algebra.P3HomogeneousIntegerInterpolation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A polynomial coefficient-height bound pays the actual gradient logarithm uniformly -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CoefficientLogBudget

theorem gradient_log_bound (d T c A H : ℕ) (hd : 0 < d) (hT : 0 < T) (hA : 0 < A)
    (hH : 1 ≤ H) (hbound : A ≤ T * H ^ c) :
    Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * A) : ℕ) : ℝ) +
      ((d - 1 : ℕ) : ℝ) * Real.log (H : ℝ) ≤
    Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * T) : ℕ) : ℝ) +
      ((c + (d - 1) : ℕ) : ℝ) * Real.log (H : ℝ) := by
  let J := Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * d
  have hJ : 0 < J := Nat.mul_pos (P3HomogeneousIntegerInterpolation.index_card_pos _) hd
  have hheight : J * A ≤ (J * T) * H ^ c := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J hbound
  have hleft : (0 : ℝ) < (J * A : ℕ) := by exact_mod_cast Nat.mul_pos hJ hA
  have hright : (0 : ℝ) < (J * T : ℕ) := by exact_mod_cast Nat.mul_pos hJ hT
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hcast : ((J * A : ℕ) : ℝ) ≤ (((J * T) * H ^ c : ℕ) : ℝ) := by exact_mod_cast hheight
  have hh := Real.log_le_log hleft hcast
  have hrhs : (((J * T) * H ^ c : ℕ) : ℝ) = ((J * T : ℕ) : ℝ) * (H : ℝ) ^ c := by
    simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hrhs, Real.log_mul hright.ne' (pow_ne_zero c hHR.ne'), Real.log_pow] at hh
  have hh' : Real.log ((J * A : ℕ) : ℝ) + ((d - 1 : ℕ) : ℝ) * Real.log (H : ℝ) ≤
      Real.log ((J * T : ℕ) : ℝ) + ((c + (d - 1) : ℕ) : ℝ) * Real.log (H : ℝ) := by
    rw [Nat.cast_add, add_mul]
    linarith
  simpa only [J, Nat.mul_assoc] using hh'

end PaperP1.P3CoefficientLogBudget
