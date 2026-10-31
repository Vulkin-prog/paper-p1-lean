module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! # A closed coarse logarithmic factorial estimate

Only the proved finite lower Stirling inequality and n!≤n^n are used.
No asymptotic factorial formula is an assumption.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialLogBounds

theorem log_factorial_bounds (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m ≤ Real.log (m.factorial : ℝ) ∧
      Real.log (m.factorial : ℝ) ≤ (m : ℝ) * Real.log m := by
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.two_le_pi])
  constructor
  · have h := Stirling.le_log_factorial_stirling (show m ≠ 0 by omega)
    linarith
  · have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
    have h := Real.log_le_log (by positivity : (0 : ℝ) < m.factorial) hfac
    simpa only [Real.log_pow] using h

theorem log_factorial_error (m : ℕ) (hm : 1 ≤ m) :
    |Real.log (m.factorial : ℝ) - (m : ℝ) * Real.log m| ≤ (m : ℝ) := by
  have h := log_factorial_bounds m hm
  apply abs_le.mpr
  constructor <;> linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

end PaperP1.FactorialLogBounds
