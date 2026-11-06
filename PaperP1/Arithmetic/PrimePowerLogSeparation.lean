module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Positivity

/-! # Literal prime-power products give strict integer determinant separation from a logarithmic inequality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimePowerLogSeparation

open Finset

theorem log_product (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (E : ℕ → ℕ) :
    Real.log ((∏ p ∈ S, p ^ E p : ℕ) : ℝ) = ∑ p ∈ S, (E p : ℝ) * Real.log (p : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast (pow_ne_zero (E p) (hprimes p hp).ne_zero)

theorem separation (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (E : ℕ → ℕ) (s W H : ℕ) (hH : 1 ≤ H)
    (hlog : Real.log (s.factorial : ℝ) + (W : ℝ) * Real.log (H : ℝ) <
      ∑ p ∈ S, (E p : ℝ) * Real.log (p : ℝ)) :
    s.factorial * H ^ W < ∏ p ∈ S, p ^ E p := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hspos : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hDpos : (0 : ℝ) < (∏ p ∈ S, p ^ E p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp ↦ pow_pos (hprimes p hp).pos (E p))
  have hApos : (0 : ℝ) < (s.factorial * H ^ W : ℕ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact mul_pos hspos (pow_pos hHpos W)
  have hA : Real.log ((s.factorial * H ^ W : ℕ) : ℝ) =
      Real.log (s.factorial : ℝ) + (W : ℝ) * Real.log (H : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hspos.ne' (pow_ne_zero W hHpos.ne'), Real.log_pow]
  have hh : Real.log ((s.factorial * H ^ W : ℕ) : ℝ) <
      Real.log ((∏ p ∈ S, p ^ E p : ℕ) : ℝ) := by
    rw [hA, log_product S hprimes E]
    exact hlog
  exact_mod_cast (Real.log_lt_log_iff hApos hDpos).mp hh

end PaperP1.PrimePowerLogSeparation
