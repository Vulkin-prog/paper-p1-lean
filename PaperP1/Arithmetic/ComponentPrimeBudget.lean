module

public import PaperP1.Arithmetic.SharpPrimeCount

/-! # A closed small-prime budget at the exact component cutoff 10B

The already proved PNT is used with error parameter one. No prime-count
estimate is an input. The constant 24 is a convenient explicit upper bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentPrimeBudget

open LocalDefectBound

theorem prime_constraint_cost_eventually :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B →
      (primeCount (10 * B) : ℝ) + 4 ≤ 24 * B / Real.log B := by
  obtain ⟨B₀, hB₀, hcount⟩ := SharpPrimeCount.primeCount_upper_eventually 1 (by norm_num)
  refine ⟨B₀, hB₀, ?_⟩
  intro B hB
  have hBtwo : 2 ≤ B := hB₀.trans hB
  have hBreal : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogmono : Real.log B ≤ Real.log ((10 * B : ℕ) : ℝ) :=
    Real.log_le_log hBreal (by exact_mod_cast (show B ≤ 10 * B by omega))
  have hc := hcount (10 * B) (by omega)
  have hc' : (primeCount (10 * B) : ℝ) ≤ 20 * B / Real.log ((10 * B : ℕ) : ℝ) := by
    convert hc using 1
    norm_num
    ring
  have hc'' : (primeCount (10 * B) : ℝ) ≤ 20 * B / Real.log B :=
    hc'.trans (div_le_div_of_nonneg_left (by positivity) hlog hlogmono)
  have hone : (1 : ℝ) ≤ B / Real.log B :=
    (le_div_iff₀ hlog).mpr (by simpa only [one_mul] using Real.log_le_self (Nat.cast_nonneg B))
  calc
    _ ≤ 20 * B / Real.log B + 4 * (B / Real.log B) := add_le_add hc'' (by linarith)
    _ = _ := by ring

end PaperP1.ComponentPrimeBudget
