module

public import PaperP1.Coding.WindowRelationCode

/-!
# The sharp numerical Griesmer threshold

The exact ceiling sum dominates the minimum distance times the geometric
factor `2 * (1 - 2^(-t))`. This gives a real logarithmic prime budget without
rounding terms, suitable for the uniform asymptotic application of PNT.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRigidityThreshold

open PaperP1.Arithmetic Finset LocalDefectBound LocalRigidityCode WindowRelationCode

local instance rigidityThresholdPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def griesmerFactor (t : ℕ) : ℝ := ∑ i ∈ Finset.range t, (2 : ℝ)⁻¹ ^ i

@[simp]
theorem griesmerFactor_zero : griesmerFactor 0 = 0 := by
  simp only [griesmerFactor, Finset.range_zero, Finset.sum_empty]

theorem griesmerFactor_succ (t : ℕ) :
    griesmerFactor (t + 1) = griesmerFactor t + (2 : ℝ)⁻¹ ^ t := by
  exact Finset.sum_range_succ _ _

theorem griesmerFactor_closed (t : ℕ) :
    griesmerFactor t = 2 * (1 - (2 : ℝ)⁻¹ ^ t) := by
  induction t with
  | zero => simp only [griesmerFactor_zero, pow_zero, sub_self, mul_zero]
  | succ t ih =>
      rw [griesmerFactor_succ, ih, pow_succ]
      norm_num
      ring

/-- The paper's exponent is an integer difference, not natural subtraction. -/
theorem griesmerFactor_eq_paper (t : ℕ) :
    griesmerFactor t = 2 - (2 : ℝ) ^ (1 - (t : ℤ)) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [griesmerFactor_closed, zpow_sub₀ h2, zpow_one, zpow_natCast]
  simp only [div_eq_mul_inv, inv_pow]
  ring

@[simp]
theorem griesmerFactor_one : griesmerFactor 1 = 1 := by
  norm_num [griesmerFactor]

@[simp]
theorem griesmerFactor_two : griesmerFactor 2 = 3 / 2 := by
  norm_num [griesmerFactor, Finset.sum_range_succ]

/-- Each ceiling is at least the original real distance divided by its power of two. -/
theorem griesmer_ceiling_sum_ge (U B t : ℕ) :
    (Real.log U / Real.log (64 * (B : ℝ))) * griesmerFactor t ≤
      ∑ i ∈ Finset.range t, (⌈(rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊ : ℝ) := by
  unfold griesmerFactor
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    (Real.log U / Real.log (64 * (B : ℝ))) * (2 : ℝ)⁻¹ ^ i =
        (Real.log U / Real.log (64 * (B : ℝ))) / (2 : ℝ) ^ i := by
      simp only [div_eq_mul_inv, inv_pow]
    _ ≤ (rungeDistance U B : ℝ) / (2 : ℝ) ^ i :=
      div_le_div_of_nonneg_right (Nat.le_ceil _) (by positivity)
    _ ≤ _ := Nat.le_ceil _

theorem window_relation_finrank_lt_of_geometric {U B t : ℕ}
    (hB : 1 ≤ B) (hU : 2 * B ≤ U)
    (hbudget : (primeCount B : ℝ) + 1 + t <
      (Real.log U / Real.log (64 * (B : ℝ))) * griesmerFactor t) :
    Module.finrank F₂ (windowRelationCode U B) < t := by
  by_contra h
  have hg := window_relation_griesmer_real hB hU (Nat.le_of_not_gt h)
  have hl := griesmer_ceiling_sum_ge U B t
  linarith

/-- A logarithmic budget with ordinary real arithmetic rules out dimension t. -/
theorem window_relation_finrank_lt_of_log_budget {U B t : ℕ}
    (hB : 1 ≤ B) (hU : 2 * B ≤ U)
    (hbudget : ((primeCount B : ℝ) + 1 + t) * Real.log (64 * (B : ℝ)) <
      Real.log U * griesmerFactor t) :
    Module.finrank F₂ (windowRelationCode U B) < t := by
  have hlog : 0 < Real.log (64 * (B : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  apply window_relation_finrank_lt_of_geometric hB hU
  have h := (lt_div_iff₀ hlog).mpr hbudget
  simpa only [div_mul_eq_mul_div] using h

end PaperP1.LocalRigidityThreshold
