module

public import PaperP1.Coding.LocalDefectBound
public import PaperP1.Arithmetic.ChebyshevPrimeCount
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Explicit prime budgets and a direct logarithmic coding radius

Finite ratio-budget proof patterns adapt PaperC/Coding/IntervalDefectBound.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, blob
dbb7fa8dd13e986eb396d88a883ba011d338752b, Apache-2.0.
The direct radius and its estimates use P1's degree-uniform Runge constant.
-/

namespace PaperP1.LocalDefectRate

open LocalDefectBound

theorem card_lt_of_count_ratio
    {H U R t A : ℕ} (hR : 1 ≤ R) (hU : 2 * R ≤ U) (ht : 1 ≤ t)
    (hlog : (2 * t : ℝ) * Real.log (64 * (R : ℝ)) < Real.log U)
    (hratio : primeCount H + 1 ≤ A * t) :
    (defectsInInterval H U R).card < 2 * t * 2 ^ (A + 1) := by
  apply (card_defectsInInterval_lt_of_log hR hU ht hlog).trans_le
  apply max_le
  · have hpow : A ≤ 2 ^ (A + 1) :=
      (Nat.le_of_lt Nat.lt_two_pow_self).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ A))
    calc
      primeCount H + 1 ≤ A * t := hratio
      _ ≤ 2 ^ (A + 1) * t := Nat.mul_le_mul_right t hpow
      _ ≤ 2 * t * 2 ^ (A + 1) := by
        nlinarith [Nat.zero_le (2 ^ (A + 1))]
  · have hdiv : (primeCount H + 1) / t ≤ A :=
      Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hratio)
    exact Nat.mul_le_mul_left (2 * t)
      (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hdiv 1))

theorem card_lt_of_chebyshev_budget
    {H U R t A : ℕ} (hH : 4 ≤ H) (hR : 1 ≤ R)
    (hU : 2 * R ≤ U) (ht : 1 ≤ t)
    (hlog : (2 * t : ℝ) * Real.log (64 * (R : ℝ)) < Real.log U)
    (hbudget : (7 * H) / Nat.log 2 H + 1 ≤ A * t) :
    (defectsInInterval H U R).card < 2 * t * 2 ^ (A + 1) := by
  apply card_lt_of_count_ratio hR hU ht hlog
  have hcount : primeCount H ≤ (7 * H) / Nat.log 2 H := by
    simpa only [primeCount] using
      ChebyshevPrimeCount.count_le_seven_mul_div_log hH
  exact (Nat.add_le_add_right hcount 1).trans hbudget

/-- Direct floored radius, with no auxiliary cap or degree inside the logarithm. -/
noncomputable def codingRadius (U R : ℕ) : ℕ :=
  ⌊Real.log U / (4 * Real.log (64 * (R : ℝ)))⌋₊

theorem codingRadius_log_condition
    {U R : ℕ} (hU : 1 ≤ U) (hR : 1 ≤ R) :
    (4 * codingRadius U R : ℝ) * Real.log (64 * (R : ℝ)) ≤ Real.log U := by
  have hlogR : 0 < Real.log (64 * (R : ℝ)) := by
    apply Real.log_pos
    have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hlogU : 0 ≤ Real.log (U : ℝ) := Real.log_nonneg (by exact_mod_cast hU)
  have hfloor : (codingRadius U R : ℝ) ≤
      Real.log U / (4 * Real.log (64 * (R : ℝ))) :=
    Nat.floor_le (div_nonneg hlogU (by positivity))
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * Real.log (64 * (R : ℝ)))).mp hfloor
  nlinarith

theorem codingRadius_log_strict
    {U R : ℕ} (hU : 2 ≤ U) (hR : 1 ≤ R) :
    (2 * codingRadius U R : ℝ) * Real.log (64 * (R : ℝ)) < Real.log U := by
  have hweak := codingRadius_log_condition (by omega : 1 ≤ U) hR
  have hpos : 0 < Real.log (U : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  nlinarith

theorem codingRadius_pos
    {U R : ℕ} (hR : 1 ≤ R)
    (hlarge : 4 * Real.log (64 * (R : ℝ)) ≤ Real.log U) :
    1 ≤ codingRadius U R := by
  apply (Nat.one_le_floor_iff _).mpr
  have hden : 0 < 4 * Real.log (64 * (R : ℝ)) := by
    have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
    exact mul_pos (by norm_num) (Real.log_pos (by linarith))
  exact (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hlarge)

/-- Explicit real local rate once the elementary prime budget is verified.
The fixed constant depends only on the natural budget parameter A. -/
theorem card_cast_lt_log_div
    {H U R A : ℕ} (hH : 4 ≤ H) (hR : 1 ≤ R) (hU : 2 * R ≤ U)
    (hlarge : 4 * Real.log (64 * (R : ℝ)) ≤ Real.log U)
    (hbudget : (7 * H) / Nat.log 2 H + 1 ≤ A * codingRadius U R) :
    ((defectsInInterval H U R).card : ℝ) <
      ((2 * 2 ^ (A + 1) : ℕ) : ℝ) *
        (Real.log U / (4 * Real.log (64 * (R : ℝ)))) := by
  have ht := codingRadius_pos hR hlarge
  have hcard := card_lt_of_chebyshev_budget hH hR hU ht
    (codingRadius_log_strict (by omega) hR) hbudget
  have hcast :
      ((defectsInInterval H U R).card : ℝ) <
        ((2 * codingRadius U R * 2 ^ (A + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
  have hfloor : (codingRadius U R : ℝ) ≤
      Real.log U / (4 * Real.log (64 * (R : ℝ))) := by
    have hlogU : 0 ≤ Real.log (U : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ U by omega))
    have hlogR : 0 ≤ Real.log (64 * (R : ℝ)) := by
      apply Real.log_nonneg
      have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    exact Nat.floor_le (div_nonneg hlogU (by positivity))
  calc
    _ < ((2 * codingRadius U R * 2 ^ (A + 1) : ℕ) : ℝ) := hcast
    _ = ((2 * 2 ^ (A + 1) : ℕ) : ℝ) * (codingRadius U R : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)

end PaperP1.LocalDefectRate

