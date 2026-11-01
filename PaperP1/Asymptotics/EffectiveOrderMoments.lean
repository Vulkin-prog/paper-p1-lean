module

public import PaperP1.Asymptotics.EffectivePrimePool
public import PaperP1.Model.FactorialBranching

/-! # Actual factorial moments at the effective-support order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveOrderMoments

open Filter Finset PaperP1.Model PaperP1.FactorialCountMoments PaperP1.FactorialBranching
  PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget PaperP1.CriticalBandScale
  PaperP1.EffectiveTailScale PaperP1.LogarithmicPrimeBudget PaperP1.ConditionalWindowRank

def errorConstant : ℝ := budgetConstant * EffectivePrimePool.coefficient +
  |Real.log upperScale| + Real.log 3 + 1

def envelope (N : ℕ) : ℝ := Real.exp (Real.log N / 2 + errorConstant * scale N)

theorem errorConstant_pos : 0 < errorConstant := by
  have hC := budgetConstant_pos
  have ha := EffectivePrimePool.coefficient_ge_one
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  unfold errorConstant
  positivity

theorem finite_exception_bound {A : Finset ℕ} {N L j : ℕ} (hN : 3 ≤ N)
    (hH : 2 ≤ Real.log N) (hh : 1 ≤ Real.log (Real.log N))
    (hsq : (Real.log (Real.log N)) ^ 2 ≤ Real.log N)
    (hA : A ⊆ dyadicBlock N) (hL : L ≤ N) (hj : A.card ≤ j)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (horder : (j : ℝ) ≤ 2 * orderScale N) :
    ((badStarts N L (rawValues A L)).card : ℝ) ≤ envelope N := by
  have hHpos : 0 < Real.log N := by linarith
  have hbudget := EffectivePrimePool.raw_budget_le_envelope hN (by linarith) hh hA hL hj hwidth horder
  have hpool := EffectivePrimePool.count_bound hN hH hh (primePool (rawValues A L) (L + 1))
    (fun p hp ↦ primePool_prime _ _ _ hp) hbudget
  change ((WindowPoolCount.poolValues (rawValues A L) (L + 1) (3 * N)).card : ℝ) ≤ _ at hpool
  have hhalf := badStarts_card_half (rawValues A L) (by omega) hL
  have hcoarse : ((badStarts N L (rawValues A L)).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * (WindowPoolCount.poolValues (rawValues A L) (L + 1) (3 * N)).card := by
    have hnonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) *
        (WindowPoolCount.poolValues (rawValues A L) (L + 1) (3 * N)).card := by positivity
    nlinarith
  have hB : ((L + 1 : ℕ) : ℝ) ≤ Real.exp (|Real.log upperScale| + Real.log (Real.log N)) := by
    calc
      _ ≤ upperScale * Real.log N := hwidth
      _ = Real.exp (Real.log upperScale + Real.log (Real.log N)) := by
        rw [Real.exp_add, Real.exp_log upperScale_pos, Real.exp_log hHpos]
      _ ≤ _ := Real.exp_le_exp.mpr (add_le_add (le_abs_self (Real.log upperScale)) le_rfl)
  obtain ⟨hs, hhs⟩ := scale_bounds hh hsq
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hconstant := mul_le_mul_of_nonneg_left hs
    (add_nonneg (abs_nonneg (Real.log upperScale)) hlog3)
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) * (WindowPoolCount.poolValues (rawValues A L) (L + 1) (3 * N)).card := hcoarse
    _ ≤ Real.exp (|Real.log upperScale| + Real.log (Real.log N)) *
        Real.exp (Real.log N / 2 + Real.log 3 / 2 + budgetConstant * EffectivePrimePool.coefficient * scale N) :=
      mul_le_mul hB hpool (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ ≤ envelope N := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      unfold errorConstant
      nlinarith

theorem factorial_bound (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ k : ℕ, k ≤ order N →
      factorialCountMoment (dyadicBlock N) L k ≤ (2 * envelope N) ^ k := by
  obtain ⟨Nscale, hNscale, hscale⟩ := conditions_eventually
  obtain ⟨Nband, hband⟩ := critical_band_scale C
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  obtain ⟨Nmean, hNmean⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop ((2 : ℝ) ^ C)))
  refine ⟨max Nscale (max Nband (max Nfinite Nmean)), by omega, ?_⟩
  intro N hN L hcrit k hk
  obtain ⟨hH, hh, hsq, _⟩ := hscale N (by omega)
  obtain ⟨hN3, hL, hLN⟩ := hfinite N (by omega) L hcrit
  have hwidth := (hband N (by omega) L hcrit).2
  have hD : ∀ r < k, ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      ((badStarts N L (rawValues A L)).card : ℝ) ≤ envelope N := by
    intro r hr A hA hcard
    have horder : (r : ℝ) ≤ 2 * orderScale N := by
      have hrk : (r : ℝ) ≤ order N := by exact_mod_cast (show r ≤ order N by omega)
      exact hrk.trans (order_bounds hh).2
    exact finite_exception_bound hN3 hH hh hsq hA hLN hcard.le hwidth horder
  have hbound := factorial_le_power (by omega : 2 ≤ N) hL k (envelope N) (Real.exp_pos _).le hD
  have hnom : (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ envelope N := by
    calc
      _ ≤ (2 : ℝ) ^ C := QuadraticOrderMoments.nominal_mean_bound (by omega) hcrit
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hNmean N (by omega)
      _ ≤ envelope N := by
        rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < N by omega))]
        apply Real.exp_le_exp.mpr
        have hs := (scale_bounds hh hsq).1
        have hE := errorConstant_pos
        nlinarith
  exact hbound.trans (pow_le_pow_left₀ (by unfold envelope; positivity) (by linarith) k)

end PaperP1.EffectiveOrderMoments
