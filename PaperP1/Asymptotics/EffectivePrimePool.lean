module

public import PaperP1.Asymptotics.EffectiveTailScale
public import PaperP1.Asymptotics.LogSquaredPrimePool

/-! # A square-root Rankin envelope at a two-thirds-logarithmic order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectivePrimePool

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget
  PaperP1.WindowPoolCount PaperP1.SmoothSquarefreeCount PaperP1.LogarithmicPrimeBudget
  PaperP1.CriticalBandScale PaperP1.EffectiveTailScale

def coefficient : ℝ := 1 + upperScale * (Real.log 4 + 4)

def envelope (N : ℕ) : ℝ := (coefficient * Real.log N * rootScale N) ^ 2

theorem coefficient_ge_one : 1 ≤ coefficient := by
  unfold coefficient
  have hu := upperScale_pos
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith

theorem raw_budget_le_envelope {A : Finset ℕ} {N L j : ℕ} (hN : 3 ≤ N)
    (hH : 1 ≤ Real.log N) (hh : 1 ≤ Real.log (Real.log N))
    (hA : A ⊆ Model.dyadicBlock N) (hL : L ≤ N) (hj : A.card ≤ j)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (horder : (j : ℝ) ≤ 2 * orderScale N) :
    (∑ p ∈ primePool (rawValues A L) (L + 1), Real.log p) ≤ envelope N := by
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : 0 ≤ Real.log N := by linarith
  have hu := upperScale_pos
  obtain ⟨_, hq, _⟩ := unit_scales hh
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hthree : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 * N)
      (by nlinarith : 3 * (N : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using h
  have hHHq : Real.log N ≤ (Real.log N) ^ 2 * orderScale N := by
    have hs : Real.log N ≤ (Real.log N) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hq (sq_nonneg (Real.log N))
    nlinarith
  have hsmall : ((L + 1 : ℕ) : ℝ) * Real.log 4 ≤
      upperScale * Real.log 4 * (Real.log N) ^ 2 * orderScale N := by
    calc
      _ ≤ (upperScale * Real.log N) * Real.log 4 := mul_le_mul_of_nonneg_right hwidth hlog4
      _ = (upperScale * Real.log 4) * Real.log N := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hHHq (mul_nonneg upperScale_pos.le hlog4)
  have hold : (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) ≤
      4 * upperScale * (Real.log N) ^ 2 * orderScale N := by
    calc
      _ ≤ (2 * orderScale N) * (upperScale * Real.log N) * (2 * Real.log N) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul (mul_le_mul horder hwidth (by positivity) (by linarith)) hthree
            (Real.log_natCast_nonneg _) (by positivity)
      _ = _ := by ring
  have hraw := raw_primePool_log_sum_le hA (by omega) hL hj
  have ha := coefficient_ge_one
  have ha2 : coefficient ≤ coefficient ^ 2 := by nlinarith
  have hcoef := mul_le_mul_of_nonneg_right ha2
    (mul_nonneg (sq_nonneg (Real.log N)) (by linarith : 0 ≤ orderScale N))
  have henvelope : envelope N = coefficient ^ 2 * (Real.log N) ^ 2 * orderScale N := by
    unfold envelope
    rw [mul_pow, mul_pow, root_sq (by linarith : 0 ≤ Real.log (Real.log N))]
  rw [henvelope]
  unfold coefficient at hcoef ⊢
  push_cast at hraw hsmall hold
  nlinarith

theorem envelope_gt_one {N : ℕ} (hH : 2 ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N)) : 1 < envelope N := by
  have ha := coefficient_ge_one
  have ht := (unit_scales hh).1
  unfold envelope
  have hbase : 2 ≤ coefficient * Real.log N * rootScale N := by
    have h := mul_le_mul ha hH (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ coefficient)
    have h' := mul_le_mul_of_nonneg_left ht (by nlinarith : 0 ≤ coefficient * Real.log N)
    nlinarith
  nlinarith

theorem log_envelope_lower {N : ℕ} (hH : 2 ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N)) : Real.log (Real.log N) ≤ Real.log (envelope N) := by
  have ha := coefficient_ge_one
  have ht := (unit_scales hh).1
  have hbase : Real.log N ≤ coefficient * Real.log N * rootScale N := by
    have h := mul_le_mul_of_nonneg_right ha (by linarith : 0 ≤ Real.log N)
    have h' := mul_le_mul_of_nonneg_left ht (by nlinarith : 0 ≤ coefficient * Real.log N)
    nlinarith
  have hY : Real.log N ≤ envelope N := by unfold envelope; nlinarith
  exact Real.log_le_log (by linarith) hY

theorem euler_cost_bound {N : ℕ} (hH : 2 ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N)) :
    budgetConstant * (envelope N) ^ (1 - (1 / 2 : ℝ)) / Real.log (envelope N) ≤
      budgetConstant * coefficient * scale N := by
  have hlogY := log_envelope_lower hH hh
  have hhpos : 0 < Real.log (Real.log N) := by linarith
  have ha := coefficient_ge_one
  have ht := (unit_scales hh).1
  have hbase : 0 ≤ coefficient * Real.log N * rootScale N := by positivity
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow, envelope, Real.sqrt_sq_eq_abs, abs_of_nonneg hbase]
  have hnum : 0 ≤ budgetConstant * (coefficient * Real.log N * rootScale N) := by
    have hC := budgetConstant_pos
    positivity
  calc
    _ ≤ budgetConstant * (coefficient * Real.log N * rootScale N) / Real.log (Real.log N) :=
      div_le_div_of_nonneg_left hnum hhpos hlogY
    _ = _ := by
      rw [← root_mul_orderScale hhpos]
      unfold scale
      have ht0 : rootScale N ≠ 0 := by linarith
      have hq0 : orderScale N ≠ 0 := by have h := (unit_scales hh).2.1; linarith
      field_simp

theorem count_bound {N : ℕ} (hN : 3 ≤ N) (hH : 2 ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N)) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ envelope N) :
    ((naturalValues P (3 * N)).card : ℝ) ≤
      Real.exp (Real.log N / 2 + Real.log 3 / 2 + budgetConstant * coefficient * scale N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hX : (1 : ℝ) ≤ (3 * N : ℕ) := by exact_mod_cast (show 1 ≤ 3 * N by omega)
  have hcount := PrimeBudgetRankin.log_values_le P hP ((3 * N : ℕ) : ℝ) hX
    (envelope N) (1 / 2) (envelope_gt_one hH hh) le_rfl (by norm_num) hbudget
  simp only [values, Nat.floor_natCast] at hcount
  have hlogX : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hn.ne']
  rw [hlogX] at hcount
  have hcost := euler_cost_bound hH hh
  have hpos : (0 : ℝ) < (naturalValues P (3 * N)).card := by
    have h := card_values_pos P ((3 * N : ℕ) : ℝ) hX
    simpa only [values, Nat.floor_natCast, Nat.cast_pos] using h
  calc
    _ = Real.exp (Real.log ((naturalValues P (3 * N)).card : ℝ)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end PaperP1.EffectivePrimePool
