module

public import PaperP1.Analysis.CubicLogTilt
public import PaperP1.Asymptotics.FixedWindowBranching
public import PaperP1.Asymptotics.ModerateOrder

/-! # The actual prime pool at the growing critical branching order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalBranchingBudget

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ConditionalWindowRank
  PaperP1.OldValuePrimeBudget PaperP1.CriticalBandScale PaperP1.CubicLogTilt
  PaperP1.LogarithmicPrimeBudget PaperP1.SmoothSquarefreeCount

def coefficient (K : ℝ) : ℝ := 1 + upperScale * (Real.log 4 + 2 * K)

theorem coefficient_ge_one {K : ℝ} (hK : 0 ≤ K) : 1 ≤ coefficient K := by
  have hD := upperScale_pos
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold coefficient
  linarith [mul_nonneg hD.le (show 0 ≤ Real.log 4 + 2 * K by linarith)]

theorem raw_budget_le_cubic {A : Finset ℕ} {N L j : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hN : 3 ≤ N) (hA : A ⊆ dyadicBlock N) (hL : L ≤ N) (hj : A.card ≤ j)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (horder : (j : ℝ) ≤ K * Real.log N / Real.log (Real.log N))
    (hh : 4096 ≤ Real.log (Real.log N)) :
    (∑ p ∈ primePool (rawValues A L) (L + 1), Real.log p) ≤
      budget (coefficient K) (Real.log N) := by
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hD := upperScale_pos
  have hNpos : (0 : ℝ) < N := by linarith
  have hH : 0 < Real.log N := Real.log_pos (by linarith)
  have hhpos : 0 < Real.log (Real.log N) := by linarith
  have hlogSelf := Real.log_le_self hH.le
  have hH1 : 1 ≤ Real.log N := by linarith
  have hcube : Real.log N ≤ (Real.log N) ^ 3 / Real.log (Real.log N) := by
    apply (le_div_iff₀ hhpos).mpr
    have h1 : Real.log N * Real.log (Real.log N) ≤ (Real.log N) ^ 2 := by nlinarith
    have h2 : (Real.log N) ^ 2 ≤ (Real.log N) ^ 3 := by nlinarith [sq_nonneg (Real.log N)]
    exact h1.trans h2
  have hthree : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 * N)
      (by nlinarith : 3 * (N : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using h
  have hsmall : ((L + 1 : ℕ) : ℝ) * Real.log 4 ≤
      (upperScale * Real.log 4) * ((Real.log N) ^ 3 / Real.log (Real.log N)) := by
    calc
      _ ≤ (upperScale * Real.log N) * Real.log 4 :=
        mul_le_mul_of_nonneg_right hwidth (Real.log_nonneg (by norm_num))
      _ = (upperScale * Real.log 4) * Real.log N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by positivity)
  have hold : (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) ≤
      (2 * K * upperScale) * ((Real.log N) ^ 3 / Real.log (Real.log N)) := by
    calc
      _ ≤ (K * Real.log N / Real.log (Real.log N)) * (upperScale * Real.log N) * (2 * Real.log N) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul (mul_le_mul horder hwidth (by positivity) (by positivity)) hthree
            (Real.log_natCast_nonneg _) (by positivity)
      _ = _ := by ring
  have hraw := raw_primePool_log_sum_le hA (by omega) hL hj
  have hrest : 0 ≤ (Real.log N) ^ 3 / Real.log (Real.log N) := by positivity
  calc
    _ ≤ (upperScale * Real.log 4) * ((Real.log N) ^ 3 / Real.log (Real.log N)) +
        (2 * K * upperScale) * ((Real.log N) ^ 3 / Real.log (Real.log N)) :=
      hraw.trans (add_le_add hsmall hold)
    _ ≤ (1 + upperScale * (Real.log 4 + 2 * K)) *
        ((Real.log N) ^ 3 / Real.log (Real.log N)) := by nlinarith
    _ = _ := by unfold budget coefficient; ring

def errorConstant (K : ℝ) : ℝ :=
  Real.log (coefficient K) / 9 + budgetConstant + Real.log 3 + |Real.log upperScale| + 5

def rate (K : ℝ) (N : ℕ) : ℝ :=
  2 / 3 * Real.log N - Real.log N * Real.log (Real.log (Real.log N)) /
    (9 * Real.log (Real.log N)) + errorConstant K * (Real.log N / Real.log (Real.log N))

def exceptionEnvelope (K : ℝ) (N : ℕ) : ℝ := Real.exp (rate K N)

theorem errorConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < errorConstant K := by
  have hA := Real.log_nonneg (coefficient_ge_one hK)
  have hC := budgetConstant_pos
  have hthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  unfold errorConstant
  positivity

theorem log_width_le {H B : ℝ} (hH : 0 < H) (hh : 1 ≤ Real.log H)
    (hB : 0 < B) (hwidth : B ≤ upperScale * H) :
    Real.log B ≤ (|Real.log upperScale| + 4) * (H / Real.log H) := by
  obtain ⟨hscale, hlogscale⟩ := log_scale_bounds hH hh
  have hbound := Real.log_le_log hB hwidth
  rw [Real.log_mul upperScale_pos.ne' hH.ne'] at hbound
  have hAbs := le_abs_self (Real.log upperScale)
  have habs := mul_le_mul_of_nonneg_left hscale (abs_nonneg (Real.log upperScale))
  nlinarith

theorem log_product_bound {K : ℝ} (hK : 0 ≤ K) {N B : ℕ} (hN : 3 ≤ N) (hB : 0 < B)
    (hwidth : (B : ℝ) ≤ upperScale * Real.log N)
    (hh : 4096 ≤ Real.log (Real.log N))
    (hlogA : Real.log (coefficient K) ≤ Real.log (Real.log N))
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ budget (coefficient K) (Real.log N)) :
    Real.log B + Real.log ((naturalValues P (3 * N)).card : ℝ) ≤ rate K N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhpos : 0 < Real.log (Real.log N) := by linarith
  have hA := coefficient_ge_one hK
  obtain ⟨hlo, hhi⟩ := tilt_bounds hA hH hh hlogA
  have hcount := PrimeBudgetRankin.log_values_le P hP ((3 * N : ℕ) : ℝ)
    (by exact_mod_cast (show 1 ≤ 3 * N by omega))
    (budget (coefficient K) (Real.log N)) (tilt (coefficient K) (Real.log N))
    (budget_gt_one hA hH hh hlogA) (by linarith) hhi hbudget
  simp only [values, Nat.floor_natCast] at hcount
  rw [budget_tilt_power hA hH hh hlogA] at hcount
  have hlogX : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  rw [hlogX, mul_add] at hcount
  have hmain := tilted_main_bound hA hH hh hlogA
  have hlogs := log_budget_bounds hA hH hh hlogA
  have hlogY : 0 < Real.log (budget (coefficient K) (Real.log N)) := by linarith
  have hcost : budgetConstant * Real.log N / Real.log (budget (coefficient K) (Real.log N)) ≤
      budgetConstant * (Real.log N / Real.log (Real.log N)) := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ budgetConstant_pos.le
    exact div_le_div_of_nonneg_left hH.le hhpos (by linarith)
  have hthree : tilt (coefficient K) (Real.log N) * Real.log 3 ≤ Real.log 3 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hscale := (log_scale_bounds hH (by linarith)).1
  have hthree' := mul_le_mul_of_nonneg_left hscale (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
  have hwidth' := log_width_le hH (by linarith : 1 ≤ Real.log (Real.log N))
    (by exact_mod_cast hB) hwidth
  unfold rate errorConstant
  have hnonneg : 0 ≤ Real.log N / Real.log (Real.log N) := by positivity
  nlinarith

theorem card_product_bound {K : ℝ} (hK : 0 ≤ K) {N B : ℕ} (hN : 3 ≤ N) (hB : 0 < B)
    (hwidth : (B : ℝ) ≤ upperScale * Real.log N)
    (hh : 4096 ≤ Real.log (Real.log N))
    (hlogA : Real.log (coefficient K) ≤ Real.log (Real.log N))
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ budget (coefficient K) (Real.log N)) :
    (B : ℝ) * (naturalValues P (3 * N)).card ≤ exceptionEnvelope K N := by
  have hcount : (0 : ℝ) < (naturalValues P (3 * N)).card := by
    have h := card_values_pos P ((3 * N : ℕ) : ℝ) (by exact_mod_cast (show 1 ≤ 3 * N by omega))
    simpa only [values, Nat.floor_natCast, Nat.cast_pos] using h
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have h := log_product_bound hK hN hB hwidth hh hlogA P hP hbudget
  rw [← Real.log_mul hBpos.ne' hcount.ne'] at h
  have hexp := Real.exp_le_exp.mpr h
  simpa only [Real.exp_log (mul_pos hBpos hcount), exceptionEnvelope] using hexp

end PaperP1.CriticalBranchingBudget
