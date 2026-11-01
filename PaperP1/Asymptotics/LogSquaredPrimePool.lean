module

public import PaperP1.Arithmetic.PrimeBudgetRankin
public import PaperP1.Arithmetic.OldValuePrimeBudget
public import PaperP1.Arithmetic.WindowPoolCount
public import PaperP1.Analysis.ElementaryLogGrowth
public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Square-root-plus-epsilon counts for the actual old-window prime pools -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogSquaredPrimePool

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget
  PaperP1.WindowPoolCount PaperP1.SmoothSquarefreeCount PaperP1.LogarithmicPrimeBudget
  PaperP1.CriticalBandScale

def envelope (a : ℝ) (N : ℕ) : ℝ := (a * Real.log N) ^ 2

theorem count_le_power_of_budget {a ε : ℝ} (ha : 1 ≤ a) (hε : 0 < ε)
    {N : ℕ} (hN : 3 ≤ N) (hlog : 2 ≤ Real.log N)
    (hlogY : 2 * budgetConstant * a / ε ≤ Real.log (envelope a N))
    (hthree : Real.log 3 ≤ ε * Real.log N) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ envelope a N) :
    ((naturalValues P (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have haLog : 0 ≤ a * Real.log N := mul_nonneg (by linarith) (by linarith)
  have haLog2 : 2 ≤ a * Real.log N := by nlinarith
  have hY : 1 < envelope a N := by unfold envelope; nlinarith
  have hlogYpos : 0 < Real.log (envelope a N) := Real.log_pos hY
  have hcoef : budgetConstant * a / Real.log (envelope a N) ≤ ε / 2 := by
    apply (div_le_iff₀ hlogYpos).mpr
    have h := (div_le_iff₀ hε).mp hlogY
    nlinarith
  have hcost : budgetConstant * (envelope a N) ^ (1 - (1 / 2 : ℝ)) /
      Real.log (envelope a N) ≤ ε / 2 * Real.log N := by
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    rw [← Real.sqrt_eq_rpow, envelope, Real.sqrt_sq_eq_abs, abs_of_nonneg haLog]
    have h := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ Real.log N)
    dsimp [envelope] at h
    convert h using 1; ring
  have hX : (1 : ℝ) ≤ (3 * N : ℕ) := by exact_mod_cast (show 1 ≤ 3 * N by omega)
  have hbound : Real.log ((naturalValues P (3 * N)).card : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (3 * N : ℕ) +
        budgetConstant * (envelope a N) ^ (1 - (1 / 2 : ℝ)) / Real.log (envelope a N) := by
    simpa only [values, Nat.floor_natCast] using
      PrimeBudgetRankin.log_values_le P hP ((3 * N : ℕ) : ℝ) hX (envelope a N) (1 / 2)
        hY (by norm_num) (by norm_num) hbudget
  have hlogX : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  rw [hlogX] at hbound
  have hfinal : Real.log ((naturalValues P (3 * N)).card : ℝ) ≤ (1 / 2 + ε) * Real.log N := by linarith
  have hcount : (0 : ℝ) < (naturalValues P (3 * N)).card := by
    have h := card_values_pos P ((3 * N : ℕ) : ℝ) hX
    simpa only [values, Nat.floor_natCast, Nat.cast_pos] using h
  calc
    _ = Real.exp (Real.log ((naturalValues P (3 * N)).card : ℝ)) := (Real.exp_log hcount).symm
    _ ≤ Real.exp ((1 / 2 + ε) * Real.log N) := Real.exp_le_exp.mpr hfinal
    _ = _ := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

theorem count_le_power_eventually (a : ℝ) (ha : 1 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      (∑ p ∈ P, Real.log p) ≤ envelope a N →
        ((naturalValues P (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := ElementaryLogGrowth.log_ge_eventually
    (max 2 (max (Real.exp (2 * budgetConstant * a / ε)) (Real.log 3 / ε)))
  refine ⟨max N₀ 3, le_max_right _ _, fun N hN P hP hbudget ↦ ?_⟩
  obtain ⟨hlog, _⟩ := hN₀ N (by omega)
  have hlog2 : 2 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hexp : Real.exp (2 * budgetConstant * a / ε) ≤ Real.log N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
  have hthird : Real.log 3 / ε ≤ Real.log N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlog)
  have hlogY : 2 * budgetConstant * a / ε ≤ Real.log (envelope a N) := by
    have hbase := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at hbase
    have haLog : Real.log N ≤ a * Real.log N := by nlinarith
    have hYge : Real.log N ≤ envelope a N := by unfold envelope; nlinarith
    exact hbase.trans (Real.log_le_log (by linarith) hYge)
  exact count_le_power_of_budget ha hε (by omega) hlog2 hlogY
    (by have h := (div_le_iff₀ hε).mp hthird; nlinarith) P hP hbudget

def windowEnvelope (j : ℕ) : ℝ := 2 * (j + 1) * (upperScale + 1)

theorem windowEnvelope_ge_one (j : ℕ) : 1 ≤ windowEnvelope j := by
  unfold windowEnvelope
  have h := upperScale_pos
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem raw_budget_le_envelope {A : Finset ℕ} {N L j : ℕ} (hA : A ⊆ Model.dyadicBlock N)
    (hN : 3 ≤ N) (hL : L ≤ N) (hj : A.card ≤ j)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N) :
    (∑ p ∈ primePool (rawValues A L) (L + 1), Real.log p) ≤ envelope (windowEnvelope j) N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hfour : Real.log 4 ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by nlinarith : (4 : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hthree : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 * N) (by nlinarith : 3 * (N : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using h
  have hraw := raw_primePool_log_sum_le hA (by omega) hL hj
  have hsmall := mul_le_mul_of_nonneg_left hfour (Nat.cast_nonneg (L + 1))
  have hold := mul_le_mul_of_nonneg_left hthree (by positivity : (0 : ℝ) ≤ (j : ℝ) * (L + 1))
  have hwidthMul := mul_le_mul_of_nonneg_right hwidth (by positivity : (0 : ℝ) ≤ 2 * (j + 1) * Real.log N)
  have hcoeff : 2 * (j + 1 : ℝ) * upperScale ≤ (windowEnvelope j) ^ 2 := by
    have h := windowEnvelope_ge_one j
    unfold windowEnvelope at *
    have hu := upperScale_pos
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (Real.log N))
  unfold envelope
  push_cast at hraw hsmall hold hwidthMul
  nlinarith

theorem actual_pool_count_critical (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ Model.dyadicBlock N → A.card ≤ j →
        ((poolValues (rawValues A L) (L + 1) (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨Ncount, hNcount, hcount⟩ := count_le_power_eventually (windowEnvelope j) (windowEnvelope_ge_one j) ε hε
  obtain ⟨Nwidth, hwidth⟩ := critical_band_scale C
  obtain ⟨Nlength, hlength⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 1 1 (by norm_num)
  refine ⟨max Ncount (max Nwidth Nlength), by omega, ?_⟩
  intro N hN L hband A hA hj
  have hB := (hwidth N (by omega) L hband).2
  have hlen := hlength N (by omega) L hB
  have hLN : L ≤ N := by
    have hreal : (L + 1 : ℝ) ≤ N := by simpa only [one_mul, pow_one, Real.rpow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hlen
    have hnat : L + 1 ≤ N := by exact_mod_cast hreal
    omega
  exact hcount N (by omega) _ (fun p hp ↦ primePool_prime _ _ _ hp)
    (raw_budget_le_envelope hA (by omega) hLN hj hB)

end PaperP1.LogSquaredPrimePool
