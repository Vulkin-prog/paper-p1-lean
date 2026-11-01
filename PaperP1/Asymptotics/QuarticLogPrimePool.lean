module

public import PaperP1.Asymptotics.CriticalBranchingBudget

/-! # Prime-pool counts after a quadratic-logarithmic number of old windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuarticLogPrimePool

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget
  PaperP1.WindowPoolCount PaperP1.SmoothSquarefreeCount PaperP1.LogarithmicPrimeBudget
  PaperP1.CriticalBandScale PaperP1.CriticalBranchingBudget

def envelope (a : ℝ) (N : ℕ) : ℝ := (a * Real.log N) ^ 4

theorem fourth_power_rpow {u : ℝ} (hu : 0 < u) : (u ^ 4) ^ (1 - (3 / 4 : ℝ)) = u := by
  rw [Real.rpow_def_of_pos (pow_pos hu _), Real.log_pow]
  have heq : (4 : ℝ) * Real.log u * (1 / 4 : ℝ) = Real.log u := by ring
  norm_num only [Nat.cast_ofNat]
  rw [heq, Real.exp_log hu]

theorem self_le_fourth {u : ℝ} (hu : 1 ≤ u) : u ≤ u ^ 4 := by
  have hs : u ≤ u ^ 2 := by nlinarith
  have hs' : u ^ 2 ≤ u ^ 4 := by nlinarith [sq_nonneg (u ^ 2 - 1)]
  exact hs.trans hs'

theorem count_le_power_of_budget {a ε : ℝ} (ha : 1 ≤ a) (hε : 0 < ε)
    {N : ℕ} (hN : 3 ≤ N) (hlog : 2 ≤ Real.log N)
    (hlogY : 2 * budgetConstant * a / ε ≤ Real.log (envelope a N))
    (hthree : Real.log 3 ≤ ε / 2 * Real.log N) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ envelope a N) :
    ((naturalValues P (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hu : 2 ≤ a * Real.log N := by nlinarith
  have hY : 1 < envelope a N := by
    have hpow := self_le_fourth (by linarith : 1 ≤ a * Real.log N)
    unfold envelope
    linarith
  have hlogYpos := Real.log_pos hY
  have hcoef : budgetConstant * a / Real.log (envelope a N) ≤ ε / 2 := by
    apply (div_le_iff₀ hlogYpos).mpr
    have h := (div_le_iff₀ hε).mp hlogY
    nlinarith
  have hcost : budgetConstant * (envelope a N) ^ (1 - (3 / 4 : ℝ)) /
      Real.log (envelope a N) ≤ ε / 2 * Real.log N := by
    rw [envelope, fourth_power_rpow (by linarith : 0 < a * Real.log N)]
    have h := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ Real.log N)
    dsimp [envelope] at h
    convert h using 1
    ring
  have hcount := PrimeBudgetRankin.log_values_le P hP ((3 * N : ℕ) : ℝ)
    (by exact_mod_cast (show 1 ≤ 3 * N by omega)) (envelope a N) (3 / 4) hY (by norm_num) le_rfl hbudget
  simp only [values, Nat.floor_natCast] at hcount
  have hlogX : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  rw [hlogX] at hcount
  have hthree0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hfinal : Real.log ((naturalValues P (3 * N)).card : ℝ) ≤ (3 / 4 + ε) * Real.log N := by linarith
  have hpos : (0 : ℝ) < (naturalValues P (3 * N)).card := by
    have h := card_values_pos P ((3 * N : ℕ) : ℝ) (by exact_mod_cast (show 1 ≤ 3 * N by omega))
    simpa only [values, Nat.floor_natCast, Nat.cast_pos] using h
  calc
    _ = Real.exp (Real.log ((naturalValues P (3 * N)).card : ℝ)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp ((3 / 4 + ε) * Real.log N) := Real.exp_le_exp.mpr hfinal
    _ = _ := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

theorem count_le_power_eventually (a : ℝ) (ha : 1 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      (∑ p ∈ P, Real.log p) ≤ envelope a N →
        ((naturalValues P (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨N₀, hN₀⟩ := ElementaryLogGrowth.log_ge_eventually
    (max 2 (max (Real.exp (2 * budgetConstant * a / ε)) (2 * Real.log 3 / ε)))
  refine ⟨max N₀ 3, le_max_right _ _, ?_⟩
  intro N hN P hP hbudget
  have hlog := (hN₀ N (by omega)).1
  have hlog2 := (le_max_left _ _).trans hlog
  have hexp := (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
  have hthird := (le_max_right _ _).trans ((le_max_right _ _).trans hlog)
  have hYge : Real.log N ≤ envelope a N := by
    have hu : Real.log N ≤ a * Real.log N := by nlinarith
    exact hu.trans (self_le_fourth (by nlinarith : 1 ≤ a * Real.log N))
  have hlogY : 2 * budgetConstant * a / ε ≤ Real.log (envelope a N) := by
    have h := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at h
    exact h.trans (Real.log_le_log (by linarith) hYge)
  have hthree : Real.log 3 ≤ ε / 2 * Real.log N := by
    have h := (div_le_iff₀ hε).mp hthird
    nlinarith
  exact count_le_power_of_budget ha hε (by omega) hlog2 hlogY hthree P hP hbudget

theorem raw_budget_le_envelope {A : Finset ℕ} {N L j : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hN : 3 ≤ N) (hlog : 1 ≤ Real.log N) (hA : A ⊆ Model.dyadicBlock N) (hL : L ≤ N) (hj : A.card ≤ j)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (horder : (j : ℝ) ≤ K * (Real.log N) ^ 2) :
    (∑ p ∈ primePool (rawValues A L) (L + 1), Real.log p) ≤ envelope (coefficient K) N := by
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : 0 < Real.log N := by linarith
  have hD := upperScale_pos
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpow := self_le_fourth hlog
  have hthree : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 * N)
      (by nlinarith : 3 * (N : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using h
  have hsmall : ((L + 1 : ℕ) : ℝ) * Real.log 4 ≤ upperScale * Real.log 4 * (Real.log N) ^ 4 := by
    calc
      _ ≤ (upperScale * Real.log N) * Real.log 4 := mul_le_mul_of_nonneg_right hwidth hfour
      _ = (upperScale * Real.log 4) * Real.log N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hold : (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) ≤ (2 * K * upperScale) * (Real.log N) ^ 4 := by
    calc
      _ ≤ (K * (Real.log N) ^ 2) * (upperScale * Real.log N) * (2 * Real.log N) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul (mul_le_mul horder hwidth (by positivity) (by positivity)) hthree
            (Real.log_natCast_nonneg _) (by positivity)
      _ = _ := by ring
  have hraw := raw_primePool_log_sum_le hA (by omega) hL hj
  have hA1 := coefficient_ge_one hK
  have hA4 := self_le_fourth hA1
  calc
    _ ≤ (upperScale * Real.log 4 + 2 * K * upperScale) * (Real.log N) ^ 4 := by nlinarith
    _ ≤ coefficient K * (Real.log N) ^ 4 := by unfold coefficient; nlinarith [pow_nonneg hH.le 4]
    _ ≤ (coefficient K) ^ 4 * (Real.log N) ^ 4 := mul_le_mul_of_nonneg_right hA4 (pow_nonneg hH.le _)
    _ = _ := by unfold envelope; ring

theorem actual_pool_count_critical (C K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ j : ℕ, (j : ℝ) ≤ K * (Real.log N) ^ 2 →
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ Model.dyadicBlock N → A.card ≤ j →
        ((poolValues (rawValues A L) (L + 1) (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Ncount, hNcount, hcount⟩ := count_le_power_eventually (coefficient K) (coefficient_ge_one hK) ε hε
  obtain ⟨Nwidth, hwidth⟩ := critical_band_scale C
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually 1
  refine ⟨max Ncount (max Nwidth (max Nfinite Nlog)), by omega, ?_⟩
  intro N hN j horder L hband A hA hj
  obtain ⟨hN3, _, hLN⟩ := hfinite N (by omega) L hband
  exact hcount N (by omega) _ (fun p hp ↦ primePool_prime _ _ _ hp)
    (raw_budget_le_envelope hK hN3 (hlog N (by omega)).1 hA hLN hj (hwidth N (by omega) L hband).2 horder)

end PaperP1.QuarticLogPrimePool
