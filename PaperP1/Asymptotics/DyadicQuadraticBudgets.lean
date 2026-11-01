module

public import PaperP1.Asymptotics.ShiftedQuadraticKernelCount
public import PaperP1.Asymptotics.ActualPrescribedDivisorBudget

/-! # Actual dyadic quadratic-kernel ranges and subpolynomial index budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicQuadraticBudgets

open Finset PaperP1.SplitOffsetProducts

def indices (N : ℕ) : Finset ℕ := range (Nat.log2 (N ^ 6) + 1)
def exponent (N j : ℕ) : ℝ := Real.log ((2 : ℝ) ^ j) / Real.log N

theorem dyadic_bounds (q : ℕ) (hq : 0 < q) :
    2 ^ Nat.log2 q ≤ q ∧ q < 2 * 2 ^ Nat.log2 q := by
  refine ⟨Nat.log2_self_le hq.ne', ?_⟩
  simpa only [Nat.pow_succ, Nat.mul_comm] using (Nat.lt_log2_self (n := q))

theorem mem_indices (N q : ℕ) (hN : 0 < N) (hq : 0 < q) (hheight : q ≤ N ^ 6) :
    Nat.log2 q ∈ indices N := by
  apply mem_range.mpr
  have hle : Nat.log2 q ≤ Nat.log2 (N ^ 6) :=
    (Nat.le_log2 (pow_ne_zero _ hN.ne')).mpr ((Nat.log2_self_le hq.ne').trans hheight)
  omega

theorem exponent_identity (N j : ℕ) (hN : 2 ≤ N) : (N : ℝ) ^ exponent N j = (2 : ℝ) ^ j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (N : ℝ) ≠ 1 := ne_of_gt (by exact_mod_cast (show 1 < N by omega))
  exact Real.rpow_logb hn hn1 (by positivity)

theorem real_window (N q j : ℕ) (hN : 2 ≤ N) (hq : 0 < q) (hj : Nat.log2 q = j) :
    (N : ℝ) ^ exponent N j ≤ q ∧ (q : ℝ) < 2 * (N : ℝ) ^ exponent N j ∧
      exponent N j ≤ Real.log q / Real.log N := by
  obtain ⟨hl, hu⟩ := dyadic_bounds q hq
  rw [hj] at hl hu
  have hlR : (2 : ℝ) ^ j ≤ q := by exact_mod_cast hl
  have huR : (q : ℝ) < 2 * (2 : ℝ) ^ j := by exact_mod_cast hu
  rw [exponent_identity N j hN]
  refine ⟨hlR, huR, ?_⟩
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ j) hlR
  exact div_le_div_of_nonneg_right hlog (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le

theorem block_kernel_height (N n W : ℕ) (B : Finset ℤ) (hN : 2 ≤ N) (hW : 2 * W ≤ N)
    (hnlo : N ≤ n) (hnhi : n ≤ 2 * N) (hB : B.card = 2) (hA : ∀ a ∈ B, a.natAbs ≤ W) :
    kernel B n ≤ N ^ 6 := by
  have hWn : W < n := by omega
  have hq := (kernel_le B n (product_pos B n W hWn hA)).trans
    (product_le_pow B N n W hnhi (by omega) hA)
  rw [hB] at hq
  have hfour : 9 ≤ N ^ 4 := (by norm_num : 9 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4)
  calc
    _ ≤ (3 * N) ^ 2 := hq
    _ = 9 * N ^ 2 := by ring
    _ ≤ N ^ 4 * N ^ 2 := Nat.mul_le_mul_right _ hfour
    _ = N ^ 6 := by rw [← pow_add]

theorem indices_card_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((indices N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nc, hNc⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow
    (6 / Real.log 2 + 1) 1 ε hε
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max 2 (max Nc Nl), ?_⟩
  intro N hN
  have hn : 0 < N := by omega
  have hlN := hNl N (by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpR : (2 : ℝ) ^ Nat.log2 (N ^ 6) ≤ (N : ℝ) ^ 6 := by
    exact_mod_cast Nat.log2_self_le (pow_ne_zero 6 hn.ne')
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 (N ^ 6)) hpR
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  have hdiv : (Nat.log2 (N ^ 6) : ℝ) ≤ 6 * Real.log N / Real.log 2 :=
    (le_div_iff₀ hl2).mpr hlog
  have hc := hNc N (by omega)
  rw [Real.rpow_one] at hc
  simp only [indices, card_range, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ 6 * Real.log N / Real.log 2 + Real.log N := add_le_add hdiv hlN
    _ = (6 / Real.log 2 + 1) * Real.log N := by ring
    _ ≤ _ := hc

theorem logarithmic_card_budget (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      (m : ℝ) ≤ c * Real.log (Real.log N) → (m : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nc, hNc⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow c 1 ε hε
  refine ⟨max 2 Nc, ?_⟩
  intro N hN m hm
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll : Real.log (Real.log N) ≤ Real.log N :=
    (Real.log_le_sub_one_of_pos hl).trans (by linarith)
  have hcN := hNc N (by omega)
  rw [Real.rpow_one] at hcN
  exact (hm.trans (mul_le_mul_of_nonneg_left hll hc)).trans hcN

end PaperP1.DyadicQuadraticBudgets
