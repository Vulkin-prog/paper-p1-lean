module

public import PaperP1.Asymptotics.GrowingDegreePrimeBudget

/-! # Logarithmic resultant errors in growing-degree prime budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GrowingDegreePrimeError

open Filter

theorem polylog_error_budget (E ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      E * (Real.log (Real.log N)) ^ 3 ≤ ε * Real.log (Real.log N) * Real.log N := by
  have hsmall : Tendsto (fun N : ℕ ↦ (Real.log (Real.log N)) ^ 2 / Real.log N)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
        PaperP1.PrimeLogBudget.log_nat_tendsto_atTop)
  have hlim : Tendsto (fun N : ℕ ↦ E * (Real.log (Real.log N)) ^ 2 / Real.log N)
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using hsmall.const_mul E
  have hevent : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 0 ≤ Real.log (Real.log N) ∧
      E * (Real.log (Real.log N)) ^ 2 / Real.log N < ε := by
    filter_upwards [eventually_ge_atTop 2,
      PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 0),
      (tendsto_order.mp hlim).2 ε hε] with N hN hll hb
    exact ⟨hN, hll, hb⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hNtwo, hll, hb⟩ := hN₀ N hN
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcross := (div_lt_iff₀ hl).mp hb
  have hmul := mul_le_mul_of_nonneg_right hcross.le hll
  nlinarith only [hmul]

theorem prime_card_of_log_height_with_error (c C E ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, 0 < n →
      Real.log n ≤ c * Real.log (Real.log N) * Real.log (C * N) +
        E * (Real.log (Real.log N)) ^ 3 →
      (n.primeFactors.card : ℝ) ≤ (c + ε) * Real.log N := by
  obtain ⟨Np, hNp⟩ := PaperP1.GrowingDegreePrimeBudget.prime_card_of_log_height
    (c + ε / 2) C (ε / 2) (by positivity) hC (by positivity)
  obtain ⟨Ne, hNe⟩ := polylog_error_budget E (ε / 2) (by positivity)
  have hevent : ∀ᶠ N : ℕ in atTop, 0 ≤ Real.log (Real.log N) :=
    PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 0)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 (max Np (max Ne Nl)), ?_⟩
  intro N hN n hn hheight
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hll := hNl N (by omega)
  have hCN : (N : ℝ) ≤ C * N := by nlinarith
  have hlogs := Real.log_le_log hNr hCN
  have he := hNe N (by omega)
  have he' : E * (Real.log (Real.log N)) ^ 3 ≤
      (ε / 2) * Real.log (Real.log N) * Real.log (C * N) :=
    he.trans (mul_le_mul_of_nonneg_left hlogs (by positivity))
  have hbudget : Real.log n ≤ (c + ε / 2) * Real.log (Real.log N) * Real.log (C * N) := by
    nlinarith only [hheight, he']
  have hp := hNp N (by omega) n hn hbudget
  have heq : c + ε / 2 + ε / 2 = c + ε := by ring
  rwa [heq] at hp

theorem exponential_budget_with_error (c C E ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C)
    (hε : 0 < ε) (a : ℝ) (ha : 1 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, 0 < n →
      Real.log n ≤ c * Real.log (Real.log N) * Real.log (C * N) +
        E * (Real.log (Real.log N)) ^ 3 →
      a ^ n.primeFactors.card ≤ (N : ℝ) ^ (c * Real.log a + ε) := by
  obtain ⟨N₀, hN₀⟩ := prime_card_of_log_height_with_error c C E (ε / Real.log a) hc hC
    (div_pos hε (Real.log_pos ha))
  refine ⟨max 2 N₀, ?_⟩
  intro N hN n hn hheight
  have hp := hN₀ N (by omega) n hn hheight
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogA := (Real.log_pos ha).le
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans ha), Real.rpow_def_of_pos hNr]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hp hlogA
  have heq : (c + ε / Real.log a) * Real.log a = c * Real.log a + ε := by
    rw [add_mul, div_mul_cancel₀ _ (Real.log_pos ha).ne']
  calc
    Real.log a * (n.primeFactors.card : ℝ) = (n.primeFactors.card : ℝ) * Real.log a := by ring
    _ ≤ ((c + ε / Real.log a) * Real.log N) * Real.log a := hmul
    _ = Real.log N * ((c + ε / Real.log a) * Real.log a) := by ring
    _ = _ := by rw [heq]

end PaperP1.GrowingDegreePrimeError
