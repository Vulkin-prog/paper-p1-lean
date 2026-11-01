module

public import PaperP1.Arithmetic.PrimeFactorialBudget
public import PaperP1.Asymptotics.ModerateOrder
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Uniform prime-support budgets at degree O(log log N) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GrowingDegreePrimeBudget

open Filter

theorem trial_log_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ (Real.log (a * Real.log N) - 1) / Real.log (Real.log N))
      atTop (nhds 1) := by
  have hinv := tendsto_inv_atTop_zero.comp PaperP1.ModerateOrder.loglog_tendsto_atTop
  have hlim : Tendsto (fun N : ℕ ↦ (Real.log a - 1) * (Real.log (Real.log N))⁻¹ + 1)
      atTop (nhds ((Real.log a - 1) * 0 + 1)) :=
    (hinv.const_mul (Real.log a - 1)).add tendsto_const_nhds
  have heq : (fun N : ℕ ↦ (Real.log (a * Real.log N) - 1) / Real.log (Real.log N)) =ᶠ[atTop]
      (fun N : ℕ ↦ (Real.log a - 1) * (Real.log (Real.log N))⁻¹ + 1) := by
    filter_upwards [eventually_ge_atTop 2,
      PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hN hll
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hllpos : 0 < Real.log (Real.log N) := by linarith
    rw [Real.log_mul ha.ne' hl.ne']
    field_simp
    ring
  exact Tendsto.congr' heq.symm (by simpa only [mul_zero, zero_add] using hlim)

theorem prime_card_of_log_height (c C ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, 0 < n →
      Real.log n ≤ c * Real.log (Real.log N) * Real.log (C * N) →
      (n.primeFactors.card : ℝ) ≤ (c + ε) * Real.log N := by
  have ha : 0 < c + ε := by positivity
  have htrial := trial_log_ratio (c + ε) ha
  have hbase := PaperP1.PrimeLogBudget.log_mul_div_log_tendsto C (by positivity)
  have hmargin : Tendsto (fun N : ℕ ↦
      (c + ε) * ((Real.log ((c + ε) * Real.log N) - 1) / Real.log (Real.log N)) -
        c * (Real.log (C * N) / Real.log N)) atTop (nhds ε) := by
    have hlim := (htrial.const_mul (c + ε)).sub (hbase.const_mul c)
    simpa only [mul_one, add_sub_cancel_left] using hlim
  have htrialTop : Tendsto (fun N : ℕ ↦ Real.log ((c + ε) * Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.const_mul_atTop ha)
  have hevent : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 1 ≤ Real.log (Real.log N) ∧
      1 ≤ Real.log ((c + ε) * Real.log N) ∧
      c * Real.log (C * N) / Real.log N <
        (c + ε) * (Real.log ((c + ε) * Real.log N) - 1) / Real.log (Real.log N) := by
    filter_upwards [eventually_ge_atTop 2,
      PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 1),
      htrialTop.eventually (eventually_ge_atTop 1),
      (tendsto_order.mp hmargin).1 0 hε] with N hN hll hlt hm
    refine ⟨hN, hll, hlt, ?_⟩
    simp only [mul_div_assoc] at hm ⊢
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, ?_⟩
  intro N hN n hn hheight
  obtain ⟨hNtwo, hll, hlt, hmarginN⟩ := hN₀ N hN
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hllpos : 0 < Real.log (Real.log N) := by linarith
  have hcross := (div_lt_div_iff₀ hl hllpos).mp hmarginN
  have hbudget : Real.log n <
      ((c + ε) * Real.log N) * (Real.log ((c + ε) * Real.log N) - 1) := by
    nlinarith only [hheight, hcross]
  exact (PaperP1.PrimeFactorialBudget.prime_card_lt_of_log_budget n hn
    ((c + ε) * Real.log N) (mul_pos ha hl) hlt hbudget).le

theorem growing_degree_prime_card (c C ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n d : ℕ, 0 < n →
      (d : ℝ) ≤ c * Real.log (Real.log N) → (n : ℝ) ≤ (C * N) ^ d →
      (n.primeFactors.card : ℝ) ≤ (c + ε) * Real.log N := by
  obtain ⟨N₀, hN₀⟩ := prime_card_of_log_height c C ε hc hC hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN n d hn hd hheight
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hCN : 1 ≤ C * (N : ℝ) := by
    calc
      1 ≤ C := hC
      _ = C * 1 := (mul_one C).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hN1 (by linarith)
  have hlog := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n) hheight
  rw [Real.log_pow] at hlog
  apply hN₀ N (by omega) n hn
  exact hlog.trans (mul_le_mul_of_nonneg_right hd (Real.log_nonneg hCN))

theorem exponential_prime_budget (c C ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C) (hε : 0 < ε)
    (a : ℝ) (ha : 1 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n d : ℕ, 0 < n →
      (d : ℝ) ≤ c * Real.log (Real.log N) → (n : ℝ) ≤ (C * N) ^ d →
      a ^ n.primeFactors.card ≤ (N : ℝ) ^ ((c + ε) * Real.log a) := by
  obtain ⟨N₀, hN₀⟩ := growing_degree_prime_card c C ε hc hC hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN n d hn hd hheight
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hN₀ N (by omega) n d hn hd hheight
  have hlogA : 0 ≤ Real.log a := (Real.log_pos ha).le
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans ha), Real.rpow_def_of_pos hNr]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hcard hlogA]

theorem exponential_prime_budget_additive (c C ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C)
    (hε : 0 < ε) (a : ℝ) (ha : 1 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n d : ℕ, 0 < n →
      (d : ℝ) ≤ c * Real.log (Real.log N) → (n : ℝ) ≤ (C * N) ^ d →
      a ^ n.primeFactors.card ≤ (N : ℝ) ^ (c * Real.log a + ε) := by
  obtain ⟨N₀, hN₀⟩ := exponential_prime_budget c C (ε / Real.log a) hc hC
    (div_pos hε (Real.log_pos ha)) a ha
  refine ⟨N₀, ?_⟩
  intro N hN n d hn hd hheight
  have hb := hN₀ N hN n d hn hd hheight
  have heq : (c + ε / Real.log a) * Real.log a = c * Real.log a + ε := by
    rw [add_mul, div_mul_cancel₀ _ (Real.log_pos ha).ne']
  simpa only [heq] using hb

theorem squarefree_divisor_budget (c C ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n d : ℕ, Squarefree n →
      (d : ℝ) ≤ c * Real.log (Real.log N) → (n : ℝ) ≤ (C * N) ^ d →
      (n.divisors.card : ℝ) ≤ (N : ℝ) ^ (c * Real.log 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := exponential_prime_budget_additive c C ε hc hC hε 2 (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN n d hn hd hheight
  rw [PaperP1.PrimeFactorialBudget.squarefree_divisors_card n hn, Nat.cast_pow, Nat.cast_ofNat]
  exact hN₀ N hN n d (Nat.pos_of_ne_zero hn.ne_zero) hd hheight

theorem prime_colourings_budget (c C ε : ℝ) (hc : 0 ≤ c) (hC : 1 ≤ C) (hε : 0 < ε)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n d : ℕ, 0 < n →
      (d : ℝ) ≤ c * Real.log (Real.log N) → (n : ℝ) ≤ (C * N) ^ d →
      (Fintype.card (n.primeFactors → Fin k) : ℝ) ≤ (N : ℝ) ^ (c * Real.log k + ε) := by
  obtain ⟨N₀, hN₀⟩ := exponential_prime_budget_additive c C ε hc hC hε k
    (by exact_mod_cast (show 1 < k by omega))
  refine ⟨N₀, ?_⟩
  intro N hN n d hn hd hheight
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] using
    hN₀ N hN n d hn hd hheight

end PaperP1.GrowingDegreePrimeBudget
