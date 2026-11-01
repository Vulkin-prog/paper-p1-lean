module

public import PaperP1.Arithmetic.TwoProgressionPrimeRows
public import PaperP1.Arithmetic.CoverRankPrimeBudget
public import PaperP1.Arithmetic.PrimeLogBudget

/-! # The omitted prime rows of polynomial-height dilation coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeFactorBudget

open Finset Filter PaperP1.Arithmetic PaperP1.TwoProgressionPrimeRows

theorem two_pow_card_le {n : ℕ} (hn : 0 < n) : 2 ^ n.primeFactors.card ≤ n := by
  calc
    _ = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p :=
      prod_le_prod (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem card_log_le {n : ℕ} (hn : 0 < n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have hpow : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast two_pow_card_le hn
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n.primeFactors.card) hpow
  simpa only [Real.log_pow] using hlog

theorem polynomial_card_log_le {n B d : ℕ} (hn : 0 < n) (hheight : n ≤ B ^ d) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ (d : ℝ) * Real.log B := by
  have hheightR : (n : ℝ) ≤ (B : ℝ) ^ d := by exact_mod_cast hheight
  have hlog := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n) hheightR
  rw [Real.log_pow] at hlog
  exact (card_log_le hn).trans hlog

theorem polynomial_card_budget (d : ℕ) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ n : ℕ, 0 < n → n ≤ B ^ d →
      (n.primeFactors.card : ℝ) ≤ B / Real.log B := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun B : ℕ ↦ (Real.log B) ^ 2 / B) atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevent : ∀ᶠ B : ℕ in atTop, (Real.log B) ^ 2 / B < Real.log 2 / ((d : ℝ) + 1) :=
    (tendsto_order.1 hlim).2 _ (by positivity)
  obtain ⟨Bcore, hcore⟩ := eventually_atTop.1 hevent
  refine ⟨max Bcore 4, ?_⟩
  intro B hB n hn hheight
  have hBfour : 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hsmall := (div_lt_div_iff₀ hBpos (by positivity : 0 < (d : ℝ) + 1)).mp
    (hcore B ((le_max_left _ _).trans hB))
  have hpoly := mul_le_mul_of_nonneg_right (polynomial_card_log_le hn hheight) hlogB.le
  apply (le_div_iff₀ hlogB).mpr
  nlinarith [sq_nonneg (Real.log B)]

theorem exceptional_budget (d : ℕ) (C₀ : ℝ) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ H a b : ℕ,
      B ≤ H → (H : ℝ) ≤ C₀ * B → 0 < a → 0 < b → a * b ≤ B ^ d →
      ((exceptionalPrimes H a b).card : ℝ) + 1 ≤
        (CoverRankPrimeBudget.constant C₀ + 1) * B / Real.log B := by
  obtain ⟨Bcore, hcore⟩ := polynomial_card_budget d
  refine ⟨max Bcore 4, ?_⟩
  intro B hB H a b hBH hH ha hb hheight
  have hBfour : 4 ≤ B := (le_max_right _ _).trans hB
  have hprime := CoverRankPrimeBudget.finite_budget hBfour hBH hH
  have hfactor := hcore B ((le_max_left _ _).trans hB) (a * b) (Nat.mul_pos ha hb) hheight
  have hcard : ((exceptionalPrimes H a b).card : ℝ) ≤
      (LocalDefectBound.primeCount H : ℝ) + (a * b).primeFactors.card := by
    exact_mod_cast exceptional_card H a b
  have hnonneg : (0 : ℝ) ≤ LocalDefectBound.primeCount H := Nat.cast_nonneg _
  have hprime' : (LocalDefectBound.primeCount H : ℝ) + 2 ≤
      CoverRankPrimeBudget.constant C₀ * B / Real.log B := by linarith
  calc
    _ ≤ (LocalDefectBound.primeCount H : ℝ) + (a * b).primeFactors.card + 1 := by linarith
    _ ≤ CoverRankPrimeBudget.constant C₀ * B / Real.log B + B / Real.log B := by linarith
    _ = _ := by ring

end PaperP1.PrimeFactorBudget
