module

public import PaperP1.Arithmetic.SplitOffsetProducts
public import PaperP1.Asymptotics.GrowingDegreePrimeError
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Derived prime-support budgets for the actual q*D_A at growing degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitOffsetHeightBudget

open Finset Filter PaperP1.SplitOffsetProducts

def errorConstant (c D A₀ : ℝ) : ℝ := c ^ 2 * (Real.log (2 * D) + A₀)

theorem width_log_bound (D A₀ : ℝ) (hD : 1 ≤ D) (N W : ℕ) (hN : 2 ≤ N)
    (hW : 0 < W) (hll : 1 ≤ Real.log (Real.log N))
    (hwidth : (W : ℝ) ≤ D * (Real.log N) ^ A₀) :
    Real.log (2 * W : ℝ) ≤ (Real.log (2 * D) + A₀) * Real.log (Real.log N) := by
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hDp : 0 < D := by linarith
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hlogD : 0 ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
  have hb : (2 : ℝ) * W ≤ (2 * D) * (Real.log N) ^ A₀ := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * W) hb
  rw [Real.log_mul (by positivity : (2 * D : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hl A₀).ne', Real.log_rpow hl] at hlog
  nlinarith

theorem actual_log_height (c D A₀ : ℝ) (hD : 1 ≤ D)
    (N n W : ℕ) (A : Finset ℤ) (hN : 2 ≤ N) (hW : 0 < W)
    (hWN : 2 * W ≤ N) (hnlo : N ≤ n) (hnhi : n ≤ 2 * N)
    (hll : 1 ≤ Real.log (Real.log N)) (hwidth : (W : ℝ) ≤ D * (Real.log N) ^ A₀)
    (hdegree : (A.card : ℝ) ≤ c * Real.log (Real.log N))
    (hA : ∀ a ∈ A, a.natAbs ≤ W) :
    Real.log (kernel A n * resultant A) ≤
      c * Real.log (Real.log N) * Real.log (3 * N) +
        errorConstant c D A₀ * (Real.log (Real.log N)) ^ 3 := by
  have hbase := kernel_resultant_log_height A N n W (by omega) hW (by omega) hnhi (by omega) hA
  have hwlog := width_log_bound D A₀ hD N W hN hW hll hwidth
  have hlogW : 0 ≤ Real.log (2 * W : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * W by omega))
  have hlogN : 0 ≤ Real.log (3 * N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * N by omega))
  have hsq : (A.card : ℝ) ^ 2 ≤ (c * Real.log (Real.log N)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hdegree 2
  have hmain := mul_le_mul_of_nonneg_right hdegree hlogN
  have herror := mul_le_mul hsq hwlog hlogW (sq_nonneg _)
  unfold errorConstant
  nlinarith only [hbase, hmain, herror]

theorem eventual_log_height (c D A₀ : ℝ) (hD : 1 ≤ D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W : ℕ, ∀ A : Finset ℤ,
      0 < W → N ≤ n → n ≤ 2 * N → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      Real.log (kernel A n * resultant A) ≤
        c * Real.log (Real.log N) * Real.log (3 * N) +
          errorConstant c D A₀ * (Real.log (Real.log N)) ^ 3 := by
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D) A₀ 1 (by norm_num)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨max 2 (max Nw Nl), ?_⟩
  intro N hN n W A hW hnlo hnhi hwidth hdegree hA
  have hWNr : (2 * W : ℝ) ≤ N := by
    have hb := hNw N (by omega)
    rw [Real.rpow_one] at hb
    nlinarith
  have hWN : 2 * W ≤ N := by exact_mod_cast hWNr
  exact actual_log_height c D A₀ hD N n W A (by omega) hW hWN hnlo hnhi
    (hNl N (by omega)) hwidth hdegree hA

theorem actual_prime_support_budget (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W : ℕ, ∀ A : Finset ℤ,
      0 < W → N ≤ n → n ≤ 2 * N → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ((kernel A n * resultant A).primeFactors.card : ℝ) ≤ (c + ε) * Real.log N := by
  obtain ⟨Nh, hNh⟩ := eventual_log_height c D A₀ hD
  obtain ⟨Np, hNp⟩ := PaperP1.GrowingDegreePrimeError.prime_card_of_log_height_with_error
    c 3 (errorConstant c D A₀) ε hc (by norm_num) hε
  refine ⟨max Nh Np, ?_⟩
  intro N hN n W A hW hnlo hnhi hwidth hdegree hA
  apply hNp N (by omega) (kernel A n * resultant A) (Nat.mul_pos (kernel_pos A n) (resultant_pos A))
  push_cast
  exact hNh N (by omega) n W A hW hnlo hnhi hwidth hdegree hA

theorem actual_exponential_budget (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hε : 0 < ε) (a : ℝ) (ha : 1 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W : ℕ, ∀ A : Finset ℤ,
      0 < W → N ≤ n → n ≤ 2 * N → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ b ∈ A, b.natAbs ≤ W) →
      a ^ (kernel A n * resultant A).primeFactors.card ≤ (N : ℝ) ^ (c * Real.log a + ε) := by
  obtain ⟨Nh, hNh⟩ := eventual_log_height c D A₀ hD
  obtain ⟨Np, hNp⟩ := PaperP1.GrowingDegreePrimeError.exponential_budget_with_error
    c 3 (errorConstant c D A₀) ε hc (by norm_num) hε a ha
  refine ⟨max Nh Np, ?_⟩
  intro N hN n W A hW hnlo hnhi hwidth hdegree hA
  apply hNp N (by omega) (kernel A n * resultant A) (Nat.mul_pos (kernel_pos A n) (resultant_pos A))
  push_cast
  exact hNh N (by omega) n W A hW hnlo hnhi hwidth hdegree hA

end PaperP1.SplitOffsetHeightBudget
