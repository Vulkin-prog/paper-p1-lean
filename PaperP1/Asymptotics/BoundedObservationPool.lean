module

public import PaperP1.Asymptotics.LogSquaredPrimePool

/-! # Prime pools for arbitrary bounded old observations and logarithmic diameters -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedObservationPool

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget
  PaperP1.WindowPoolCount PaperP1.SmoothSquarefreeCount PaperP1.LogSquaredPrimePool

def widthEnvelope (D : ℝ) (j : ℕ) : ℝ := 2 * (j + 1) * (D + 1)

theorem widthEnvelope_ge_one {D : ℝ} (hD : 0 ≤ D) (j : ℕ) : 1 ≤ widthEnvelope D j := by
  unfold widthEnvelope
  have hj := Nat.cast_nonneg (α := ℝ) j
  nlinarith

theorem pool_budget_le_envelope {R : Finset ℕ} {N B j : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hN : 3 ≤ N) (hR : ∀ n ∈ R, 1 ≤ n ∧ n ≤ 3 * N) (hcard : R.card ≤ j * B)
    (hwidth : (B : ℝ) ≤ D * Real.log N) :
    (∑ p ∈ primePool R B, Real.log p) ≤ envelope (widthEnvelope D j) N := by
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hfour : Real.log 4 ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by nlinarith : (4 : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hthree : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 * N) (by nlinarith : 3 * (N : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using h
  have hraw := primePool_log_sum_le R B (3 * N) hR
  have hcardR : (R.card : ℝ) ≤ (j : ℝ) * B := by exact_mod_cast hcard
  have hcardLog := mul_le_mul_of_nonneg_right hcardR (Real.log_natCast_nonneg (3 * N))
  have hsmall := mul_le_mul_of_nonneg_left hfour (Nat.cast_nonneg B)
  have hold := mul_le_mul_of_nonneg_left hthree (by positivity : (0 : ℝ) ≤ (j : ℝ) * B)
  have hwidthMul := mul_le_mul_of_nonneg_right hwidth (by positivity : (0 : ℝ) ≤ 2 * (j + 1) * Real.log N)
  have hcoeff : 2 * (j + 1 : ℝ) * D ≤ (widthEnvelope D j) ^ 2 := by
    have h := widthEnvelope_ge_one hD j
    unfold widthEnvelope at *
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (Real.log N))
  unfold envelope
  push_cast at hraw hcardLog hold
  nlinarith

theorem pool_count_logarithmic (D : ℝ) (hD : 0 ≤ D) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, (B : ℝ) ≤ D * Real.log N →
      ∀ R : Finset ℕ, (∀ n ∈ R, 1 ≤ n ∧ n ≤ 3 * N) → R.card ≤ j * B →
        ((poolValues R B (3 * N)).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨N₀, hN₀, hcount⟩ := count_le_power_eventually (widthEnvelope D j) (widthEnvelope_ge_one hD j) ε hε
  exact ⟨N₀, hN₀, fun N hN B hwidth R hR hcard ↦
    hcount N hN _ (fun p hp ↦ primePool_prime _ _ _ hp)
      (pool_budget_le_envelope hD (by omega) hR hcard hwidth)⟩

end PaperP1.BoundedObservationPool
