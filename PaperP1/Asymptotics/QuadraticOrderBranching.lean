module

public import PaperP1.Asymptotics.QuarticLogPrimePool

/-! # Exact full-vector branching through a quadratic logarithmic order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticOrderBranching

open Finset PaperP1.Model PaperP1.OldValuePrimeBudget PaperP1.BranchingExceptional
  PaperP1.FixedWindowBranching PaperP1.CriticalBandScale PaperP1.WindowPoolCount

theorem badStarts_card_critical (C K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ j : ℕ, (j : ℝ) ≤ K * (Real.log N) ^ 2 →
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        ((badStarts N L (rawValues A L)).card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Npool, hNpool, hpool⟩ := QuarticLogPrimePool.actual_pool_count_critical C K (ε / 2) hK (by linarith)
  obtain ⟨Nwidth, hwidth⟩ := critical_band_scale C
  obtain ⟨NB, hB⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 1 (ε / 2) (by linarith)
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  refine ⟨max Npool (max Nwidth (max NB Nfinite)), by omega, ?_⟩
  intro N hN j horder L hband A hA hj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hN3, _, hLN⟩ := hfinite N (by omega) L hband
  have hwidthN := (hwidth N (by omega) L hband).2
  have hBN : ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_mul, pow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hB N (by omega) L hwidthN
  have hpoolN := hpool N (by omega) j horder L hband A hA hj
  have hhalf := badStarts_card_half (rawValues A L) (by omega) hLN
  have hcoarse : ((badStarts N L (rawValues A L)).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := by
    have hnonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := by positivity
    nlinarith
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := hcoarse
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (3 / 4 + ε / 2) :=
      mul_le_mul hBN hpoolN (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

theorem quadratic_order_branching (C K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ j : ℕ, (j : ℝ) ≤ K * (Real.log N) ^ 2 →
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ (E.card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) ∧
          IndependentConclusion N L A E := by
  obtain ⟨N₀, hN₀, hbound⟩ := badStarts_card_critical C K ε hK hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN j horder L hband A hA hj
  exact ⟨badStarts N L (rawValues A L), badStarts_subset _ _ _,
    hbound N hN j horder L hband A hA hj, retained_independent (by omega) hA⟩

end PaperP1.QuadraticOrderBranching
