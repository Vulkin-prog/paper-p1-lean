module

public import PaperP1.Asymptotics.CriticalBranchingBudget

/-! # Companion T22.4: exact independence at a growing critical order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalOrderBranching

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.ConditionalWindowRank
  PaperP1.OldValuePrimeBudget PaperP1.CriticalBandScale PaperP1.CriticalBranchingBudget
  PaperP1.BranchingExceptional PaperP1.FixedWindowBranching PaperP1.WindowPoolCount

theorem finite_exception_bound {K : ℝ} (hK : 0 ≤ K) {N L j : ℕ} {A : Finset ℕ}
    (hN : 3 ≤ N) (hL : L ≤ N) (hA : A ⊆ dyadicBlock N) (hj : A.card ≤ j)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (horder : (j : ℝ) ≤ K * Real.log N / Real.log (Real.log N))
    (hh : 4096 ≤ Real.log (Real.log N))
    (hlogA : Real.log (coefficient K) ≤ Real.log (Real.log N)) :
    ((badStarts N L (rawValues A L)).card : ℝ) ≤ exceptionEnvelope K N := by
  have hbudget := raw_budget_le_cubic hK hN hA hL hj hwidth horder hh
  have hpool := card_product_bound hK hN (by omega : 0 < L + 1) hwidth hh hlogA
    (primePool (rawValues A L) (L + 1)) (primePool_prime _ _) hbudget
  have hhalf := badStarts_card_half (rawValues A L) (by omega) hL
  have hnonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := by positivity
  change ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card ≤ _ at hpool
  nlinarith

theorem uniform_exception_bound (K C : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ j : ℕ,
      (j : ℝ) ≤ K * Real.log N / Real.log (Real.log N) →
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        ((badStarts N L (rawValues A L)).card : ℝ) ≤ exceptionEnvelope K N := by
  obtain ⟨Nh, hNh⟩ := eventually_atTop.mp
    (ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop (max 4096 (Real.log (coefficient K)))))
  obtain ⟨Nwidth, hNwidth⟩ := critical_band_scale C
  obtain ⟨Nfinite, _, hNfinite⟩ := ConditionalRankTheorem.finite_conditions C
  refine ⟨max 3 (max Nh (max Nwidth Nfinite)), le_max_left _ _, ?_⟩
  intro N hN j horder L hband A hA hj
  have hlarge := hNh N (by omega)
  obtain ⟨hN3, _, hLN⟩ := hNfinite N (by omega) L hband
  exact finite_exception_bound hK hN3 hLN hA hj (hNwidth N (by omega) L hband).2
    horder ((le_max_left _ _).trans hlarge) ((le_max_right _ _).trans hlarge)

/-- One envelope and one threshold precede every growing order, length and old observation. -/
theorem companion_T22_4 (K C : ℝ) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧ ∃ Dstar : ℕ → ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      0 < Dstar N ∧
      Real.log (Dstar N) ≤ 2 / 3 * Real.log N -
        Real.log N * Real.log (Real.log (Real.log N)) / (9 * Real.log (Real.log N)) +
          c * (Real.log N / Real.log (Real.log N)) ∧
      ∀ j : ℕ, (j : ℝ) ≤ K * Real.log N / Real.log (Real.log N) →
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ (E.card : ℝ) ≤ Dstar N ∧
          IndependentConclusion N L A E := by
  obtain ⟨N₀, hN₀, hbound⟩ := uniform_exception_bound K C hK.le
  refine ⟨errorConstant K, errorConstant_pos hK.le, exceptionEnvelope K, N₀, hN₀, ?_⟩
  intro N hN
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · simp only [exceptionEnvelope, Real.log_exp, rate, le_refl]
  · intro j horder L hband A hA hj
    exact ⟨badStarts N L (rawValues A L), badStarts_subset _ _ _,
      hbound N hN j horder L hband A hA hj, retained_independent (by omega) hA⟩

end PaperP1.CriticalOrderBranching
