module

public import PaperP1.Arithmetic.RelaxedSaturation
public import PaperP1.Asymptotics.SaturationDegrees

/-! # Uniform degree bounds for the lower saturation threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelaxedSaturationDegrees

open Filter Finset PaperP1.RelaxedSaturation PaperP1.ModerateOrder

theorem relaxed_neighborhood_bounds (C A ε : ℝ) (hA : 1 < A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ Ico N (2 * N),
      ((outgoing (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ (2 / A + ε) ∧
      ((incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ (2 / A + ε) ∧
      ((outgoing (L + 1) N (cutoff A N) x ∪ incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤
        (N : ℝ) ^ (2 / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  obtain ⟨Nbudget, hbudget⟩ := eventually_atTop.mp
    (PaperP1.SaturationDegreeBudget.product_le_power_eventually A PaperP1.CriticalBandScale.upperScale
      (2 * Real.exp 1) 2 ε (by linarith) hD (by positivity) (by norm_num) hε)
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C A hA
  refine ⟨max Nbudget Nfinite, ?_⟩
  intro N hN L hL x hx
  obtain ⟨hN10, hB, hBN, hY, hwidth⟩ := hfinite N (by omega) L hL
  have hunion := neighbors_bound hN10 hB hBN hx (cutoff A N) hY
  have hpower := hbudget N (by omega) (L + 1) (by omega) hwidth
  change 2 * (↑(L + 1) : ℝ) ^ 2 * (2 * Real.exp 1 * (↑(L + 1) : ℝ)) ^
    PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) ≤ _ at hpower
  have h := hunion.trans hpower
  have hout : ((outgoing (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (outgoing (L + 1) N (cutoff A N) x ∪ incoming (L + 1) N (cutoff A N) x).card := by
    exact_mod_cast card_le_card (subset_union_left : outgoing (L + 1) N (cutoff A N) x ⊆ _)
  have hin : ((incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (outgoing (L + 1) N (cutoff A N) x ∪ incoming (L + 1) N (cutoff A N) x).card := by
    exact_mod_cast card_le_card (subset_union_right : incoming (L + 1) N (cutoff A N) x ⊆ _)
  exact ⟨hout.trans h, hin.trans h, h⟩

end PaperP1.RelaxedSaturationDegrees
