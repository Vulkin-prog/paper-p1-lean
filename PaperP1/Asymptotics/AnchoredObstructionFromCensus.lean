module

public import PaperP1.Asymptotics.AnchoredSmallPivotCostLower
public import PaperP1.Asymptotics.AnchoredCostErrorScale
public import PaperP1.Asymptotics.LogFifthPivotCutoff
public import PaperP1.Analysis.AnchoredCostNormalization

/-! # The uniform actual anchored obstruction from its independent ordinary source census

Only the genuine ordinary-candidate census remains as a finite arithmetic
condition. Every other error, cutoff, source selection, observation law
and actual forcing-cost comparison is discharged internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredObstructionFromCensus

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.AnchoredPrivateField PaperP1.OrdinarySmoothSourcePopulation
  PaperP1.AnchoredCostErrorScale PaperP1.LogFifthPivotCutoff

theorem uniform_census_implication (D a t : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B Y K M : ℕ,
      1 ≤ K → K + 1 ≤ B → B ≤ Y → Y ≤ cutoff N →
      (B : ℝ) ≤ D * Real.log N → 2 * N + B ≤ M →
      ((missingCandidates N K ((N : ℝ) ^ a)).card : ℝ) ≤ (t / 2) * N →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1),
      ∀ A : Data M Y K (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y) anchor,
      ∀ b : Fin (K + 1) → F₂,
      (1 - 3 * t) * (rate K) ^ 2 * (N : ℝ) ^ (2 - a) ≤ offsite A b := by
  have heps := errorExponent_pos ha1
  obtain ⟨NC, hC⟩ := PaperP1.AnchoredSmallPivotCostLower.uniform_ordinary_candidates_lower
    D hD (errorExponent a) heps
  obtain ⟨NE, hE⟩ := uniform_errors D a t hD ha ha1 ht
  obtain ⟨NZ, hZ⟩ := uniform_data D t ht ht1
  obtain ⟨NV, hV⟩ := PaperP1.PolylogPivotCount.uniform_window_bound D hD (errorExponent a) heps
  refine ⟨max (max NC NE) (max NZ NV), ?_⟩
  intro N hN B Y K M hK hKB hBY hYZ hB hM hmissing anchor A b
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨_h2B, hz1, hratio, hcollision, hupper⟩ := hZ N (by omega) B K hB hKB
  have hKlog : ((K + 1 : ℕ) : ℝ) ≤ D * Real.log N :=
    (by exact_mod_cast hKB : ((K + 1 : ℕ) : ℝ) ≤ B).trans hB
  obtain ⟨hbadscale, herr⟩ := hE N (by omega) K hKlog
  have hbad := hV N (by omega) B (cutoff N) hB hz1 hupper
  have hbadbound : ((badBoundaries N B (cutoff N)).card : ℝ) ≤ (t / 2) * N := by
    have hc : ((badBoundaries N B (cutoff N)).card : ℝ) ≤
        (PaperP1.PolylogPivotExceptions.badWindows N B (cutoff N)).card := by
      exact_mod_cast badBoundaries_card_le N B (cutoff N)
    exact hc.trans (hbad.trans hbadscale)
  let J := goodSources N K B (cutoff N) ((N : ℝ) ^ a)
  have hjhi : (J.card : ℝ) ≤ N := by
    exact_mod_cast (card_le_card (goodSources_subset N K B (cutoff N) ((N : ℝ) ^ a))).trans
      (boundaryBlock_card_le N)
  have hledger : (N : ℝ) ≤ J.card + (missingCandidates N K ((N : ℝ) ^ a)).card +
      (badBoundaries N B (cutoff N)).card := by
    exact_mod_cast source_deletion_ledger (K := K) (B := B) (Z := cutoff N) ((N : ℝ) ^ a) (by omega)
  have hjlo : (1 - t) * (N : ℝ) ≤ J.card := by linarith only [hledger, hmissing, hbadbound]
  have hscale : (N : ℝ) ^ 2 / (N : ℝ) ^ a = (N : ℝ) ^ (2 - a) := by
    rw [Real.rpow_sub hn, Real.rpow_two]
  have herr' : (((K : ℝ) * (K + 1 : ℕ) + 1) + 1) * N +
      (N : ℝ) ^ (19 / 10 + errorExponent a : ℝ) + (N : ℝ) ^ (3 / 2 + errorExponent a : ℝ) ≤
        t * ((N : ℝ) ^ 2 / (N : ℝ) ^ a) := by rwa [hscale]
  have hnorm := PaperP1.AnchoredCostNormalization.with_errors hn.le (Real.rpow_pos_of_pos hn a)
    ht1 (by positivity : (0 : ℝ) ≤ (K : ℝ) * (K + 1 : ℕ) + 1) hratio hjlo hjhi herr'
  have hoff := hC N (by omega) B Y (cutoff N) K M ((N : ℝ) ^ a) hK hKB hBY hB
    hYZ hupper hM hcollision anchor A b
  calc
    _ = (rate K) ^ 2 * ((1 - 3 * t) * ((N : ℝ) ^ 2 / (N : ℝ) ^ a)) := by rw [hscale]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (sq_nonneg (rate K))
    _ ≤ offsite A b := hoff

end PaperP1.AnchoredObstructionFromCensus
