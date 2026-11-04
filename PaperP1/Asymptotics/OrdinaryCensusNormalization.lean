module

public import PaperP1.Asymptotics.AnchoredCostErrorScale
public import PaperP1.Asymptotics.LogFifthPivotCutoff
public import PaperP1.Asymptotics.PolylogPivotCount
public import PaperP1.Arithmetic.OrdinarySmoothSourcePopulation
public import PaperP1.Analysis.AnchoredCostNormalization

/-! # Uniform normalization of the literal ordinary-source arithmetic ledger

This statement contains no forcing, anchor, probability law or cost.
It can be used unchanged for deterministic or randomized pair weights.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCensusNormalization

open Finset PaperP1.Arithmetic PaperP1.ForcingExceptionalSets
  PaperP1.OrdinarySmoothSourcePopulation PaperP1.AnchoredCostErrorScale PaperP1.LogFifthPivotCutoff

theorem uniform_normalized_ledger (D a t : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B K : ℕ, K + 1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      ((missingCandidates N K ((N : ℝ) ^ a)).card : ℝ) ≤ (t / 2) * N →
      ((1 - 3 * t) * (N : ℝ) ^ (2 - a) ≤
        (1 - ((K : ℝ) * (K + 1 : ℕ) + 1) / cutoff N) * N *
          ((goodSources N K B (cutoff N) ((N : ℝ) ^ a)).card / (N : ℝ) ^ a) -
        (((K : ℝ) * (K + 1 : ℕ) + 1) + 1) * (goodSources N K B (cutoff N) ((N : ℝ) ^ a)).card -
        (N : ℝ) ^ (19 / 10 + errorExponent a : ℝ) - (N : ℝ) ^ (3 / 2 + errorExponent a : ℝ)) ∧
      ((K : ℝ) * (K + 1 : ℕ) + 1) ≤ cutoff N ∧
      (cutoff N : ℝ) ≤ (Real.log N) ^ 5 ∧ 2 * B ≤ cutoff N := by
  have heps := errorExponent_pos ha1
  obtain ⟨NE, hE⟩ := uniform_errors D a t hD ha ha1 ht
  obtain ⟨NZ, hZ⟩ := uniform_data D t ht ht1
  obtain ⟨NV, hV⟩ := PaperP1.PolylogPivotCount.uniform_window_bound D hD (errorExponent a) heps
  refine ⟨max NE (max NZ NV), ?_⟩
  intro N hN B K hKB hB hmissing
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨h2B, hz1, hratio, hcollision, hupper⟩ := hZ N (by omega) B K hB hKB
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
    exact_mod_cast (card_le_card (goodSources_subset N K B (cutoff N) ((N : ℝ) ^ a))).trans (boundaryBlock_card_le N)
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
  rw [hscale] at hnorm
  exact ⟨hnorm, hcollision, hupper, h2B⟩

end PaperP1.OrdinaryCensusNormalization
