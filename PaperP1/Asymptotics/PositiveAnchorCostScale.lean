module

public import PaperP1.Asymptotics.PositiveTwoCandidateDensity
public import PaperP1.Asymptotics.AnchoredCostErrorScale
public import PaperP1.Asymptotics.LogFifthPivotCutoff
public import PaperP1.Analysis.PositiveFractionCostNormalization

/-! # The actual clean-source anchored ledger has a fixed positive power-scale lower bound

All ordinary-candidate census, collision and exceptional losses are supplied
internally. This arithmetic bracket is shared by deterministic and randomized
private forcing cost comparisons.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveAnchorCostScale

open Finset ForcingExceptionalSets OrdinarySmoothSourcePopulation LogFifthPivotCutoff AnchoredCostErrorScale

theorem uniform_bracket_lower (C D a : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (ha1 : a < 1 / 10) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ, ∀ i : Fin 2, ∀ B : ℕ,
      1 ≤ L → L + i.val + 1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      r * (N : ℝ) ^ (2 - a) ≤
        (1 - (((L + i.val : ℕ) : ℝ) * (L + i.val + 1 : ℕ) + 1) / cutoff N) * N *
            ((goodSources N (L + i.val) B (cutoff N) ((N : ℝ) ^ a)).card / (N : ℝ) ^ a) -
          ((((L + i.val : ℕ) : ℝ) * (L + i.val + 1 : ℕ) + 1) + 1) *
            (goodSources N (L + i.val) B (cutoff N) ((N : ℝ) ^ a)).card -
          (N : ℝ) ^ (19 / 10 + errorExponent a) - (N : ℝ) ^ (3 / 2 + errorExponent a) := by
  obtain ⟨δ, hδ, NS, hs⟩ := PositiveTwoCandidateDensity.uniform_clean_two_candidates C D a hD ha
  obtain ⟨NE, he⟩ := uniform_errors D a (δ / 4) hD ha ha1 (by positivity)
  obtain ⟨NZ, hz⟩ := uniform_data D (1 / 4) (by norm_num) (by norm_num)
  refine ⟨δ / 2, by positivity, max NS (max NE NZ), ?_⟩
  intro N hN L i B hL hKB hwidth hcrit
  let K := L + i.val
  let J := goodSources N K B (cutoff N) ((N : ℝ) ^ a)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨_hbig, hZ, hratio, _hc, hupper⟩ := hz N (by omega) B K hwidth hKB
  have hsource := hs N (by omega) L i B (cutoff N) (by omega) hwidth hZ hupper hcrit
  have hjhi : (J.card : ℝ) ≤ N := by
    exact_mod_cast (card_le_card (goodSources_subset N K B (cutoff N) ((N : ℝ) ^ a))).trans
      (boundaryBlock_card_le N)
  have hKwidth : ((K + 1 : ℕ) : ℝ) ≤ D * Real.log N :=
    (by exact_mod_cast hKB : ((K + 1 : ℕ) : ℝ) ≤ B).trans hwidth
  have herr := (he N (by omega) K hKwidth).2
  have hscale : (N : ℝ) ^ (2 - a) = (N : ℝ) ^ 2 / (N : ℝ) ^ a := by
    rw [Real.rpow_sub hn, Real.rpow_two]
  rw [hscale] at herr ⊢
  exact PositiveFractionCostNormalization.with_errors hn.le (Real.rpow_pos_of_pos hn a)
    hδ.le (by positivity : (0 : ℝ) ≤ (K : ℝ) * (K + 1 : ℕ) + 1) hratio hsource hjhi herr

end PaperP1.PositiveAnchorCostScale
