module

public import PaperP1.Arithmetic.BranchingExceptional
public import PaperP1.Model.ConditionalRelativeBits
public import PaperP1.Asymptotics.ConditionalRankTheorem

/-! # Exact fixed-window branching, with a smaller deterministic exception set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedWindowBranching

open Finset MeasureTheory ProbabilityTheory PaperP1.Arithmetic PaperP1.Model
  PaperP1.OldValuePrimeBudget PaperP1.OldPrimeCardinality PaperP1.BranchingExceptional
  PaperP1.ConditionalRelativeBits PaperP1.RelativeSignIndependence PaperP1.ConditionalWindowRank
  PaperP1.Model.InfiniteRademacher PaperP1.ConditionalRunProbability
  PaperP1.CriticalBandScale PaperP1.WindowPoolCount

local instance fixedWindowMeasurableF2 : MeasurableSpace F₂ := ⊤

def IndependentConclusion (N L : ℕ) (A E : Finset ℕ) : Prop :=
  ∀ x ∈ dyadicBlock N, x ∉ E →
    infiniteRademacherMeasure.map (infiniteStartBits x L) = Measure.pi (fun _ : Fin L ↦ coordinateMeasure) ∧
    IndepFun (infiniteStartBits x L) (infiniteOldBits (rawValues A L)) infiniteRademacherMeasure ∧
    ∀ (a : SampleSpace (dyadicCutoff N L)) (b : Fin L → F₂),
      conditionalWordProbability (rawValues A L) a x L b = (2 ^ L : ℝ)⁻¹

theorem retained_independent {N L : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hA : A ⊆ dyadicBlock N) :
    IndependentConclusion N L A (badStarts N L (rawValues A L)) := by
  intro x hx hnot
  have hxb := mem_Ico.mp hx
  have hxpos : 0 < x := (by norm_num : 0 < (2 : ℕ)).trans_le (hN.trans hxb.1)
  have hcut : x + L ≤ dyadicCutoff N L := by unfold dyadicCutoff; omega
  have hR := ConditionalRankTheorem.rawValues_le_cutoff (L := L) hA
  have hcard := retained_card_le_one hx hnot
  exact ⟨map_new_eq_fair hxpos hcut hR hcard, independent_of_old hxpos hcut hR hcard,
    fun a b ↦ conditionalWordProbability_nominal hxpos hcut hR a hcard b⟩

theorem finite_stronger {N L j : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hLN : L ≤ N) (hA : A ⊆ dyadicBlock N) (hj : A.card ≤ j) :
    ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ IndependentConclusion N L A E ∧
      (E.card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2 * Real.sqrt (3 * N : ℕ) *
        Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by
  exact ⟨badStarts N L (rawValues A L), badStarts_subset _ _ _, retained_independent hN hA,
    badStarts_card_explicit hA hN hL hLN hj⟩

theorem finite_source_bound {N L j : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hLN : L ≤ N) (hA : A ⊆ dyadicBlock N) (hj : A.card ≤ j) :
    ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ IndependentConclusion N L A E ∧
      (E.card : ℝ) ≤ (j : ℝ) * (2 * L + 1) + ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
        Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by
  obtain ⟨E, hE, hind, hcount⟩ := finite_stronger hN hL hLN hA hj
  refine ⟨E, hE, hind, hcount.trans ?_⟩
  have hprod : 0 ≤ ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
      Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by positivity
  have hjL : (0 : ℝ) ≤ (j : ℝ) * (2 * L + 1) := by positivity
  nlinarith

theorem badStarts_card_critical (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        ((badStarts N L (rawValues A L)).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨Npool, hNpool, hpool⟩ := LogSquaredPrimePool.actual_pool_count_critical C j (ε / 2) (by linarith)
  obtain ⟨Nwidth, hwidth⟩ := critical_band_scale C
  obtain ⟨NB, hB⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 1 (ε / 2) (by linarith)
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  refine ⟨max Npool (max Nwidth (max NB Nfinite)), by omega, ?_⟩
  intro N hN L hband A hA hj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hN3, _, hLN⟩ := hfinite N (by omega) L hband
  have hwidthN := (hwidth N (by omega) L hband).2
  have hBN : ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_mul, pow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hB N (by omega) L hwidthN
  have hpoolN := hpool N (by omega) L hband A hA hj
  have hhalf := badStarts_card_half (rawValues A L) (by omega) hLN
  have hcoarse : ((badStarts N L (rawValues A L)).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := by
    have hprod : 0 ≤ ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := by positivity
    nlinarith
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) * (poolValues (rawValues A L) (L + 1) (3 * N)).card := hcoarse
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul hBN hpoolN (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

theorem original_windows_critical (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ IndependentConclusion N L A E ∧
          (E.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) ∧
          (E.card : ℝ) ≤ (j : ℝ) * (2 * L + 1) + ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
            Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by
  obtain ⟨Ncount, hNcount, hcount⟩ := badStarts_card_critical C j ε hε
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  refine ⟨max Ncount Nfinite, by omega, ?_⟩
  intro N hN L hband A hA hj
  obtain ⟨hN3, hLpos, hLN⟩ := hfinite N (by omega) L hband
  have hsharp := badStarts_card_explicit hA (by omega) hLpos hLN hj
  have hsource : ((badStarts N L (rawValues A L)).card : ℝ) ≤
      (j : ℝ) * (2 * L + 1) + ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
        Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by
    have hprod : 0 ≤ ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
        Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by positivity
    have hjL : (0 : ℝ) ≤ (j : ℝ) * (2 * L + 1) := by positivity
    nlinarith
  exact ⟨badStarts N L (rawValues A L), badStarts_subset _ _ _, retained_independent (by omega) hA,
    hcount N (by omega) L hband A hA hj, hsource⟩

end PaperP1.FixedWindowBranching
