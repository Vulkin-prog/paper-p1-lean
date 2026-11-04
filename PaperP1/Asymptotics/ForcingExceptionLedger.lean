module

public import PaperP1.Model.ForcingExceptionalSets
public import PaperP1.Asymptotics.PolylogPivotCount
public import PaperP1.Asymptotics.RawDependenceCount
public import PaperP1.Arithmetic.CleanPivotPairs

/-! # The actual clean-pair minorant with proved exceptional-set losses

The threshold precedes all widths, prime cutoffs, source sets and selected
prime data. Small-pivot and full raw-dependence losses are discharged by
the proved counts. Selection and asymptotics of the reciprocal source sum
remain explicit mathematical work, not assumptions hidden in these bounds.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ForcingExceptionLedger

open Finset PaperP1.ForcingExceptionalSets PaperP1.CleanPivotPairs

theorem uniform_exception_counts (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B Y M S T : ℕ,
      1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      2 * N + B ≤ M → S ≤ B → T ≤ B →
      ((badBoundaries N B Y).card : ℝ) ≤ (N : ℝ) ^ (9 / 10 + ε : ℝ) ∧
      ((dependentBoundaryPairs M N S T).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε : ℝ) := by
  obtain ⟨NV, hV⟩ := PaperP1.PolylogPivotCount.uniform_window_bound D hD ε hε
  obtain ⟨NR, hR⟩ := PaperP1.RawDependenceCount.uniform_rectangular_bound D hD ε hε
  refine ⟨max NV NR, ?_⟩
  intro N hN B Y M S T hB hlog hY hcut hM hS hT
  constructor
  · have hc : ((badBoundaries N B Y).card : ℝ) ≤
        (PaperP1.PolylogPivotExceptions.badWindows N B Y).card := by
      exact_mod_cast badBoundaries_card_le N B Y
    exact hc.trans (hV N (by omega) B Y hlog hY hcut)
  · have hc : ((dependentBoundaryPairs M N S T).card : ℝ) ≤
        (PaperP1.RawDependencePairs.rectangularBadPairs M N S T).card := by
      exact_mod_cast dependentBoundaryPairs_card_le M N S T
    exact hc.trans (hR N (by omega) B hB hlog M S T hM hS hT)

theorem uniform_surviving_lower (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B Y M S T K : ℕ,
      1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      2 * N + B ≤ M → S ≤ B → T ≤ B →
      ∀ J : Finset ℕ, J ⊆ boundaryBlock N →
      ∀ q : ℕ → ℕ, ∀ R : ℕ → Finset ℕ,
      (∀ j ∈ J, Y ≤ q j) → (∀ j ∈ J, ∀ r ∈ R j, Y ≤ r) →
      (∀ j ∈ J, ∀ r ∈ R j, (q j).Coprime r) → (∀ j ∈ J, (R j).card ≤ K) →
      (N : ℝ) * reciprocalSum J q - J.card -
        ((K : ℝ) * T + 1) * (((N : ℝ) / Y) * reciprocalSum J q + J.card) -
        (N : ℝ) ^ (19 / 10 + ε : ℝ) - (N : ℝ) ^ (3 / 2 + ε : ℝ) ≤
      ((survivors J (N - 2) N T q R (badBoundaries N B Y)
        (dependentBoundaryPairs M N S T)).card : ℝ) := by
  obtain ⟨NE, hE⟩ := uniform_exception_counts D hD ε hε
  refine ⟨max NE 2, ?_⟩
  intro N hN B Y M S T K hB hlog hY hcut hM hS hT J hJ q R hq hR hcop hsize
  obtain ⟨hv, hd⟩ := hE N (by omega) B Y M S T hB hlog hY hcut hM hS hT
  have hj : (J.card : ℝ) ≤ N := by
    exact_mod_cast (card_le_card hJ).trans (boundaryBlock_card_le N)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdel : (J.card : ℝ) * (badBoundaries N B Y).card ≤
      (N : ℝ) ^ (19 / 10 + ε : ℝ) := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ (9 / 10 + ε : ℝ) :=
        mul_le_mul hj hv (Nat.cast_nonneg _) hn.le
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (9 / 10 + ε : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hl := surviving_lower J (N - 2) N T Y K q R (badBoundaries N B Y)
    (dependentBoundaryPairs M N S T) (by omega) hq hR hcop hsize
  linarith only [hl, hdel, hd]

end PaperP1.ForcingExceptionLedger
