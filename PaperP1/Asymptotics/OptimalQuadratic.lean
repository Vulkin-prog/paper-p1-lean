module

public import PaperP1.Asymptotics.FourThirdsQuadraticUpper
public import PaperP1.Asymptotics.QuadraticLawLowerBound
public import PaperP1.Asymptotics.ActualReferenceProbability

/-! # Complete optimal quadratic approximation of the original law

The exact original mean and second factorial cumulant are retained in both
power bounds, nominal-mean bias and eventual probability status.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalQuadratic

open Finset MeasureTheory Model Model.InfiniteStarts CountObservables

def reference (N L : ℕ) : SignedMeasure ℕ := QuadraticPoisson.reference
  (countMoment (dyadicBlock N) L 1) (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)

def error (N L : ℕ) : ℝ := SignedAtomicDistance.distance
  (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure (reference N L)

theorem article_1_1 (C ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      a * (N : ℝ) ^ (-4 / 3 - ε) ≤ error N L ∧ error N L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
      |countMoment (dyadicBlock N) L 1 - (N : ℝ) * (2 ^ L : ℝ)⁻¹| ≤
        (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε) ∧ AtomicSignedLaw.IsProbability (reference N L) := by
  obtain ⟨NU, _hNU, hu⟩ := FourThirdsQuadraticUpper.uniform_exact C ε hε
  obtain ⟨a, ha, NL, _hNL, hl⟩ := QuadraticLawLowerBound.article_16_2_lower C ε hε
  obtain ⟨NB, _hNB, hb⟩ := CriticalActualMean.uniform_nominal_bias C ε hε
  obtain ⟨NP, _hNP, hp⟩ := ActualReferenceProbability.uniform_quadratic_probability C
  refine ⟨a, ha, 10 + NU + NL + NB + NP, by omega, ?_⟩
  intro N hN L hband
  refine ⟨?_, hu N (by omega) L hband (dyadicBlock N) Subset.rfl,
    hb N (by omega) L hband, hp N (by omega) L hband⟩
  simpa only [error, reference,
    HeterogeneousDirectMaximum.actualMean_eq_countMoment (subset_refl (dyadicBlock N))] using
    hl N (by omega) L hband

theorem article_16_2 (C ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      a * (N : ℝ) ^ (-4 / 3 - ε) ≤ error N L ∧ error N L ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨a, ha, N₀, hN₀, h⟩ := article_1_1 C ε hε
  exact ⟨a, ha, N₀, hN₀, fun N hN L hband ↦
    ⟨(h N hN L hband).1, (h N hN L hband).2.1⟩⟩

end PaperP1.OptimalQuadratic
