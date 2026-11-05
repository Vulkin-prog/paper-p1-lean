module

public import PaperP1.Asymptotics.FourThirdsQuadraticUpper
public import PaperP1.Asymptotics.ActualQuadraticMomentBounds
public import PaperP1.Model.QuadraticFactorialMomentTransfer
public import PaperP1.Model.FourthCharlierLawDistance

/-! # Every fixed polynomial weight at the optimal actual quadratic power

Both the unweighted rate and every auxiliary fixed moment are supplied
internally. No finite geometric bundle or target error premise remains.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialWeightedQuadratic

open Finset MeasureTheory Model CountObservables FactorialCountMoments
open ActualQuadraticSubpowerMoments (original quadratic)

def weightedError (N L m : ℕ) : ℝ :=
  ∑' k : ℕ, (1 + (k : ℝ)) ^ m * |original N L k - quadratic N L k|

theorem uniform_weighted (C ε : ℝ) (hε : 0 < ε) :
    ∀ m : ℕ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Summable (fun k : ℕ ↦ (1 + (k : ℝ)) ^ m * |original N L k - quadratic N L k|) ∧
      weightedError N L m ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨NU, _hNU, hu⟩ := FourThirdsQuadraticUpper.uniform_exact C (ε / 4) (by positivity)
  simp only [weightedError, show (-4 / 3 : ℝ) = -(4 / 3) by ring]
  apply PolynomialWeightedSequenceRate.uniform_bound original quadratic (fun k : ℕ ↦ 1 + (k : ℝ))
    (fun k ↦ le_add_of_nonneg_right (Nat.cast_nonneg k)) C (4 / 3) ε hε
  · refine ⟨NU, ?_⟩
    intro N hN L hband
    have hμ : 0 ≤ countMoment (dyadicBlock N) L 1 := by
      rw [← HeterogeneousDirectMaximum.actualMean_eq_countMoment (subset_refl (dyadicBlock N))]
      exact sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
    refine ⟨((AtomicProbability.hasSum_realMass _).summable.sub
      (PoissonSequence.hasSum_quadraticMass _ _ hμ).summable).abs, ?_⟩
    have hh := hu N hN L hband (dyadicBlock N) Subset.rfl
    rw [FourthCharlierLawDistance.distance_eq_sequence _ _ _ hμ] at hh
    simpa only [original, quadratic, show (-4 / 3 : ℝ) = -(4 / 3) by ring] using hh
  · intro r δ hδ
    obtain ⟨N₀, _hN₀, h⟩ := ActualQuadraticMomentBounds.uniform_moments C r δ hδ
    exact ⟨N₀, h⟩

theorem article_17_1 (C ε : ℝ) (hε : 0 < ε) :
    (∀ m : ℕ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Summable (fun k : ℕ ↦ (1 + (k : ℝ)) ^ m * |original N L k - quadratic N L k|) ∧
      weightedError N L m ≤ (N : ℝ) ^ (-4 / 3 + ε)) ∧
    (∀ r : ℕ, ∃ N₁ : ℕ, 2 ≤ N₁ ∧ ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |factorialCountMoment (dyadicBlock N) L r -
        QuadraticFactorialMomentTransfer.referenceMoment (countMoment (dyadicBlock N) L 1)
          (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L) r| ≤
        (N : ℝ) ^ (-4 / 3 + ε)) ∧
    (∀ N L : ℕ, factorialCountMoment (dyadicBlock N) L 0 = 1 ∧
      factorialCountMoment (dyadicBlock N) L 1 = countMoment (dyadicBlock N) L 1 ∧
      factorialCountMoment (dyadicBlock N) L 2 = (countMoment (dyadicBlock N) L 1) ^ 2 +
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L) := by
  have hw := uniform_weighted C ε hε
  refine ⟨hw, ?_, fun N L ↦ QuadraticFactorialMomentTransfer.exact_small_orders (subset_refl (dyadicBlock N))⟩
  intro r
  obtain ⟨N₁, hN₁, h⟩ := hw r
  refine ⟨N₁, hN₁, ?_⟩
  intro N hN L hband
  obtain ⟨hs, hb⟩ := h N hN L hband
  exact (QuadraticFactorialMomentTransfer.finite_bound (subset_refl (dyadicBlock N)) r hs).trans hb

end PaperP1.PolynomialWeightedQuadratic
