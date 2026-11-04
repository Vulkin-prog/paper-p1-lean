module

public import PaperP1.Asymptotics.FourThirdsQuadraticUpperUnderInputs
public import PaperP1.Asymptotics.ActualQuadraticSubpowerMoments
public import PaperP1.Model.QuadraticFactorialMomentTransfer
public import PaperP1.Model.FourthCharlierLawDistance

/-! # Every fixed polynomial weight at the optimal quadratic power

One finite geometric bundle is chosen before the polynomial degree. Its fields
are actual source/ordinary covers and normalized curve counts, never weighted
errors or moment bounds. All moments and summability assertions are proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialWeightedQuadraticUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.CountObservables
  PaperP1.ActualQuadraticSubpowerMoments PaperP1.FactorialCountMoments

structure Parameters where
  channelHeight : ℕ
  channels : (ab : FiniteInteriorUnitEdges.channels channelHeight) → FiniteCompressedInteriorMass.Parameters
  tripleError : FinitePairDeficitInputs.Parameters
  reconstruction : TripleActivityLawReconstructionUnderInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  channels : ∀ ab, FiniteCompressedInteriorMass.Hypotheses (p.channels ab) ab.val.2 (ε / 256)
  tripleError : FinitePairDeficitInputs.Hypotheses p.tripleError (GeneralGraphHostCount.sizeCap (ε / 32768))
  reconstruction : TripleActivityLawReconstructionUnderInputs.Hypotheses p.reconstruction (min (ε / 256) (1 / 48))

def weightedError (N L m : ℕ) : ℝ := ∑' k : ℕ, (1 + (k : ℝ)) ^ m * |original N L k - quadratic N L k|

theorem uniform_weighted (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.channelHeight ∧ (Hypotheses p ε →
      ∀ m : ℕ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Summable (fun k : ℕ ↦ (1 + (k : ℝ)) ^ m * |original N L k - quadratic N L k|) ∧
        weightedError N L m ≤ (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨Q, hQ, ps, pe, pr, hu⟩ := FourThirdsQuadraticUpperUnderInputs.uniform_exact
    c κ hc hBCN C (ε / 4) (by positivity)
  refine ⟨⟨Q, ps, pe, pr⟩, hQ, ?_⟩
  intro hgeo
  obtain ⟨Nu, _hNu, hu⟩ := hu
    (by simpa only [div_div, show (4 : ℝ) * 64 = 256 by norm_num] using hgeo.channels)
    (by simpa only [div_div, show (4 : ℝ) * 8192 = 32768 by norm_num] using hgeo.tripleError)
    (by simpa only [div_div, show (4 : ℝ) * 64 = 256 by norm_num] using hgeo.reconstruction)
  simp only [weightedError, show (-4 / 3 : ℝ) = -(4 / 3) by ring]
  apply PolynomialWeightedSequenceRate.uniform_bound original quadratic (fun k : ℕ ↦ 1 + (k : ℝ))
    (fun k ↦ le_add_of_nonneg_right (Nat.cast_nonneg k)) C (4 / 3) ε hε
  · refine ⟨Nu, ?_⟩
    intro N hN L hband
    have hμ : 0 ≤ countMoment (dyadicBlock N) L 1 := by
      rw [← HeterogeneousDirectMaximum.actualMean_eq_countMoment (subset_refl (dyadicBlock N))]
      exact sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
    refine ⟨((AtomicProbability.hasSum_realMass _).summable.sub
      (PoissonSequence.hasSum_quadraticMass _ _ hμ).summable).abs, ?_⟩
    have hh := hu N hN L hband (dyadicBlock N) (subset_refl _)
    rw [FourthCharlierLawDistance.distance_eq_sequence _ _ _ hμ] at hh
    simpa only [original, quadratic, show (-4 / 3 : ℝ) = -(4 / 3) by ring] using hh
  · intro r δ hδ
    obtain ⟨N₀, _hN₀, h⟩ := uniform_moments c κ hc hBCN C r δ hδ
    exact ⟨N₀, h⟩

theorem article_17_1 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.channelHeight ∧ (Hypotheses p ε →
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
          RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)) := by
  obtain ⟨p, hQ, hw⟩ := uniform_weighted c κ hc hBCN C ε hε
  refine ⟨p, hQ, ?_⟩
  intro hgeo
  have hw := hw hgeo
  refine ⟨hw, ?_, fun N L ↦ QuadraticFactorialMomentTransfer.exact_small_orders (subset_refl (dyadicBlock N))⟩
  intro r
  obtain ⟨N₁, hN₁, h⟩ := hw r
  refine ⟨N₁, hN₁, ?_⟩
  intro N hN L hband
  obtain ⟨hs, hb⟩ := h N hN L hband
  exact (QuadraticFactorialMomentTransfer.finite_bound (subset_refl (dyadicBlock N)) r hs).trans hb

end PaperP1.PolynomialWeightedQuadraticUnderInputs
