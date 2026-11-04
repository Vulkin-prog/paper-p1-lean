module

public import PaperP1.Asymptotics.FourThirdsQuadraticUpperUnderInputs
public import PaperP1.Asymptotics.QuadraticLawLowerBoundUnderInputs
public import PaperP1.Asymptotics.ActualReferenceAdmissibility

/-! # The actual optimal quadratic approximation under explicit analytic and geometric inputs

Both power bounds, the nominal-mean bias and eventual probability status
are assembled. The theorem uses the original law, exact actual mean and
second factorial cumulant. It does not assume a quadratic error bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalQuadraticUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables

structure Parameters where
  channelHeight : ℕ
  channels : (ab : FiniteInteriorUnitEdges.channels channelHeight) → FiniteCompressedInteriorMass.Parameters
  tripleError : FinitePairDeficitInputs.Parameters
  reconstruction : TripleActivityLawReconstructionUnderInputs.Parameters
  lowerOrder : ℕ
  lower : QuadraticLawLowerBoundUnderInputs.Parameters lowerOrder

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  channels : ∀ ab, FiniteCompressedInteriorMass.Hypotheses (p.channels ab) ab.val.2 (ε / 64)
  tripleError : FinitePairDeficitInputs.Hypotheses p.tripleError (GeneralGraphHostCount.sizeCap (ε / 8192))
  reconstruction : TripleActivityLawReconstructionUnderInputs.Hypotheses p.reconstruction (min (ε / 64) (1 / 48))
  lower : QuadraticLawLowerBoundUnderInputs.Hypotheses p.lower

def reference (N L : ℕ) : SignedMeasure ℕ := QuadraticPoisson.reference
  (countMoment (dyadicBlock N) L 1) (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)

def error (N L : ℕ) : ℝ := SignedAtomicDistance.distance
  (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure (reference N L)

theorem article_1_1 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.channelHeight ∧ 4 ≤ p.lowerOrder ∧ (Hypotheses p ε →
      ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        a * (N : ℝ) ^ (-4 / 3 - ε) ≤ error N L ∧ error N L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
        |countMoment (dyadicBlock N) L 1 - (N : ℝ) * (2 ^ L : ℝ)⁻¹| ≤
          (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε) ∧ AtomicSignedLaw.IsProbability (reference N L)) := by
  obtain ⟨Q, hQ, ps, pe, pr, hu⟩ := FourThirdsQuadraticUpperUnderInputs.uniform_exact c κ hc hBCN C ε hε
  obtain ⟨r, hr, pl, hl⟩ := QuadraticLawLowerBoundUnderInputs.article_16_2_lower C ε hε
  obtain ⟨Nb, _hNb, hb⟩ := CriticalActualMean.uniform_nominal_bias C ε hε
  obtain ⟨Np, _hNp, hp⟩ := ActualReferenceAdmissibility.uniform_quadratic_probability c κ hc hBCN C
  refine ⟨⟨Q, ps, pe, pr, r, pl⟩, hQ, hr, ?_⟩
  intro hgeo
  obtain ⟨Nu, _hNu, hu⟩ := hu hgeo.channels hgeo.tripleError hgeo.reconstruction
  obtain ⟨a, ha, Nl, _hNl, hl⟩ := hl hgeo.lower
  refine ⟨a, ha, max 10 (max Nu (max Nl (max Nb Np))), by omega, ?_⟩
  intro N hN L hcrit
  refine ⟨?_, hu N (by omega) L hcrit (dyadicBlock N) (subset_refl _),
    hb N (by omega) L hcrit, hp N (by omega) L hcrit⟩
  have hh := hl N (by omega) L hcrit
  simpa only [error, reference, HeterogeneousDirectMaximum.actualMean_eq_countMoment (subset_refl (dyadicBlock N))] using hh

theorem article_16_2 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.channelHeight ∧ 4 ≤ p.lowerOrder ∧ (Hypotheses p ε →
      ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        a * (N : ℝ) ^ (-4 / 3 - ε) ≤ error N L ∧ error N L ≤ (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨p, hQ, hr, h⟩ := article_1_1 c κ hc hBCN C ε hε
  refine ⟨p, hQ, hr, ?_⟩
  intro hgeo
  obtain ⟨a, ha, N₀, hN₀, h⟩ := h hgeo
  exact ⟨a, ha, N₀, hN₀, fun N hN L hcrit ↦
    ⟨(h N hN L hcrit).1, (h N hN L hcrit).2.1⟩⟩

end PaperP1.OptimalQuadraticUnderInputs
