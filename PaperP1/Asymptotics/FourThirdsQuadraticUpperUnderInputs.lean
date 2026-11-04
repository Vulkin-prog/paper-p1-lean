module

public import PaperP1.Asymptotics.FourThirdsThirdActivityUnderInputs
public import PaperP1.Asymptotics.TripleActivityLawReconstructionUnderInputs

/-! # Optimal-power upper bound for the exact actual quadratic reference

The symbolic reconstruction only needs the coarse four-thirds third
activity. The stronger41/30 third-order estimate is unnecessary here.
All analytic and finite geometric inputs remain explicit theorem arguments.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourThirdsQuadraticUpperUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables

theorem uniform_exact (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      ∃ pe : FinitePairDeficitInputs.Parameters, ∃ pr : TripleActivityLawReconstructionUnderInputs.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 64)) →
      FinitePairDeficitInputs.Hypotheses pe (GeneralGraphHostCount.sizeCap (ε / 8192)) →
      TripleActivityLawReconstructionUnderInputs.Hypotheses pr (min (ε / 64) (1 / 48)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
          (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Q, hQ, p, pe, ha⟩ := FourThirdsThirdActivityUnderInputs.uniform_absolute_activity
    c κ hc hBCN C (ε / 4) (by positivity)
  obtain ⟨pr, hr⟩ := TripleActivityLawReconstructionUnderInputs.uniform_estimates C (ε / 4) (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Q, hQ, p, pe, pr, ?_⟩
  intro hgeo hgeoE hgeoR
  obtain ⟨Na, _hNa, ha⟩ := ha
    (by simpa only [div_div, show (4 : ℝ) * 16 = 64 by norm_num] using hgeo)
    (by simpa only [div_div, show (4 : ℝ) * 2048 = 8192 by norm_num] using hgeoE)
  obtain ⟨Nr, _hNr, hr⟩ := hr
    (by simpa only [div_div, show (4 : ℝ) * 16 = 64 by norm_num] using hgeoR)
  refine ⟨max 10 (max Na (max Nr Nf)), by omega, ?_⟩
  intro N hN L hcrit G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA := ha N (by omega) L hcrit G hG
  have hR := (hr N (by omega) L hcrit G hG).2
  have hfirst : (N : ℝ) ^ (ε / 4) * CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤
      (N : ℝ) ^ (-4 / 3 + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-4 / 3 + ε / 4) :=
        mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn, show ε / 4 + (-4 / 3 + ε / 4) = -4 / 3 + ε / 2 by ring]
  have hsecond : (N : ℝ) ^ (-4 / 3 + ε / 4) ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hfactor : 2 * (N : ℝ) ^ (-4 / 3 + ε / 2) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
    simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)
  linarith only [hR, hfirst, hsecond, hfactor]

end PaperP1.FourThirdsQuadraticUpperUnderInputs
