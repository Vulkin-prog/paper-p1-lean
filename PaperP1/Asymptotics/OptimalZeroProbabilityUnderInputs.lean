module

public import PaperP1.Asymptotics.PolynomialWeightedQuadraticUnderInputs
public import PaperP1.Probability.PoissonReferenceSeparation

/-! # Optimal approximation for the event of no retained start

The event is Z=0 for starts inside the original dyadic ground. It makes no
assertion about a run that began before the left boundary.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalZeroProbabilityUnderInputs

open Finset PaperP1.Model PaperP1.CountObservables PaperP1.ActualQuadraticSubpowerMoments
  PaperP1.PolynomialWeightedQuadraticUnderInputs

theorem article_17_2 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.channelHeight ∧ (Hypotheses p ε →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |original N L 0 - Real.exp (-countMoment (dyadicBlock N) L 1) *
          (1 + RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 2)| ≤
          (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨p, hQ, hw⟩ := uniform_weighted c κ hc hBCN C ε hε
  refine ⟨p, hQ, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, h⟩ := hw hgeo 0
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hs, hb⟩ := h N hN L hband
  have hz := hs.sum_le_tsum {0} (fun _ _ ↦ by positivity)
  simp only [sum_singleton, pow_zero, one_mul] at hz
  simp only [weightedError, pow_zero, one_mul] at hb
  have hq : quadratic N L 0 = Real.exp (-countMoment (dyadicBlock N) L 1) *
      (1 + RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 2) :=
    PoissonReferenceSeparation.quadratic_mass_zero _ _
  rw [hq] at hz
  exact hz.trans hb

end PaperP1.OptimalZeroProbabilityUnderInputs
