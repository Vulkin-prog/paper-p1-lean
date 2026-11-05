module

public import PaperP1.Asymptotics.PolynomialWeightedQuadratic
public import PaperP1.Probability.PoissonReferenceSeparation

/-! # Complete main Corollary 17.2 for no retained start in the original ground -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalZeroProbability

open Finset Model CountObservables PolynomialWeightedQuadratic
open ActualQuadraticSubpowerMoments (original quadratic)

theorem article_17_2 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |original N L 0 - Real.exp (-countMoment (dyadicBlock N) L 1) *
        (1 + RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 2)| ≤
        (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_weighted C ε hε 0
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

end PaperP1.OptimalZeroProbability
