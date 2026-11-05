module

public import PaperP1.Asymptotics.SharpThirdActivity
public import PaperP1.Asymptotics.TripleActivityLawReconstruction

/-! # The internal optimal-power upper bound for the actual quadratic reference

The symbolic reconstruction and complete actual third-activity theorem
supply every arithmetic input, uniformly on original subgrounds.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourThirdsQuadraticUpper

open Finset MeasureTheory Model Model.InfiniteStarts CountObservables

theorem uniform_exact (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
        (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
        (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := SharpThirdActivity.uniform_absolute C (ε / 4) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := TripleActivityLawReconstruction.uniform_estimates C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NA + NR + NF, by omega, ?_⟩
  intro N hN L hcrit G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA : CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-4 / 3 + ε / 4) :=
    (ha N (by omega) L hcrit G hG).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
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

end PaperP1.FourThirdsQuadraticUpper
