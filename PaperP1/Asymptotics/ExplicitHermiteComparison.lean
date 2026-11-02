module

public import PaperP1.Asymptotics.ExplicitReferenceAdmissibility
public import PaperP1.Probability.HermiteSignedComparison

/-! # Unconditional N^(-4/3+epsilon) comparison of the explicit references

The comparison and the stability of distances hold for every fixed height
and every actual probability law. No approximation of the original count
law, pair-profile remainder or optimality statement is a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitHermiteComparison

open MeasureTheory PaperP1.FiniteChannelHierarchy PaperP1.FiniteChannelHierarchyBounds

def signedError (N L h : ℕ) : ℝ := ∑' k : ℕ,
  |(QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) -
    CompletedLaw.toSignedMeasure (HermiteReference.reference (nominalMean N L) (coefficient N L h))) {k}|

theorem uniform_bound (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → signedError N L h ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NA, hNA, hpower⟩ := uniform_power_bound C h hh η hη
  obtain ⟨NP, hNP, hpositive⟩ := uniform_positive C h hh
  obtain ⟨NS, hNS, hsmall⟩ := uniform_small C h hh 1 (by norm_num)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption
    (4 * Real.exp 2) (-4 / 3 + 2 * η) (ε / 2) (by positivity)
  refine ⟨max NA (max NP (max NS NF)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hμ : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hα : 0 ≤ coefficient N L h := (hpositive N (by omega) L hband).le
  have hα1 := hsmall N (by omega) L hband
  have hsquare : (coefficient N L h) ^ 2 ≤ (N : ℝ) ^ (-4 / 3 + 2 * η) := by
    apply (pow_le_pow_left₀ hα (hpower N (by omega) L hband) 2).trans_eq
    rw [pow_two, ← Real.rpow_add hn]
    congr 1
    ring
  have hexp : Real.exp (2 * |coefficient N L h|) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hα]
    linarith only [hα1]
  calc
    _ ≤ 4 * (coefficient N L h) ^ 2 * Real.exp (2 * |coefficient N L h|) :=
      HermiteSignedComparison.actual_signed_error_symmetric _ _ hμ
    _ ≤ 4 * (N : ℝ) ^ (-4 / 3 + 2 * η) * Real.exp 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hexp
        (Real.exp_nonneg _) (by positivity)
    _ = (4 * Real.exp 2) * (N : ℝ) ^ (-4 / 3 + 2 * η) := by ring
    _ ≤ (N : ℝ) ^ ((-4 / 3 + 2 * η) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

/-- Actual probability witnesses for the two literal references, and a
comparison of their distances to every actual law on the natural numbers. -/
theorem uniform_reference_stability (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ Q H : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure =
          QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) ∧
        (H : Measure ℕ).toSignedMeasure = CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L h)) ∧
        ∀ P : ProbabilityMeasure ℕ,
          |AtomicProbability.totalVariation P Q - AtomicProbability.totalVariation P H| ≤
            (N : ℝ) ^ (-4 / 3 + ε) / 2 := by
  obtain ⟨NA, hNA, herror⟩ := uniform_bound C h hh ε hε
  obtain ⟨NP, hNP, hprob⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  refine ⟨max NA NP, by omega, ?_⟩
  intro N hN L hband
  have hp := hprob N (by omega) L hband
  obtain ⟨Q, hQ⟩ := hp.2.2.1
  obtain ⟨H, hH⟩ := hp.2.2.2
  refine ⟨Q, H, hQ, hH, ?_⟩
  intro P
  have hs := AtomicProbabilityMetric.reference_stability_signed P Q H
  rw [hQ, hH] at hs
  exact hs.trans (div_le_div_of_nonneg_right (herror N (by omega) L hband) (by norm_num))

end PaperP1.ExplicitHermiteComparison
