module

public import PaperP1.Probability.PoissonParameterStability
public import PaperP1.Probability.PoissonReferenceSeparation
public import PaperP1.Model.MeanBiasQuantization
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Asymptotics.FiniteChannelHierarchyBounds
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # The actual cost of changing only the exact run mean to the nominal mean

The upper bound is unconditional. The lower bound applies at every scale
where the proved integer mean bias is nonzero. No assertion of infinitely
many such scales is made, and the quadratic coefficient is held fixed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualNominalReferenceComparison

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.FiniteChannelHierarchy

def distance (N L : ℕ) (α : ℝ) : ℝ :=
  ∑' k : ℕ, |(QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1) α -
    QuadraticPoisson.reference (nominalMean N L) α) {k}|

def lowerConstant (C : ℝ) : ℝ :=
  (Real.exp (-(2 * (2 : ℝ) ^ C)) / 2) * ((2 : ℝ) ^ C)⁻¹

theorem lowerConstant_pos (C : ℝ) : 0 < lowerConstant C := by unfold lowerConstant; positivity

theorem actual_mean_nonneg (N L : ℕ) : 0 ≤ countMoment (dyadicBlock N) L 1 := by
  rw [countMoment_one (subset_refl _)]
  exact sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L

theorem finite_upper (N L : ℕ) (α : ℝ) :
    distance N L α ≤ 2 * (1 + 2 * |α|) *
      |countMoment (dyadicBlock N) L 1 - nominalMean N L| := by
  simpa only [distance, sub_self, abs_zero, mul_zero, add_zero] using
    PoissonParameterStability.actual_signed_difference (actual_mean_nonneg N L)
      (by unfold nominalMean; positivity) α α

theorem uniform_upper (C A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ α : ℝ, |α| ≤ A →
      distance N L α ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NB, hNB, hbias⟩ := CriticalActualMean.uniform_nominal_bias C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption
    (2 * (1 + 2 * A) * (2 : ℝ) ^ C) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NB NF, by omega, ?_⟩
  intro N hN L hband α hα
  have hmean := hbias N (by omega) L hband
  change |countMoment (dyadicBlock N) L 1 - nominalMean N L| ≤ _ at hmean
  calc
    _ ≤ 2 * (1 + 2 * |α|) * |countMoment (dyadicBlock N) L 1 - nominalMean N L| := finite_upper N L α
    _ ≤ 2 * (1 + 2 * A) * ((2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε / 2)) := by
      gcongr
    _ = (2 * (1 + 2 * A) * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_nonzero_bias_lower (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      MeanBiasQuantization.bias (dyadicBlock N) L ≠ 0 → ∀ α : ℝ, -1 ≤ α →
      lowerConstant C / N ≤ distance N L α := by
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NM NG, by omega, ?_⟩
  intro N hN L hband hbias α hα
  have hNtwo : 2 ≤ N := by omega
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hmu := (hmean N (by omega) L hband).2
  have hnu : nominalMean N L ≤ 2 * (2 : ℝ) ^ C := by
    have h := (FiniteChannelHierarchyBounds.nominal_bounds hNtwo hband).2
    have hp : 0 ≤ (2 : ℝ) ^ C := by positivity
    linarith only [h, hp]
  have hquant := MeanBiasQuantization.critical_quantum_lower_bound hNtwo hL hband hbias
  change ((2 : ℝ) ^ C)⁻¹ / N ≤ |countMoment (dyadicBlock N) L 1 - nominalMean N L| at hquant
  have hsep := PoissonReferenceSeparation.actual_reference_separation
    (actual_mean_nonneg N L) (by unfold nominalMean; positivity) hmu hnu hα
  change _ ≤ distance N L α at hsep
  calc
    _ = (Real.exp (-(2 * (2 : ℝ) ^ C)) / 2) * (((2 : ℝ) ^ C)⁻¹ / N) := by
      unfold lowerConstant
      ring
    _ ≤ (Real.exp (-(2 * (2 : ℝ) ^ C)) / 2) *
        |countMoment (dyadicBlock N) L 1 - nominalMean N L| :=
      mul_le_mul_of_nonneg_left hquant (by positivity)
    _ ≤ _ := hsep

theorem uniform_two_sided (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ α : ℝ, |α| ≤ 1 →
      distance N L α ≤ (N : ℝ) ^ (-1 + ε) ∧
      (MeanBiasQuantization.bias (dyadicBlock N) L ≠ 0 → lowerConstant C / N ≤ distance N L α) := by
  obtain ⟨NU, hNU, hupper⟩ := uniform_upper C 1 (by norm_num) ε hε
  obtain ⟨ND, hND, hlower⟩ := uniform_nonzero_bias_lower C
  refine ⟨max NU ND, by omega, ?_⟩
  intro N hN L hband α hα
  refine ⟨hupper N (by omega) L hband α hα, ?_⟩
  intro hbias
  exact hlower N (by omega) L hband hbias α (abs_le.mp hα).1

end PaperP1.ActualNominalReferenceComparison
