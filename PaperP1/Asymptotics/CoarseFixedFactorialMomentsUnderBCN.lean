module

public import PaperP1.Asymptotics.FixedCountMomentBoundsUnderBCN
public import PaperP1.Asymptotics.FixedFactorialLower

/-! # Two-sided fixed factorial-moment convergence under explicit BCN

The exact original count is compared with powers of its exact actual mean,
with a coarse N^(-1/2+epsilon) error. The quadratic correction and source
N^(-4/5+epsilon) remainder are not claimed here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseFixedFactorialMomentsUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum PaperP1.FiniteChannelHierarchy

theorem uniform_power_mean_bias (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |actualMean (dyadicBlock N) L ^ r - nominalMean N L ^ r| ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NB, _hNB, hbias⟩ := CriticalActualMean.uniform_nominal_bias C (ε / 2) (by positivity)
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let D : ℝ := (2 : ℝ) ^ C * r * M ^ (r - 1)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption D (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NB (max NM NF), by omega, ?_⟩
  intro N hN L hband
  have hμ : 0 ≤ actualMean (dyadicBlock N) L :=
    sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hnom : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hμM : actualMean (dyadicBlock N) L ≤ M := by
    rw [actualMean_eq_countMoment (subset_refl _)]
    exact (hmean N (by omega) L hband).2
  have hnomM : nominalMean N L ≤ M := by
    have h := (FiniteChannelHierarchyBounds.nominal_bounds (by omega) hband).2
    have hpos : 0 < (2 : ℝ) ^ C := Real.rpow_pos_of_pos (by norm_num) _
    dsimp [M]
    linarith
  have hb : |actualMean (dyadicBlock N) L - nominalMean N L| ≤
      (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε / 2) := by
    simpa only [actualMean_eq_countMoment (subset_refl _), nominalMean] using hbias N (by omega) L hband
  calc
    _ ≤ |actualMean (dyadicBlock N) L - nominalMean N L| * r * M ^ (r - 1) :=
      NonnegativePowerDifference.bound _ _ M hμ hnom hμM hnomM r
    _ ≤ D * (N : ℝ) ^ (-1 + ε / 2) := by
      have h := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (r : ℝ) * M ^ (r - 1))
      dsimp [D]
      nlinarith only [h]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_nominal_error (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |factorialCountMoment (dyadicBlock N) L r - nominalMean N L ^ r| ≤
        (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NU, _hNU, hupper⟩ := FixedCountMomentBoundsUnderBCN.uniform_factorial_upper r c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NL, _hNL, hlower⟩ := FixedFactorialLower.uniform_lower_error r C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbias⟩ := uniform_power_mean_bias r C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 2 (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NU (max NL (max NB NF))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let T := (N : ℝ) ^ (-1 / 2 + ε / 2)
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hu := hupper N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hl := hlower N (by omega) L hband
  have hb : |actualMean (dyadicBlock N) L ^ r - nominalMean N L ^ r| ≤ T :=
    (hbias N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have ha : |factorialCountMoment (dyadicBlock N) L r - nominalMean N L ^ r| ≤ 2 * T := by
    dsimp only [T] at *
    apply abs_le.mpr
    have h := le_abs_self (actualMean (dyadicBlock N) L ^ r - nominalMean N L ^ r)
    constructor <;> linarith only [hu, hl, hb, hT, h]
  calc
    _ ≤ 2 * T := ha
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_actual_error (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |factorialCountMoment (dyadicBlock N) L r - actualMean (dyadicBlock N) L ^ r| ≤
        (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NN, _hNN, hnominal⟩ := uniform_nominal_error r c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbias⟩ := uniform_power_mean_bias r C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 2 (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NN (max NB NF)), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hb : |nominalMean N L ^ r - actualMean (dyadicBlock N) L ^ r| ≤
      (N : ℝ) ^ (-1 / 2 + ε / 2) := by
    rw [abs_sub_comm]
    exact (hbias N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  calc
    _ ≤ |factorialCountMoment (dyadicBlock N) L r - nominalMean N L ^ r| +
        |nominalMean N L ^ r - actualMean (dyadicBlock N) L ^ r| := abs_sub_le _ _ _
    _ ≤ (N : ℝ) ^ (-1 / 2 + ε / 2) + (N : ℝ) ^ (-1 / 2 + ε / 2) :=
      add_le_add (hnominal N (by omega) L hband) hb
    _ = 2 * (N : ℝ) ^ (-1 / 2 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.CoarseFixedFactorialMomentsUnderBCN
