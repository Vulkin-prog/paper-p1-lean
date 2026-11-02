module

public import PaperP1.Model.FreshFactorialLower
public import PaperP1.Asymptotics.ConditionalNegativeDeviation
public import PaperP1.Asymptotics.FiniteChannelHierarchyBounds
public import PaperP1.Algebra.NonnegativePowerDifference

/-! # An unconditional lower estimate for every fixed actual factorial moment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedFactorialLower

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.SourceConditionalDeviations PaperP1.FiniteChannelHierarchy

theorem uniform_lower_power (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (max 0 (nominalMean N L - (N : ℝ) ^ (-1 / 2 + ε))) ^ r ≤
        factorialCountMoment (dyadicBlock N) L r := by
  obtain ⟨N₀, hN₀, hmean⟩ := ConditionalNegativeDeviation.uniform_mean_lower C r ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  apply FreshFactorialLower.factorial_lower_power N L r _ (le_max_left _ _)
  intro q hq A hA hcard hpos
  apply max_le
  · exact sum_nonneg fun z _ ↦ conditional_nonneg A L z
  · exact hmean N hN L hband A hA (by omega) hpos

theorem uniform_lower_error (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      nominalMean N L ^ r - factorialCountMoment (dyadicBlock N) L r ≤
        (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NP, _hNP, hpower⟩ := uniform_lower_power r C (ε / 2) (by positivity)
  let D : ℝ := r * ((2 : ℝ) ^ C) ^ (r - 1)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption D (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NP NF), by omega, ?_⟩
  intro N hN L hband
  let a := nominalMean N L
  let δ := (N : ℝ) ^ (-1 / 2 + ε / 2)
  let b := max 0 (a - δ)
  have ha : 0 ≤ a := by dsimp [a, nominalMean]; positivity
  have hδ : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hb : 0 ≤ b := le_max_left _ _
  have hba : b ≤ a := max_le ha (sub_le_self _ hδ)
  have haM : a ≤ (2 : ℝ) ^ C := (FiniteChannelHierarchyBounds.nominal_bounds (by omega) hband).2
  have hab : |a - b| ≤ δ := by rw [abs_of_nonneg (sub_nonneg.mpr hba)]; have h := le_max_right 0 (a - δ); dsimp [b]; linarith
  have hp := NonnegativePowerDifference.bound a b ((2 : ℝ) ^ C) ha hb haM (hba.trans haM) r
  have hconst : |a - b| * r * ((2 : ℝ) ^ C) ^ (r - 1) ≤ D * δ := by
    have h := mul_le_mul_of_nonneg_right hab (by positivity : 0 ≤ (r : ℝ) * ((2 : ℝ) ^ C) ^ (r - 1))
    dsimp [D]
    nlinarith only [h]
  calc
    _ ≤ a ^ r - b ^ r := sub_le_sub_left (hpower N (by omega) L hband) _
    _ ≤ |a ^ r - b ^ r| := le_abs_self _
    _ ≤ D * δ := hp.trans hconst
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FixedFactorialLower
