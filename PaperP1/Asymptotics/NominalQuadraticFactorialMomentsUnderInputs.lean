module

public import PaperP1.Asymptotics.FixedMomentInputs
public import PaperP1.Asymptotics.FinitePairActivityInputs
public import PaperP1.Asymptotics.CoarseFixedFactorialMomentsUnderBCN
public import PaperP1.Model.SecondFactorialCorrection

/-! # The optional nominal-parameter fixed factorial correction has the same stronger remainder exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NominalQuadraticFactorialMomentsUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum PaperP1.FiniteChannelHierarchy

theorem uniform_fixed (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FixedMomentInputs.Parameters r, ∃ pa : FinitePairDeficitInputs.Parameters,
      FixedMomentInputs.Hypotheses p (ε / 4) →
      FinitePairDeficitInputs.Hypotheses pa (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |factorialCountMoment (dyadicBlock N) L r - nominalMean N L ^ r -
          (r.choose 2 : ℝ) * nominalMean N L ^ (r - 2) * SecondFactorialCorrection.value N L| ≤
            (N : ℝ) ^ (-1 + ε) := by
  let M := max 1 ((2 : ℝ) ^ C)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let D := 2 + (r.choose 2 : ℝ) * (1 + M ^ (r - 2))
  obtain ⟨p, hp⟩ := FixedMomentInputs.uniform_fixed r hr C (ε / 4) (by positivity)
  obtain ⟨pa, ha⟩ := FinitePairActivityInputs.uniform_cumulant C (1 / 6) (by norm_num)
  obtain ⟨NR, _hNR, hR⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_power_mean_bias r C (ε / 4) (by positivity)
  obtain ⟨NK, _hNK, hK⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_power_mean_bias (r - 2) C (ε / 4) (by positivity)
  obtain ⟨N2, _hN2, h2⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_power_mean_bias 2 C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption D (-1 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨p, pa, ?_⟩
  intro hgeo hgeoA
  obtain ⟨NE, _hNE, he⟩ := hp hgeo
  obtain ⟨NA, _hNA, ha⟩ := ha hgeoA
  refine ⟨10 + NR + NK + N2 + NF + NE + NA, by omega, ?_⟩
  intro N hN L hband
  let G := dyadicBlock N
  let μ := actualMean G L
  let ν := nominalMean N L
  let a := RegularCumulantTransfer.secondFactorialCumulant G L
  let b := SecondFactorialCorrection.value N L
  let T := (N : ℝ) ^ (-1 + ε / 4)
  let E := factorialCountMoment G L r - μ ^ r - (r.choose 2 : ℝ) * μ ^ (r - 2) * a
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hν : 0 ≤ ν := by dsimp only [ν, nominalMean]; positivity
  have hνM : ν ≤ M := (FiniteChannelHierarchyBounds.nominal_bounds (by omega) hband).2.trans (le_max_right _ _)
  have hνpow : ν ^ (r - 2) ≤ M ^ (r - 2) := pow_le_pow_left₀ hν hνM _
  have hpow : (N : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have haone : |a| ≤ 1 := by
    have h := ha N (by omega) L hband G Subset.rfl
    norm_num only [show (-2 / 3 : ℝ) + 1 / 6 = -1 / 2 by ring] at h
    exact h.trans (by simpa only [neg_div] using hpow)
  have hE : |E| ≤ T := he N (by omega) L hband G Subset.rfl
  have hR' : |μ ^ r - ν ^ r| ≤ T := hR N (by omega) L hband
  have hK' : |μ ^ (r - 2) - ν ^ (r - 2)| ≤ T := hK N (by omega) L hband
  have hab : |a - b| ≤ T := by
    have hgap := SecondFactorialCorrection.gap_identity N L
    change b - a = countMoment G L 1 ^ 2 - ν ^ 2 at hgap
    rw [← actualMean_eq_countMoment Subset.rfl] at hgap
    change b - a = μ ^ 2 - ν ^ 2 at hgap
    rw [abs_sub_comm, hgap]
    exact h2 N (by omega) L hband
  have hid : factorialCountMoment G L r - ν ^ r - (r.choose 2 : ℝ) * ν ^ (r - 2) * b =
      E + (μ ^ r - ν ^ r) + (r.choose 2 : ℝ) *
        ((μ ^ (r - 2) - ν ^ (r - 2)) * a + ν ^ (r - 2) * (a - b)) := by
    dsimp only [E]
    ring
  have hfirst : |(μ ^ (r - 2) - ν ^ (r - 2)) * a| ≤ T := by
    rw [abs_mul]
    exact (mul_le_mul hK' haone (abs_nonneg a) hT).trans_eq (mul_one T)
  have hsecond : |ν ^ (r - 2) * (a - b)| ≤ M ^ (r - 2) * T := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hν _)]
    exact mul_le_mul hνpow hab (abs_nonneg _) (pow_nonneg hM _)
  have hcorr : |(r.choose 2 : ℝ) *
      ((μ ^ (r - 2) - ν ^ (r - 2)) * a + ν ^ (r - 2) * (a - b))| ≤
      (r.choose 2 : ℝ) * (T + M ^ (r - 2) * T) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hfirst hsecond)) (Nat.cast_nonneg _)
  calc
    _ = |E + (μ ^ r - ν ^ r) + (r.choose 2 : ℝ) *
        ((μ ^ (r - 2) - ν ^ (r - 2)) * a + ν ^ (r - 2) * (a - b))| := congrArg abs hid
    _ ≤ |E| + |μ ^ r - ν ^ r| + |(r.choose 2 : ℝ) *
        ((μ ^ (r - 2) - ν ^ (r - 2)) * a + ν ^ (r - 2) * (a - b))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ T + T + (r.choose 2 : ℝ) * (T + M ^ (r - 2) * T) := add_le_add (add_le_add hE hR') hcorr
    _ = D * T := by dsimp only [D]; ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 4) + 3 * ε / 4) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.NominalQuadraticFactorialMomentsUnderInputs
