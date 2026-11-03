module

public import PaperP1.Model.SecondFactorialCorrection
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase

/-! # The nominal second factorial correction has an unconditional positive two-thirds-scale lower bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondFactorialCorrectionLower

open Finset PaperP1.Model PaperP1.CountObservables PaperP1.FiniteChannelHierarchy
  PaperP1.SecondFactorialCorrection

theorem uniform_gap (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |value N L - RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L| ≤ (N : ℝ) ^ (-1 + ε) := by
  let A := (2 : ℝ) ^ C
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨NB, _hNB, hb⟩ := CriticalActualMean.uniform_nominal_bias C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (3 * A ^ 2) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NB + NM + NF, by omega, ?_⟩
  intro N hN L hband
  let μ := countMoment (dyadicBlock N) L 1
  let ν := nominalMean N L
  have hμ : 0 ≤ μ := by
    change 0 ≤ countMoment (dyadicBlock N) L 1
    rw [countMoment_one Subset.rfl]
    exact sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hν : 0 ≤ ν := by dsimp [ν, nominalMean]; positivity
  have hμcap : μ ≤ 2 * A := (hm N (by omega) L hband).2
  have hνcap : ν ≤ A := by
    have h := LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hband
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simpa only [ν, nominalMean, A, mul_comm] using (le_div_iff₀ hn).mp h
  have hdiff : |μ - ν| ≤ A * (N : ℝ) ^ (-1 + ε / 2) := hb N (by omega) L hband
  calc
    _ = |(μ - ν) * (μ + ν)| := by rw [gap_identity]; congr 1; dsimp [μ, ν]; ring
    _ = |μ - ν| * (μ + ν) := by rw [abs_mul, abs_of_nonneg (add_nonneg hμ hν)]
    _ ≤ (A * (N : ℝ) ^ (-1 + ε / 2)) * (3 * A) :=
      mul_le_mul hdiff (by linarith only [hμcap, hνcap]) (add_nonneg hμ hν) (by positivity)
    _ = (3 * A ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_lower (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → c * L * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ value N L := by
  obtain ⟨c, _k, hc, _hk, NP, _hNP, hp⟩ := PrincipalChannelEdgesPhase.positive_phase C 8
  obtain ⟨NK, _hNK, hk⟩ := PrincipalChannelEdgesPhase.uniform_cumulant_upper_error C (1 / 12) (by norm_num)
  obtain ⟨NA, _hNA, ha⟩ := uniform_gap C (1 / 12) (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 / c) (-11 / 12) (1 / 4) (by norm_num)
  refine ⟨c, hc, 3 + NP + NK + NA + NG + NF, by omega, ?_⟩
  intro N hN L hband
  have hL : 1 ≤ L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hphase := (hp N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl).1
  have hcum := hk N (by omega) L (8 * (L + 1)) hband
  have hgap := (abs_le.mp (ha N (by omega) L hband)).1
  have hsmall : 2 * (N : ℝ) ^ (-11 / 12 : ℝ) ≤ c * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hf N (by omega)) hc.le
    rw [show (-11 / 12 : ℝ) + 1 / 4 = -2 / 3 by ring] at h
    have heq : c * (2 / c * (N : ℝ) ^ (-11 / 12 : ℝ)) = 2 * (N : ℝ) ^ (-11 / 12 : ℝ) := by field_simp
    rw [heq] at h
    apply h.trans
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLR hc.le)
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-2 / 3 : ℝ))
    simpa only [mul_one] using hmul
  norm_num only [show -(1 : ℝ) + 1 / 12 = -11 / 12 by ring] at hcum hgap
  linarith only [hphase, hcum, hgap, hsmall]

end PaperP1.SecondFactorialCorrectionLower
