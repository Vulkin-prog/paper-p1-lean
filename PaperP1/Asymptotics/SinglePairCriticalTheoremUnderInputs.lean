module

public import PaperP1.Asymptotics.PrincipalSelectedPairMassUnderInputs
public import PaperP1.Asymptotics.CriticalFreshBranchingLog
public import PaperP1.Model.CountVariance

/-! # Complete companion T22.5: one actual good pair at every critical order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SinglePairCriticalTheoremUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.Model.InfiniteRademacher PaperP1.PrincipalSelectedPairMassUnderInputs
  PaperP1.CriticalFreshBranchingBudget

theorem mean_eq_integral (N L : ℕ) : mean N L =
    ∫ ω, (infiniteStartCount (dyadicBlock N) L ω : ℝ) ∂infiniteRademacherMeasure := by
  simp only [mean, countMoment, pow_one]

theorem alpha_eq_variance (N L : ℕ) : alpha N L =
    ProbabilityTheory.variance (fun ω ↦ (infiniteStartCount (dyadicBlock N) L ω : ℝ)) infiniteRademacherMeasure -
      ∫ ω, (infiniteStartCount (dyadicBlock N) L ω : ℝ) ∂infiniteRademacherMeasure :=
  CountVariance.second_cumulant_variance (dyadicBlock N) L

theorem selected_family_positive {N H L k : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    ∀ x ∈ SelectedPairBranchingTuples.families (dyadicBlock N) (PrincipalChannelEdges.edges N H L) N L k,
      Function.Injective x ∧ FiniteFamilyEnumeration.tupleSet x ⊆ dyadicBlock N ∧
        0 < infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet x) := by
  apply SelectedPairBranchingTuples.family_data hN hL Subset.rfl
  intro e he
  rcases mem_union.mp he with he | he
  · exact (mem_filter.mp he).2
  · exact (mem_filter.mp he).2


theorem companion_T22_5 (C : ℝ) (D : ℕ) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∀ K : ℝ, 0 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀,
        0 < freshEnvelope K N ∧
        Real.log (freshEnvelope K N) ≤ 2 / 3 * Real.log N -
          Real.log N * Real.log (Real.log (Real.log N)) / (9 * Real.log (Real.log N)) +
            c * (Real.log N / Real.log (Real.log N)) ∧
        ∀ m : ℕ, 2 ≤ m → (m : ℝ) ≤ orderCap K N → ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
          weightedError N H L m ≤ η * SecondFactorialCorrection.value N L ∧
          ∀ r : ℕ, 2 ≤ r → r ≤ m →
            |selected N H L r - (r.choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ (r - 2) * amplitude N H L| ≤
            ((r.choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ (r - 2) * amplitude N H L) *
              (((r - 2 : ℕ) : ℝ) * freshEnvelope K N / N) := by
  obtain ⟨p, hp⟩ := uniform_weighted C D
  refine ⟨p, ?_⟩
  intro hgeo K hK
  obtain ⟨c, hc, NC, _hNC, hlog⟩ := CriticalFreshBranchingLog.fresh_log_upper K hK
  obtain ⟨NW, _hNW, hw⟩ := hp hgeo K hK
  obtain ⟨NF, _hNF, hf⟩ := uniform_first K C hK
  obtain ⟨a, ha, NA, _hNA, hlower⟩ := SecondFactorialCorrectionLower.uniform_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨c, hc, ?_⟩
  intro η hη
  obtain ⟨NX, hx⟩ := HalfCountSchedule.factor_absorption (1 / (η * a)) (-3 / 4) (1 / 12) (by norm_num)
  refine ⟨10 + NC + NW + NF + NA + NG + NX, by omega, ?_⟩
  intro N hN
  refine ⟨freshEnvelope_pos K N, hlog N (by omega), ?_⟩
  intro m hm horder L H hband hcut hH
  have hL : (1 : ℝ) ≤ L := by
    have hh := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (show 1 ≤ L by omega)
  have haN : a * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ SecondFactorialCorrection.value N L := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL ha.le)
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-2 / 3 : ℝ))
    have hbase : a * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ a * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
      simpa only [mul_one] using hh
    exact hbase.trans (hlower N (by omega) L hband)
  have hsmall : (N : ℝ) ^ (-3 / 4 : ℝ) / (η * a) ≤ (N : ℝ) ^ (-2 / 3 : ℝ) := by
    have hh := hx N (by omega)
    rw [show (-3 / 4 : ℝ) + 1 / 12 = -2 / 3 by norm_num] at hh
    simpa [div_eq_mul_inv, mul_comm] using hh
  have hraw : (N : ℝ) ^ (-3 / 4 : ℝ) ≤ η * (a * (N : ℝ) ^ (-2 / 3 : ℝ)) := by
    have hh := (div_le_iff₀ (mul_pos hη ha)).mp hsmall
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  exact ⟨(hw N (by omega) m hm horder L H hband hcut hH).trans
      (hraw.trans (mul_le_mul_of_nonneg_left haN hη.le)),
    hf N (by omega) m hm horder L H hband⟩

end PaperP1.SinglePairCriticalTheoremUnderInputs
