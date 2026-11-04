module

public import PaperP1.Asymptotics.PositionalOriginalDeletionWeightedUnderInputs
public import PaperP1.Probability.PositionalCovarianceComparison

/-! # Remaining covariances of both actual deleted fields, companion T19.10 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalOriginalCovarianceUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection
  PaperP1.PositionalDeletedFields PaperP1.PositionalFactorialCovariance
  PaperP1.RetainedComponentActivityUnderInputs

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (min (ε / 4) (1 / 5) / 256) (1 / 12)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let G := dyadicBlock N
        let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
        (∑ z ∈ G ×ˢ G, |covariance (onceLaw E G L) z.1 z.2|) +
          (∑ z ∈ G ×ˢ G, |covariance (isolatedLaw E G L) z.1 z.2|) ≤
            (N : ℝ) ^ (-4 / 5 + ε) := by
  let η := min (ε / 4) (1 / 5)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hη1 : η ≤ 1 / 5 := min_le_right _ _
  obtain ⟨p, hp⟩ := PositionalOriginalDeletionWeightedUnderInputs.uniform_bound C η hη
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NW, _hNW, hw⟩ := hp hgeo 2
  obtain ⟨NA, _hNA, ha⟩ := PositionalDeletionTransferUnderInputs.uniform_original_moments 2 C 1 (by norm_num)
  obtain ⟨B, _hB, NU, _hNU, hu⟩ := PositionalBackgroundMoments.uniform_bound 2 C
  obtain ⟨NP, _hNP, hp0⟩ := WeakPairIncidence.full_single_rates_positive C
  let M : ℝ := (2 : ℝ) ^ C
  let K : ℝ := 2 + 2 * M
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * K) (-4 / 5 + η) (ε - η)
    (by linarith only [hε, hηε])
  refine ⟨10 + NW + NA + NU + NP + NF, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  let t := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
  let U := PositionalBernoulliProducts.poisson G t
  let R := (N : ℝ) ^ (-4 / 5 + η)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ht0 (x : ℕ) : 0 ≤ t x := (hp0 N (by omega) L hband (8 * (L + 1) : ℕ) x).le
  have ht (x : ℕ) : t x ≤ (2 ^ L : ℝ)⁻¹ := by
    apply sub_le_self
    unfold PositionalCompoundPoisson.incidence
    apply sum_nonneg
    intro e _he
    split_ifs
    · exact infiniteJointMoment_nonneg L e
    · exact le_rfl
  have hmean : (∑ x ∈ G, t x) ≤ M := by
    calc
      _ ≤ ∑ _x ∈ G, (2 ^ L : ℝ)⁻¹ := sum_le_sum (fun x _hx ↦ ht x)
      _ = (N : ℝ) * (2 ^ L : ℝ)⁻¹ := by rw [sum_const, nsmul_eq_mul, dyadicBlock_card]
      _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) hn.le
      _ = M := by dsimp [M]; field_simp
  have hR0 : 0 ≤ R := Real.rpow_nonneg hn.le _
  have hR1 : R ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hη1] : (-4 / 5 : ℝ) + η ≤ 0)
    simpa only [Real.rpow_zero] using hh
  have hK : 0 ≤ K := by dsimp only [K, M]; positivity
  have hU := hu N (by omega) L hband (8 * (L + 1) : ℕ)
  have hA := ha N (by omega) L hband G Subset.rfl E
  have hW := hw N (by omega) L hband
  have hcov (ν : Space ℕ) (hν : ∀ v, 0 ≤ coeff v ν)
      (hsν : Summable (fun v ↦ coeff v ν * (1 + (totalCount v : ℝ)) ^ 2))
      (hd : Summable (fun v ↦ (1 + (totalCount v : ℝ)) ^ 2 * |coeff v ν - coeff v U|) ∧
        (∑' v, (1 + (totalCount v : ℝ)) ^ 2 * |coeff v ν - coeff v U|) ≤ R) :
      (∑ z ∈ G ×ˢ G, |covariance ν z.1 z.2|) ≤ K * R := by
    let D := ∑' v, |coeff v ν - coeff v U| * weight v
    have hsd : Summable (fun v ↦ |coeff v ν - coeff v U| * weight v) := by
      simpa only [weight, mul_comm] using hd.1
    have hD : D ≤ R := by simpa only [D, weight, mul_comm] using hd.2
    have hh := PositionalCovarianceComparison.poisson_bound G ν t hν (fun x _hx ↦ ht0 x)
      hsν hU.2.1 hsd
    apply hh.trans
    apply mul_le_mul
    · change 1 + 2 * (∑ x ∈ G, t x) + D ≤ K
      dsimp only [K]
      linarith only [hmean, hD.trans hR1]
    · exact hD
    · exact tsum_nonneg (fun v ↦ mul_nonneg (abs_nonneg _) (by dsimp [weight]; positivity))
    · exact hK
  have hOnce := hcov (onceLaw E G L) (onceLaw_isProbability E G L).1 hA.1.1 hW.1
  have hIsolated := hcov (isolatedLaw E G L) (isolatedLaw_isProbability E G L).1 hA.2.1 hW.2
  have hfactor : 2 * K * R ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  exact (add_le_add hOnce hIsolated).trans (by nlinarith only [hfactor])

end PaperP1.PositionalOriginalCovarianceUnderInputs
