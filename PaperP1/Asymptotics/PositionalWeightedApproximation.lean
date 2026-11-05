module

public import PaperP1.Asymptotics.PositionalFullApproximation
public import PaperP1.Asymptotics.PositionalMomentBounds
public import PaperP1.Probability.PolynomialWeightTransfer

/-! # Every fixed polynomial weight for the full original positional comparison

The unweighted arithmetic estimate is proved before the polynomial degree. Higher
original moments are only required to be subpolynomial, never exponential.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalWeightedApproximation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CompletedPositionalLaw
  PaperP1.PositionalFiniteLaw PaperP1.PositionalCountProjection
  PaperP1.RetainedComponentActivity

theorem uniform_coefficient_bound (C ε : ℝ) (hε : 0 < ε) :
    ∀ j : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let T := PositionalCompoundPoisson.target (dyadicBlock N)
          (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        Summable (fun v : Configuration ℕ ↦ (1 + (totalCount v : ℝ)) ^ j *
          |(PositionalStoppedLaw.actualLaw (dyadicBlock N) L).coeff v - coeff v T|) ∧
        (∑' v : Configuration ℕ, (1 + (totalCount v : ℝ)) ^ j *
          |(PositionalStoppedLaw.actualLaw (dyadicBlock N) L).coeff v - coeff v T|) ≤
            (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NN, _hNN, hh⟩ := PositionalFullApproximation.uniform_norm_bound
    C (ε / 4) (by positivity)
  intro j
  let δ : ℝ := ε / (4 * (j + 1 : ℕ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδj : δ * (j : ℝ) ≤ ε / 4 := by
    have hd : 0 < (j + 1 : ℕ) := by positivity
    have he : δ * ((j + 1 : ℕ) : ℝ) = ε / 4 := by dsimp [δ]; field_simp
    have hmono : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
    exact (mul_le_mul_of_nonneg_left hmono hδ.le).trans_eq he
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / δ)
  have hδq : 1 ≤ δ * (q : ℝ) := by
    have hhq := (div_lt_iff₀ hδ).mp hq
    linarith only [hhq]
  obtain ⟨NA, _hNA, ha⟩ := PositionalMomentBounds.uniform_original (j + q) C (ε / 4) (by positivity)
  obtain ⟨B, _hB, NT, _hNT, ht⟩ := PositionalMomentBounds.uniform_reference (j + q) C
  obtain ⟨NB, hb⟩ := HalfCountSchedule.factor_absorption B 0 (ε / 4) (by positivity)
  obtain ⟨NP, _hNP, hprob⟩ := WeakPairIncidence.full_target_isProbability C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NN + NA + NT + NB + NP + NF, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let A := ofFinite (PositionalStoppedLaw.actualLaw (dyadicBlock N) L)
  let T := PositionalCompoundPoisson.target (dyadicBlock N)
    (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  let a := fun v : Configuration ℕ ↦ coeff v A
  let b := fun v : Configuration ℕ ↦ coeff v T
  let w := fun v : Configuration ℕ ↦ 1 + (totalCount v : ℝ)
  let R := (N : ℝ) ^ δ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 0 < R := Real.rpow_pos_of_pos hn δ
  have hw (v : Configuration ℕ) : 1 ≤ w v := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have ha0 (v : Configuration ℕ) : 0 ≤ a v := by
    simpa only [a, A, coeff_ofFinite] using PositionalStoppedLaw.actualLaw_nonneg (dyadicBlock N) L v
  have hb0 : ∀ v : Configuration ℕ, 0 ≤ b v :=
    (hprob N (by omega) L hband (8 * (L + 1) : ℕ)).1
  have hma := ha N (by omega) L hband (dyadicBlock N) Subset.rfl
  have hmt := ht N (by omega) L hband (8 * (L + 1) : ℕ)
  have hBbound : B ≤ (N : ℝ) ^ (ε / 4) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hb N (by omega)
  have hsa : Summable (fun v ↦ w v ^ (j + q) * a v) := by
    simpa only [a, A, w, coeff_ofFinite, mul_comm] using hma.1
  have hsb : Summable (fun v ↦ w v ^ (j + q) * b v) := by
    simpa only [b, T, w, mul_comm] using hmt.1
  have hMa : (∑' v, w v ^ (j + q) * a v) ≤ (N : ℝ) ^ (ε / 4) := by
    simpa only [a, A, w, coeff_ofFinite, mul_comm] using hma.2
  have hMb : (∑' v, w v ^ (j + q) * b v) ≤ (N : ℝ) ^ (ε / 4) := by
    have hhB := hmt.2.trans hBbound
    simpa only [b, T, w, mul_comm] using hhB
  have hs0 : Summable (fun v ↦ |a v - b v|) := by
    simpa only [a, b, map_sub] using summable_abs_coeff (A - T)
  have hnorm : (∑' v, |a v - b v|) ≤ (N : ℝ) ^ (-4 / 5 + ε / 4) := by
    have hm := hh N (by omega) L hband
    rw [PositionalCoefficientExpansion.norm_eq_tsum_abs_coeff] at hm
    simpa only [a, b, A, T, map_sub] using hm
  have hs := PolynomialWeightTransfer.summable_weighted_error w a b hw ha0 hb0 j q hsa hsb
  have hcut := PolynomialWeightTransfer.cutoff_bound w a b hw ha0 hb0 j q R hR hs0 hsa hsb
  have hsmall : R ^ j * (∑' v, |a v - b v|) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    calc
      _ ≤ R ^ j * (N : ℝ) ^ (-4 / 5 + ε / 4) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg hR.le j)
      _ = (N : ℝ) ^ (δ * (j : ℝ) + (-4 / 5 + ε / 4)) := by
        dsimp only [R]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδj])
  have htail : (R ^ q)⁻¹ * ((∑' v, w v ^ (j + q) * a v) +
      ∑' v, w v ^ (j + q) * b v) ≤ 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    calc
      _ ≤ (R ^ q)⁻¹ * (2 * (N : ℝ) ^ (ε / 4)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hMa, hMb]) (by positivity)
      _ = 2 * (N : ℝ) ^ (-(δ * (q : ℝ)) + ε / 4) := by
        dsimp only [R]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_neg hn.le]
        rw [mul_left_comm, ← Real.rpow_add hn]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδq, hε])) (by norm_num)
  have hfinal : (∑' v, w v ^ j * |a v - b v|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    have hfactor : 3 * (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
      convert hf N (by omega) using 1
      congr 1
      ring
    linarith only [hcut, hsmall, htail, hfactor]
  simpa only [a, A, b, T, w, coeff_ofFinite] using And.intro hs hfinal

theorem uniform_probability_bound (C ε : ℝ) (hε : 0 < ε) :
    ∀ j : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let T := PositionalCompoundPoisson.target (dyadicBlock N)
          (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        PositivePositionalConvolution.IsProbability T ∧
        (∑' v : Configuration ℕ, (1 + (totalCount v : ℝ)) ^ j *
          |Model.InfiniteRademacher.infiniteRademacherMeasure.real
              {ω | configuration (dyadicBlock N) (fun x ↦ infiniteStartIndicator x L) ω = v} -
            coeff v T|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  have hp := uniform_coefficient_bound C ε hε
  obtain ⟨NP, _hNP, hprob⟩ := WeakPairIncidence.full_target_isProbability C
  intro j
  obtain ⟨NN, _hNN, hh⟩ := hp j
  refine ⟨10 + NP + NN, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  refine ⟨hprob N (by omega) L hband (8 * (L + 1) : ℕ), ?_⟩
  simpa only [PositionalStoppedLaw.actualLaw_coeff] using (hh N (by omega) L hband).2

end PaperP1.PositionalWeightedApproximation
