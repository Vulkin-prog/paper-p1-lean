module

public import PaperP1.Asymptotics.PositiveQuarticObstruction
public import PaperP1.Asymptotics.FixedCountMomentBounds
public import PaperP1.Asymptotics.PairActivity
public import PaperP1.Model.FourthCharlierLawDistance

/-! # The optimal-power lower bound for the actual quadratic signed approximation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticLawLowerBound

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum
  PaperP1.FourthRunFactorialCumulant

theorem article_16_2_lower (C ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      c * (N : ℝ) ^ (-4 / 3 - ε) ≤
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (actualMean (dyadicBlock N) L)
            (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)) := by
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let r := 4 + ⌈(7 / 3 : ℝ) / δ⌉₊
  have hr : 4 ≤ r := by dsimp [r]; omega
  have htail : (7 / 3 : ℝ) ≤ δ * (r - 4 : ℕ) := by
    have hc := Nat.le_ceil ((7 / 3 : ℝ) / δ)
    have heq : r - 4 = ⌈(7 / 3 : ℝ) / δ⌉₊ := by dsimp [r]; omega
    rw [heq]
    have h := mul_le_mul_of_nonneg_left hc hδ.le
    have he : δ * ((7 / 3 : ℝ) / δ) = 7 / 3 := by field_simp
    rw [he] at h
    exact h
  let M := max 1 (2 * (2 : ℝ) ^ C)
  let K := (1 + M) ^ 4
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨d, hd, NQ, _hNQ, hquartic⟩ := PositiveQuarticObstruction.uniform_lower C
  obtain ⟨BM, hBM, NP, _hNP, hmoment⟩ := FixedCountMomentBounds.uniform_ordinary_bound r C
  obtain ⟨NA, _hNA, halpha⟩ := PairActivity.uniform_cumulant C (1 / 6) (by norm_num)
  obtain ⟨BQ, hBQ, hreference⟩ := PoissonPolynomialMoments.uniform_absolute_moment M hM r
  obtain ⟨NM, _hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let J := (2 : ℝ) ^ r * (1 + BM) + BQ
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * K * J / d) (-7 / 3) 1 (by norm_num)
  refine ⟨d / (2 * K), by positivity, max 2 (max NQ (max NP (max NA (max NM (max NL NF))))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hl N (by omega) L hband).2.2.1; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  let μ := actualMean (dyadicBlock N) L
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let E := fourthFactorialCumulant (dyadicBlock N) L + 3 * α ^ 2
  let D := SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
    (QuadraticPoisson.reference μ α)
  let R := (N : ℝ) ^ δ
  have hR : 1 ≤ R := Real.one_le_rpow hn1 hδ.le
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : μ ≤ M := by
    have h := (hmean N (by omega) L hband).2
    rw [countMoment_one (subset_refl (dyadicBlock N))] at h
    exact h.trans (le_max_right _ _)
  have hα : |α| ≤ 1 := by
    have h := halpha N (by omega) L hband (dyadicBlock N) (subset_refl _)
    apply h.trans
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-2 / 3 : ℝ) + 1 / 6 ≤ 0)).trans_eq (Real.rpow_zero _)
  obtain ⟨hqs, hqb⟩ := hreference μ α hμ hμM hα
  have htest := FourthCharlierLawDistance.finite_bound (L := L) (subset_refl (dyadicBlock N)) r hr M R BQ hμM hR hqs hqb
  have hmomentB := hmoment N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have htest' : |E| ≤ K * R ^ 4 * D + K / R ^ (r - 4) * J := by
    apply htest.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (by dsimp [J]; gcongr) (by positivity))
  have htailPower : K / R ^ (r - 4) * J ≤ K * J * (N : ℝ) ^ (-7 / 3 : ℝ) := by
    calc
      _ = K * J * (N : ℝ) ^ (-(δ * (r - 4 : ℕ))) := by
        rw [Real.rpow_neg hn.le, Real.rpow_mul_natCast hn.le]
        dsimp only [R]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [htail])) (mul_nonneg hK.le hJ)
  have htailSmall : K / R ^ (r - 4) * J ≤ (d / 2) * (N : ℝ) ^ (-4 / 3 : ℝ) := by
    have h := hf N (by omega)
    rw [show (-7 / 3 : ℝ) + 1 = -4 / 3 by ring] at h
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ d / 2)
    have heq : d / 2 * ((2 * K * J / d) * (N : ℝ) ^ (-7 / 3 : ℝ)) =
        K * J * (N : ℝ) ^ (-7 / 3 : ℝ) := by field_simp
    rw [heq] at hmul
    exact htailPower.trans hmul
  have hpositive := (hquartic N (by omega) L hband).2
  have hbase : d * (N : ℝ) ^ (-4 / 3 : ℝ) ≤ E := by
    have hLsq : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    have h := mul_le_mul_of_nonneg_right hLsq (mul_nonneg hd.le (Real.rpow_nonneg hn.le (-4 / 3)))
    nlinarith only [hpositive, h]
  have hmain : d / 2 * (N : ℝ) ^ (-4 / 3 : ℝ) ≤ K * R ^ 4 * D := by
    linarith only [hbase, htest', htailSmall, le_abs_self E]
  have hRfour : R ^ 4 = (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    dsimp [δ]
    ring
  have hcancel : (K * R ^ 4) * (d / (2 * K) * (N : ℝ) ^ (-4 / 3 - ε / 2)) =
      d / 2 * (N : ℝ) ^ (-4 / 3 : ℝ) := by
    rw [hRfour]
    have hc : K * (d / (2 * K)) = d / 2 := by field_simp
    calc
      _ = (K * (d / (2 * K))) * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-4 / 3 - ε / 2)) := by ring
      _ = _ := by
        rw [hc, ← Real.rpow_add hn, show ε / 2 + (-4 / 3 - ε / 2) = (-4 / 3 : ℝ) by ring]
  have hlower : d / (2 * K) * (N : ℝ) ^ (-4 / 3 - ε / 2) ≤ D := by
    apply (mul_le_mul_iff_left₀ (mul_pos hK (pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR) 4))).mp
    rw [mul_comm (d / (2 * K) * (N : ℝ) ^ (-4 / 3 - ε / 2)) (K * R ^ 4), hcancel,
      mul_comm D (K * R ^ 4)]
    exact hmain
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))
    (by positivity : 0 ≤ d / (2 * K))).trans hlower

end PaperP1.QuadraticLawLowerBound
