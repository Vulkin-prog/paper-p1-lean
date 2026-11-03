module

public import PaperP1.Asymptotics.RetainedBinomialApproximationUnderInputs
public import PaperP1.Asymptotics.RetainedBetaCovarianceUnderInputs
public import PaperP1.Asymptotics.RegularQuadraticReferenceRestoration
public import PaperP1.Asymptotics.PoissonCharlierConversion

/-! # Companion T17.5: the first actual quadratic approximation, at both actual and nominal means -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstQuadraticApproximationUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.SecondFactorialCorrection

structure Parameters where
  binomial : RetainedComponentActivityUnderInputs.Parameters
  beta : FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  binomial : RetainedComponentActivityUnderInputs.Hypotheses p.binomial (min (ε / 24) (1 / 12))
  beta : FinitePairDeficitInputs.Hypotheses p.beta (GeneralGraphHostCount.sizeCap (ε / 768))

theorem regular_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let G := RegularStarts.regularStarts N L
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
            (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨pB, hpB⟩ := RetainedBinomialApproximationUnderInputs.uniform_bound C (ε / 3) (by positivity)
  obtain ⟨pβ, hpβ⟩ := RetainedBetaCovarianceUnderInputs.uniform_bound C (ε / 3) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := SubpowerPairAbsoluteActivity.uniform_bound C (ε / 3) (by positivity)
  obtain ⟨NC, hc⟩ := PoissonCharlierConversion.actual_regular_bound C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let E := PoissonCharlierConversion.errorConstant C
  have hE : 0 ≤ E := (PoissonCharlierConversion.errorConstant_pos C).le
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (5 + 2 * E)
    (-4 / 5 + ε / 3) (2 * ε / 3) (by positivity)
  refine ⟨⟨pB, pβ⟩, ?_⟩
  intro hgeo
  have hsB : (ε / 3) / 8 = ε / 24 := by ring
  have hsβ : (ε / 3) / 256 = ε / 768 := by ring
  obtain ⟨NB, _hNB, hb⟩ := hpB (by simpa only [hsB] using hgeo.binomial)
  obtain ⟨Nβ, _hNβ, hβ⟩ := hpβ (by simpa only [hsβ] using hgeo.beta)
  refine ⟨10 + NA + NC + NG + NF + NB + Nβ, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := RegularStarts.regularStarts N L
  let μ := countMoment G L 1
  let α := RegularCumulantTransfer.secondFactorialCumulant G L
  let H : ℝ := (8 * (L + 1) : ℕ)
  let P := (N : ℝ) ^ (-4 / 5 + ε / 3)
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : 2 ≤ N := by omega
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hcov : |regularCovariance N L| ≤ (N : ℝ) ^ (ε / 3) :=
    (abs_sum_le_sum_abs _ _).trans (ha N (by omega) L hband G (RegularStarts.regularStarts_subset N L))
  have hquot : |regularCovariance N L| / N ≤ P := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 3) / N := div_le_div_of_nonneg_right hcov hnpos.le
      _ = (N : ℝ) ^ (-1 + ε / 3) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hnpos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hNtwo : 1 / (N : ℝ) ^ 2 ≤ P := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hnpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
  have hbeta : |RetainedReferenceTheorem.beta H N L - regularCovariance N L| ≤ P := hβ N (by omega) L hband
  have hconv := hc N (by omega) L hband H (regularCovariance N L)
  dsimp only at hconv
  rw [← regular_mean hN2 hL, ← regular_cumulant hN2 hL] at hconv
  simp only [_root_.sub_apply] at hconv
  change SignedAtomicDistance.distance (FiniteLawEmbedding.embed (RetainedReferenceTheorem.binomialReference H N L))
    (QuadraticPoisson.reference μ α) ≤ 4 * |RetainedReferenceTheorem.beta H N L - regularCovariance N L| +
      E * (1 / (N : ℝ) ^ 2 + |regularCovariance N L| / N) at hconv
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hNtwo hquot) hE
  have hconversion : SignedAtomicDistance.distance
      (FiniteLawEmbedding.embed (RetainedReferenceTheorem.binomialReference H N L))
      (QuadraticPoisson.reference μ α) ≤ (4 + 2 * E) * P := by
    nlinarith only [hconv, hscaled, hbeta]
  have hbinomial : SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (RetainedReferenceTheorem.binomialReference H N L)) ≤ P := hb N (by omega) L hband
  have htriangle := SignedAtomicDistance.triangle (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
    (FiniteLawEmbedding.embed (RetainedReferenceTheorem.binomialReference H N L)) (QuadraticPoisson.reference μ α)
  calc
    _ ≤ (5 + 2 * E) * P := by linarith only [htriangle, hbinomial, hconversion]
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 3) + 2 * ε / 3) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T17_5 (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (ε / 2) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let μ := countMoment (dyadicBlock N) L 1
        let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
        let ν := (N : ℝ) * (2 ^ L : ℝ)⁻¹
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference μ α) ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference ν α) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := regular_bound C (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := RegularQuadraticReferenceRestoration.uniform_reference_errors C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NR, _hNR, hr⟩ := hp hgeo
  refine ⟨10 + NT + NF + NR, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := RegularStarts.regularStarts N L
  let Q := QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)
  let P := (N : ℝ) ^ (-4 / 5 + ε / 2)
  let U := (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  let R := (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hrest := ht N (by omega) L hband
  have hsmall : (N : ℝ) ^ (-1 + ε / 2) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hregular : SignedAtomicDistance.distance R Q ≤ P := hr N (by omega) L hband
  have hfactor : 2 * P ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have htriangle (S : SignedMeasure ℕ) : SignedAtomicDistance.distance U S ≤
      SignedAtomicDistance.distance U R + SignedAtomicDistance.distance R Q + SignedAtomicDistance.distance Q S := by
    have hUR := SignedAtomicDistance.triangle U R S
    have hRQ := SignedAtomicDistance.triangle R Q S
    linarith only [hUR, hRQ]
  constructor
  · apply (htriangle _).trans
    apply le_trans _ hfactor
    linarith only [hregular, hrest.1.trans hsmall]
  · apply (htriangle _).trans
    apply le_trans _ hfactor
    linarith only [hregular, hrest.2.trans hsmall]

end PaperP1.FirstQuadraticApproximationUnderInputs
