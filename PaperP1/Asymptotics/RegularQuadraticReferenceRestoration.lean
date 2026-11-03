module

public import PaperP1.Asymptotics.RegularSecondCumulantRestoration
public import PaperP1.Asymptotics.SubpowerPairAbsoluteActivity
public import PaperP1.Model.OriginalCountLawCoupling
public import PaperP1.Probability.SignedAtomicDistance
public import PaperP1.Probability.PoissonParameterStability

/-! # Restoring the full actual and nominal quadratic references costs N^(-1+epsilon), without geometric or higher-moment premises -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularQuadraticReferenceRestoration

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables

theorem mean_gap (N L : ℕ) :
    |countMoment (dyadicBlock N) L 1 - countMoment (RegularStarts.regularStarts N L) L 1| =
      ∑ x ∈ RegularStarts.irregularStarts N L, infiniteMarginal x L := by
  have h := sum_sdiff (RegularStarts.regularStarts_subset N L) (f := fun x ↦ infiniteMarginal x L)
  have heq : (∑ x ∈ dyadicBlock N, infiniteMarginal x L) -
      (∑ x ∈ RegularStarts.regularStarts N L, infiniteMarginal x L) =
      ∑ x ∈ RegularStarts.irregularStarts N L, infiniteMarginal x L := by
    change (∑ x ∈ RegularStarts.irregularStarts N L, infiniteMarginal x L) +
      (∑ x ∈ RegularStarts.regularStarts N L, infiniteMarginal x L) = _ at h
    linarith only [h]
  rw [countMoment_one Subset.rfl, countMoment_one (RegularStarts.regularStarts_subset N L), heq,
    abs_of_nonneg (sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)]

theorem uniform_mean_gap (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |countMoment (dyadicBlock N) L 1 - countMoment (RegularStarts.regularStarts N L) L 1| ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, _hN₀, h⟩ := IrregularPairActivity.uniform_marginal_mass C ε hε
  refine ⟨10 + N₀, by omega, ?_⟩
  intro N hN L hband
  rw [mean_gap]
  exact h N (by omega) L hband

theorem uniform_subpower_cumulant (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤ (N : ℝ) ^ ε := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨NA, _hNA, ha⟩ := SubpowerPairAbsoluteActivity.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + M ^ 2) (ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NA + NM + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) hG
    (fun x hx ↦ hm N (by omega) L hband x (hG hx))
  change (∑ x ∈ G, infiniteMarginal x L ^ 2) ≤ M ^ 2 / N at hdiag
  have hD : (∑ x ∈ G, infiniteMarginal x L ^ 2) ≤ M ^ 2 * (N : ℝ) ^ (ε / 2) := by
    apply hdiag.trans
    have hNpow : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hNpow (sq_nonneg M)
  have hform := HeterogeneousRunConversion.second_cumulant_formula (L := L) hG
  change RegularCumulantTransfer.secondFactorialCumulant G L =
    2 * (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) - ∑ x ∈ G, infiniteMarginal x L ^ 2 at hform
  have hfinite : |RegularCumulantTransfer.secondFactorialCumulant G L| ≤
      2 * (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) + ∑ x ∈ G, infiniteMarginal x L ^ 2 := by
    rw [hform]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sum_nonneg fun x _ ↦ sq_nonneg (infiniteMarginal x L))]
    exact add_le_add (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)) le_rfl
  have hA := ha N (by omega) L hband G hG
  calc
    _ ≤ (2 + M ^ 2) * (N : ℝ) ^ (ε / 2) := by linarith only [hfinite, hA, hD]
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem parameter_bound (μ ν α β V T B : ℝ) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hV : 1 ≤ V) (hT : 0 ≤ T) (_hB : 0 ≤ B) (hα : |α| ≤ V)
    (hmean : |μ - ν| ≤ B * T) (hcumulant : |α - β| ≤ T) :
    SignedAtomicDistance.distance (QuadraticPoisson.reference μ α) (QuadraticPoisson.reference ν β) ≤
      (6 * B + 2) * V * T := by
  have h := PoissonParameterStability.actual_signed_difference hμ hν α β
  simp only [_root_.sub_apply] at h
  change SignedAtomicDistance.distance _ _ ≤ 2 * (1 + 2 * |α|) * |μ - ν| + 2 * |α - β| at h
  have hcoef : 2 * (1 + 2 * |α|) ≤ 6 * V := by linarith only [hα, hV]
  have hprod := mul_le_mul hcoef hmean (abs_nonneg (μ - ν)) (by linarith only [hV] : 0 ≤ 6 * V)
  have htail := mul_le_mul_of_nonneg_right hV hT
  nlinarith only [h, hprod, hcumulant, htail]

theorem uniform_reference_errors (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let G := RegularStarts.regularStarts N L
      let μR := countMoment G L 1
      let αR := RegularCumulantTransfer.secondFactorialCumulant G L
      let μ := countMoment (dyadicBlock N) L 1
      let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
      let ν := (N : ℝ) * (2 ^ L : ℝ)⁻¹
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure +
        SignedAtomicDistance.distance (QuadraticPoisson.reference μR αR) (QuadraticPoisson.reference μ α) ≤
          (N : ℝ) ^ (-1 + ε) ∧
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure +
        SignedAtomicDistance.distance (QuadraticPoisson.reference μR αR) (QuadraticPoisson.reference ν α) ≤
          (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨NM, _hNM, hm⟩ := uniform_mean_gap C δ hδ
  obtain ⟨NA, _hNA, ha⟩ := RegularSecondCumulantRestoration.uniform_bound C δ hδ
  obtain ⟨NV, _hNV, hv⟩ := uniform_subpower_cumulant C δ hδ
  obtain ⟨ND, hd⟩ := RegularSetAsymptotic.discarded_activity_critical C δ hδ
  obtain ⟨NN, _hNN, hn⟩ := CriticalActualMean.uniform_nominal_bias C δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let M : ℝ := (2 : ℝ) ^ C
  let A : ℝ := 8 + 10 * M
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption A (-1 + 2 * δ) (ε / 2) (by positivity)
  refine ⟨10 + NM + NA + NV + ND + NN + NG + NF, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := RegularStarts.regularStarts N L
  let μR := countMoment G L 1
  let μ := countMoment (dyadicBlock N) L 1
  let αR := RegularCumulantTransfer.secondFactorialCumulant G L
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let ν := (N : ℝ) * (2 ^ L : ℝ)⁻¹
  let V := (N : ℝ) ^ δ
  let T := (N : ℝ) ^ (-1 + δ)
  let W := (N : ℝ) ^ (-1 + 2 * δ)
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hV : 1 ≤ V := Real.one_le_rpow hn1 hδ.le
  have hT : 0 ≤ T := Real.rpow_nonneg hnpos.le _
  have hW : 0 ≤ W := Real.rpow_nonneg hnpos.le _
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hVT : V * T = W := by rw [← Real.rpow_add hnpos]; congr 1; ring
  have hTW : T ≤ W := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ])
  have hμR : 0 ≤ μR := RegularMomentTransfer.countMoment_nonneg (RegularStarts.regularStarts_subset N L) 1
  have hμ : 0 ≤ μ := RegularMomentTransfer.countMoment_nonneg (Subset.refl (dyadicBlock N)) 1
  have hν : 0 ≤ ν := by dsimp only [ν]; positivity
  have hαR : |αR| ≤ V := hv N (by omega) L hband G (RegularStarts.regularStarts_subset N L)
  have hmean : |μR - μ| ≤ T := by simpa only [abs_sub_comm] using hm N (by omega) L hband
  have halpha : |αR - α| ≤ T := by simpa only [abs_sub_comm] using ha N (by omega) L hband
  have hnom : |μ - ν| ≤ M * T := hn N (by omega) L hband
  have hmeanNom : |μR - ν| ≤ (1 + M) * T :=
    (abs_sub_le μR μ ν).trans (by linarith only [hmean, hnom])
  have href : SignedAtomicDistance.distance (QuadraticPoisson.reference μR αR) (QuadraticPoisson.reference μ α) ≤ 8 * W := by
    have h := parameter_bound μR μ αR α V T 1 hμR hμ hV hT (by norm_num) hαR
      (by simpa only [one_mul] using hmean) halpha
    norm_num only [show (6 * (1 : ℝ) + 2) = 8 by norm_num] at h
    simpa only [mul_assoc, hVT] using h
  have hrefNom : SignedAtomicDistance.distance (QuadraticPoisson.reference μR αR) (QuadraticPoisson.reference ν α) ≤
      (8 + 6 * M) * W := by
    have h := parameter_bound μR ν αR α V T (1 + M) hμR hν hV hT (by linarith only [hM]) hαR hmeanNom halpha
    rw [mul_assoc, hVT] at h
    convert h using 1; ring
  have hcouple : SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure ≤ 4 * M * W := by
    rw [SignedAtomicDistance.probability_eq]
    have h := (OriginalCountLawCoupling.coupling L (dyadicBlock N) G).trans (hd N (by omega) L hL hband)
    have hmul := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    have hsmall := mul_le_mul_of_nonneg_left hTW (by positivity : 0 ≤ 4 * M)
    nlinarith only [hmul, hsmall]
  have hfactor : A * W ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    dsimp only [δ]
    ring
  have hfirst : SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure +
      SignedAtomicDistance.distance (QuadraticPoisson.reference μR αR) (QuadraticPoisson.reference μ α) ≤ A * W := by
    dsimp only [A]
    nlinarith only [hcouple, href, mul_nonneg hM hW]
  have hsecond : SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure +
      SignedAtomicDistance.distance (QuadraticPoisson.reference μR αR) (QuadraticPoisson.reference ν α) ≤ A * W := by
    dsimp only [A]
    nlinarith only [hcouple, hrefNom]
  exact ⟨hfirst.trans hfactor, hsecond.trans hfactor⟩

end PaperP1.RegularQuadraticReferenceRestoration
