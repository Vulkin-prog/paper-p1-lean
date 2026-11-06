module

public import PaperP1.Analysis.GrowingGoodFullPolynomial


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ScaledFirstGoodEnergy
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem quantitative_bound (D : ℝ) (hD : 0 ≤ D) (N H : ℕ) (hN : 0 < N) (hH : 0 < H)
    (hU : 1 ≤ SlowPrimeBandSieve.upper N) (hL : 1 ≤ SlowPrimeBandSieve.lower N)
    (Q : Finset ℕ) (f : ℕ → ℂ) (hf : ∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) (hTime : T ≤ D*(N : ℝ)/Real.log (N : ℝ)) :
    (∫ t in SmallPrimeRegion.goodSet H (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N),
      ‖NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) Q f t‖^2) ≤
        (D+1)*FirstBandSmallRegion.envelope H N := by
  obtain ⟨hAnchor,hCard⟩ := FirstBandSmallRegion.indices_geometry N H hH hU hL
  have hNP : (0 : ℝ) < N := by exact_mod_cast hN
  have hLog : 0 < Real.log (N : ℝ) := by change 1 ≤ Real.log (N : ℝ) at hU; linarith only [hU]
  have hD1 : 0 ≤ D+1 := by linarith only [hD]
  have hC := SupportedCoefficientSquareBudget.constant_pos
  let P := TwoPrimeBandPopulation.first N
  let J := NarrowPrimeBands.indices H P
  have hMean (j : ℕ) (hj : j ∈ J) :
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N H j)
        (NarrowRamareRectangle.coefficient P Q f) t‖^2) ≤ SupportedCoefficientSquareBudget.constant*(D+1) := by
    have hProduct : T*NarrowPrimeBands.anchor H j ≤ D*(N : ℝ) :=
      (mul_le_mul_of_nonneg_left (hAnchor j hj) hT.le).trans ((le_div_iff₀ hLog).mp hTime)
    have hRatio : T*NarrowPrimeBands.anchor H j/(N : ℝ) ≤ D := (div_le_iff₀ hNP).mpr hProduct
    have hm := NarrowCofactorMeanValue.quantitative_bound N H j hN P Q f
      (fun n hn ↦ hf n (mem_filter.mp hn).1) T hT
    exact hm.trans (mul_le_mul_of_nonneg_left (add_le_add hRatio (le_refl 1)) hC.le)
  have hBound := SmallPrimeRegion.finite_product_bound J
    (fun j ↦ DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f)
    (fun j ↦ DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N H j) (NarrowRamareRectangle.coefficient P Q f))
    (fun _ _ ↦ GaussianExponentialSums.polynomial_continuous _ _ _)
    (fun _ _ ↦ GaussianExponentialSums.polynomial_continuous _ _ _)
    (SmallPrimeRegion.goodSet H P f T (FirstBandSmallRegion.threshold N))
    (SmallPrimeRegion.goodSet_measurable _ _ _ _ _) T (FirstBandSmallRegion.threshold N)
    (SupportedCoefficientSquareBudget.constant*(D+1)) hT.le (FirstBandSmallRegion.threshold_nonneg N)
    (fun _ ht ↦ ht.1) (fun _ ht j hj ↦ ht.2 j hj) hMean
  have hSq := pow_le_pow_left₀ (Nat.cast_nonneg J.card) hCard 2
  have hx : 0 < SlowPrimeBandSieve.lower N := by linarith only [hL]
  have hScalar : (J.card : ℝ)^2*(FirstBandSmallRegion.threshold N)^2*(2*SupportedCoefficientSquareBudget.constant) ≤
      FirstBandSmallRegion.envelope H N := by
    calc
      _ ≤ (((H : ℝ)+1)*SlowPrimeBandSieve.lower N)^2*(FirstBandSmallRegion.threshold N)^2*
          (2*SupportedCoefficientSquareBudget.constant) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hSq (sq_nonneg _)) (by positivity)
      _ = _ := by unfold FirstBandSmallRegion.threshold FirstBandSmallRegion.envelope; field_simp [hx.ne']
  have hConst : SupportedCoefficientSquareBudget.constant*(D+1) ≤ (D+1)*(2*SupportedCoefficientSquareBudget.constant) := by
    nlinarith only [mul_nonneg hC.le hD1]
  calc
    _ ≤ (J.card : ℝ)^2*(FirstBandSmallRegion.threshold N)^2*(SupportedCoefficientSquareBudget.constant*(D+1)) := hBound
    _ ≤ (J.card : ℝ)^2*(FirstBandSmallRegion.threshold N)^2*((D+1)*(2*SupportedCoefficientSquareBudget.constant)) :=
      mul_le_mul_of_nonneg_left hConst (by positivity)
    _ = (D+1)*((J.card : ℝ)^2*(FirstBandSmallRegion.threshold N)^2*(2*SupportedCoefficientSquareBudget.constant)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hScalar hD1

theorem rectangle_small_uniform (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 →
      ∀ Q : Finset ℕ, ∀ f : ℕ → ℂ, (∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in SmallPrimeRegion.goodSet H (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N),
        ‖NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) Q f t‖^2) ≤ ε := by
  have hLimit : Tendsto (fun N ↦ (D+1)*GrowingFirstGoodRegion.envelope N) atTop (nhds 0) := by
    simpa only [mul_zero] using GrowingFirstGoodRegion.envelope_tendsto.const_mul (D+1)
  obtain ⟨NE,hE⟩ := eventually_atTop.mp (hLimit.eventually (eventually_lt_nhds hε))
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨max 1 (max NE (max NU NL)),by omega,?_⟩
  intro N hN H hH hCap Q f hf T hT hTime
  have hActual := quantitative_bound D hD N H (by omega) (by omega) (hU N (by omega)) (hL N (by omega)) Q f hf T hT hTime
  have hEnvelope := mul_le_mul_of_nonneg_left (GrowingFirstGoodRegion.first_envelope_bound N H (hL N (by omega)) hCap)
    (by linarith only [hD] : 0 ≤ D+1)
  exact hActual.trans (hEnvelope.trans (hE N (by omega)).le)

theorem full_small_uniform (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ m n, f (m*n)=f m*f n) → (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T
        (FirstBandSmallRegion.threshold N), ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤ ε := by
  obtain ⟨H₀,hH₀,NA,hNA,hApprox⟩ := TwoBandRectangleApproximation.both_rectangles_small_uniform (ε/4) (by positivity)
  obtain ⟨NR,hNR,hRectangle⟩ := rectangle_small_uniform D hD (ε/4) (by positivity)
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop (max 1 D)))
  obtain ⟨NH,hWidth⟩ := eventually_atTop.mp (GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop H₀))
  obtain ⟨NG,hGeometry⟩ := eventually_atTop.mp GrowingFirstGoodRegion.width_geometry
  refine ⟨max NA (max NR (max NL (max NH NG))),by omega,?_⟩
  intro N hN f hf hb T hT hTime
  have hNP : 0 < N := by omega
  have hLog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans (hLog N (by omega))
  have hDLog : D ≤ Real.log (N : ℝ) := (le_max_right _ _).trans (hLog N (by omega))
  have hLogP : 0 < Real.log (N : ℝ) := by linarith only [hLog1]
  have hTN : T ≤ (N : ℝ) := hTime.trans ((div_le_iff₀ hLogP).mpr (by
    have hh := mul_le_mul_of_nonneg_right hDLog (Nat.cast_nonneg N)
    nlinarith only [hh]))
  have hWide : ∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (hNP.trans_le (mem_Ico.mp hn).1)
  have hUnit : ∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (mem_Icc.mp hn).1
  have hGeo := hGeometry N (by omega)
  have ha := (hApprox (GrowingFirstGoodRegion.width N) (hWidth N (by omega)) N (by omega) f hf hWide T hT hTN).1
  have hr := hRectangle N (by omega) (GrowingFirstGoodRegion.width N) (by omega) hGeo.2.1
    (TwoPrimeBandPopulation.second N) f hUnit T hT hTime
  have ht := FirstGoodFullPolynomial.restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) f)
    (GaussianExponentialSums.polynomial_continuous _ _ _) (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _)
    (SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N))
    (SmallPrimeRegion.goodSet_measurable (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N))
    T hT.le (fun _ ht ↦ ht.1)
  linarith only [ht,ha,hr]
end PaperP1.ScaledFirstGoodEnergy
