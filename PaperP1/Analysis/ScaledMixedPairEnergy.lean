module

public import PaperP1.Analysis.ActualMixedPairDecay


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ScaledMixedPairEnergy
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem uniform_bound (D : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      ∀ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      ∀ f : ℕ → ℂ, (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T →
      T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in ActualMixedPairDecay.region N j l f T, ‖ActualMixedPairDecay.term N l f t‖^2) ≤
        (D+1)*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/100 : ℝ) := by
  obtain ⟨NG,hG⟩ := eventually_atTop.mp ActualAnchorOrderGeometry.eventual_order_geometry
  refine ⟨max 1 NG,by omega,?_⟩
  intro N hN j hj l hl f hf T hT hTime
  obtain ⟨hx,hH,hGeometry⟩ := hG N (by omega)
  obtain ⟨hHu,huCap,hLogu,hLogu1,hq1,hLogq,hqLow,hkH,hkCap⟩ := hGeometry j hj l hl
  let H := GrowingFirstGoodRegion.width N
  let x := SlowPrimeBandSieve.lower N
  let u := NarrowPrimeBands.anchor H j
  let q := NarrowPrimeBands.anchor H l
  let k := FloorAmplificationOrder.order u q
  let A := NarrowPrimeBands.band H (TwoPrimeBandPopulation.first N) j
  let Ltot := ⌈u⌉₊^k*⌈(N : ℝ)/q⌉₊
  have hu : 1 < u := by
    have hup : 0 < u := NarrowPrimeBands.anchor_pos H j
    have hh := Real.exp_lt_exp.mpr (show 0 < Real.log u by linarith only [hLogu1])
    simpa only [Real.exp_zero,Real.exp_log hup] using hh
  have hup : 0 < u := by linarith only [hu]
  have hqp : 0 < q := NarrowPrimeBands.anchor_pos H l
  have hxp : 0 < x := by change 2 ≤ x at hx; linarith only [hx]
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hPrime : ∀ p ∈ TwoPrimeBandPopulation.first N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hfP : ∀ p ∈ TwoPrimeBandPopulation.first N, ‖f p‖ ≤ 1 := fun p hp ↦ hf p (hPrime p hp).pos
  have hfB : ∀ n ∈ NarrowRamareRectangle.cofactorSet N H l, ‖f n‖ ≤ 1 := by
    intro n hn
    exact hf n (mem_Icc.mp (mem_filter.mp hn).1).1
  have hHR : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hMass := NarrowBandReciprocalMass.mass_le_one H hH (TwoPrimeBandPopulation.first N)
    (fun p hp ↦ (hPrime p hp).one_le) j (by linarith only [hHR,hHu])
  have hWeight : ((q^(-1/40 : ℝ))^2/(1/x^10)^(2*k))*AmplifiedPrimeProductMean.budget k A ≤ q^(-1/100 : ℝ) :=
    AmplificationThresholdDecay.mixed_weight_bound x u q hx hqp k hkCap A hMass hLogu
      (FloorAmplificationOrder.logarithmic_upper u q hu hq1)
  have hBaseLength : (N : ℝ)/Real.log (N : ℝ) ≤ (Ltot : ℝ) :=
    FloorAmplificationOrder.short_height_bound N u q ((N : ℝ)/Real.log (N : ℝ)) hu hq1 huCap le_rfl
  have hTime' : T ≤ D*((N : ℝ)/Real.log (N : ℝ)) := by simpa only [mul_div_assoc] using hTime
  have hLength : T ≤ D*(Ltot : ℝ) := hTime'.trans (mul_le_mul_of_nonneg_left hBaseLength hD)
  have hUL : 0 < ⌈u⌉₊ := Nat.ceil_pos.mpr hup
  have hNL : 0 < ⌈(N : ℝ)/q⌉₊ := Nat.ceil_pos.mpr (div_pos hNP hqp)
  have hLN : 0 < Ltot := Nat.mul_pos (pow_pos hUL k) hNL
  have hLP : (0 : ℝ) < Ltot := by exact_mod_cast hLN
  have hRatio : T/(Ltot : ℝ)+1 ≤ D+1 :=
    add_le_add ((div_le_iff₀ hLP).mpr hLength) (le_refl 1)
  have hv : 0 < 1/x^10 := by positivity
  have hw : 0 ≤ q^(-1/40 : ℝ) := Real.rpow_nonneg hqp.le _
  have hm := ActualNarrowMixedMean.estimates.{0} N H j l k (by omega) hH hkH hHu
    (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N)
    hPrime f hfP hfB T (1/x^10) (q^(-1/40 : ℝ)) hT hv hw
  let c := (q^(-1/40 : ℝ))^2/(1/x^10)^(2*k)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hb := AmplifiedPrimeProductMean.budget_nonneg k A
  have hC := BoundedAmplificationFactor.constant_pos
  change c*AmplifiedPrimeProductMean.budget k A ≤ q^(-1/100 : ℝ) at hWeight
  calc
    _ ≤ c*(BoundedAmplificationFactor.constant*(T/(Ltot : ℝ)+1)*AmplifiedPrimeProductMean.budget k A) := hm.1
    _ = (BoundedAmplificationFactor.constant*(T/(Ltot : ℝ)+1))*(c*AmplifiedPrimeProductMean.budget k A) := by ring
    _ ≤ (BoundedAmplificationFactor.constant*(D+1))*q^(-1/100 : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hRatio hC.le) hWeight (mul_nonneg hc hb)
        (mul_nonneg hC.le (by linarith only [hD]))
    _ = _ := by ring
end PaperP1.ScaledMixedPairEnergy
