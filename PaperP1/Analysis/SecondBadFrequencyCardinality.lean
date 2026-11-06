module

public import PaperP1.Analysis.MixedRegionEnvelope
public import PaperP1.Analysis.SecondPrimeLargeValueCardinality

set_option autoImplicit false
@[expose] public noncomputable section
universe u833
namespace PaperP1.SecondBadFrequencyCardinality
open Finset Filter PaperP1
open scoped Classical

theorem band_count_factor (x z : ℝ) (hx : 100000 ≤ x) (hz : x^5 ≤ z) :
    2*x^6 ≤ Real.exp (z/342) := by
  have hxp : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hLogX := Real.log_le_sub_one_of_pos hxp
  have hLogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hLog : Real.log (2*x^6) ≤ 7*x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 6 hxp.ne'),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hLogX,hLogTwo,hx]
  have hx4 : 2394 ≤ x^4 := by
    have hh := pow_le_pow_right₀ hx1 (by norm_num : (1 : ℕ) ≤ 4)
    simp only [pow_one] at hh
    linarith only [hh,hx]
  have hExp : 7*x ≤ z/342 := by
    have hh := mul_le_mul_of_nonneg_right hx4 hxp.le
    nlinarith only [hh,hz]
  calc
    _ = Real.exp (Real.log (2*x^6)) := (Real.exp_log (by positivity : 0 < 2*x^6)).symm
    _ ≤ Real.exp (7*x) := Real.exp_le_exp.mpr hLog
    _ ≤ _ := Real.exp_le_exp.mpr hExp

theorem all_blocks_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ p ∈ TwoPrimeBandPopulation.second N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u833} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
        (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j)^(-1/40 : ℝ) ≤
        ‖DirichletPolynomialMeanValue.value
          (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) j) f (τ r)‖) →
      (R.card : ℝ) ≤ (N : ℝ)^(1/18 : ℝ) := by
  obtain ⟨NM,hNM,hM⟩ := SecondPrimeLargeValueCardinality.per_block_uniform.{u833}
  have hGeometry : ∀ᶠ N : ℕ in atTop,
      100000 ≤ SlowPrimeBandSieve.lower N ∧ 1 ≤ SlowPrimeBandSieve.upper N ∧
      (SlowPrimeBandSieve.lower N)^5 ≤ SlowPrimeBandSieve.upper N ∧
      1 ≤ GrowingFirstGoodRegion.width N ∧
      (GrowingFirstGoodRegion.width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 := by
    filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 100000),
      SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1),
      PowerLogPrimeBand.geometry_eventually 5 (by norm_num),GrowingFirstGoodRegion.width_geometry] with N hx hz hp hw
    exact ⟨hx,hz,hp.2,by omega,hw.2.1⟩
  obtain ⟨NG,hG⟩ := eventually_atTop.mp hGeometry
  refine ⟨max NM NG,by omega,?_⟩
  intro N hN f hf ι R τ T hT hTN htau hsep hAny
  let H := GrowingFirstGoodRegion.width N
  let J := NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)
  let S (j : ℕ) := R.filter (fun r ↦ (NarrowPrimeBands.anchor H j)^(-1/40 : ℝ) ≤
    ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (TwoPrimeBandPopulation.second N) j) f (τ r)‖)
  have hCover : R ⊆ J.biUnion S := by
    intro r hr
    obtain ⟨j,hj,hLarge⟩ := hAny r hr
    exact mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hr,hLarge⟩⟩
  have hCard : (R.card : ℝ) ≤ ∑ j ∈ J, ((S j).card : ℝ) := by
    have hh := (card_le_card hCover).trans (card_biUnion_le)
    exact_mod_cast hh
  have hEach (j : ℕ) (hj : j ∈ J) : ((S j).card : ℝ) ≤ (N : ℝ)^(1/19 : ℝ) :=
    hM N (by omega) j hj f hf (S j) τ T hT hTN
      (fun r hr ↦ htau r (mem_filter.mp hr).1)
      (fun r hr s hs hne ↦ hsep r (mem_filter.mp hr).1 s (mem_filter.mp hs).1 hne)
      (fun r hr ↦ (mem_filter.mp hr).2)
  obtain ⟨hx,hz,hz5,hH,hHcap⟩ := hG N (by omega)
  have hJ := (MixedRegionEnvelope.index_card_bounds N H (by omega) (by linarith only [hx]) hz hHcap).2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hFactor := band_count_factor (SlowPrimeBandSieve.lower N) (SlowPrimeBandSieve.upper N) hx hz5
  have hFactorR : 2*(SlowPrimeBandSieve.lower N)^6 ≤ (N : ℝ)^(1/342 : ℝ) := by
    convert hFactor using 1
    rw [Real.rpow_def_of_pos hNp]
    change Real.exp (Real.log (N : ℝ)*(1/342))=Real.exp (Real.log (N : ℝ)/342)
    congr 1
    ring
  calc
    _ ≤ ∑ j ∈ J, ((S j).card : ℝ) := hCard
    _ ≤ ∑ _j ∈ J, (N : ℝ)^(1/19 : ℝ) := sum_le_sum hEach
    _ = (J.card : ℝ)*(N : ℝ)^(1/19 : ℝ) := by simp
    _ ≤ (2*(SlowPrimeBandSieve.lower N)^6)*(N : ℝ)^(1/19 : ℝ) :=
      mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ ≤ (N : ℝ)^(1/342 : ℝ)*(N : ℝ)^(1/19 : ℝ) :=
      mul_le_mul_of_nonneg_right hFactorR (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num
end PaperP1.SecondBadFrequencyCardinality
