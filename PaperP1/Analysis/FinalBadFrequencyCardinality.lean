module

public import PaperP1.Analysis.FinalNarrowBandGeometry
public import PaperP1.Analysis.FinalPrimeLargeValueCardinality

set_option autoImplicit false
@[expose] public noncomputable section
universe u844
namespace PaperP1.FinalBadFrequencyCardinality
open Finset Filter PaperP1
open scoped Classical

theorem band_count_factor (x z : ℝ) (hx : 10 ≤ x) (hz : 0 < z) (hLog : Real.log z=x) :
    2*z^4 ≤ Real.exp (x^2) := by
  have hxp : 0 < x := by linarith only [hx]
  have hLogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hArg : Real.log (2*z^4) ≤ x^2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 4 hz.ne'),Real.log_pow,hLog]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_left hx hxp.le
    nlinarith only [hLogTwo,hh,hx]
  calc
    _ = Real.exp (Real.log (2*z^4)) := (Real.exp_log (by positivity : 0 < 2*z^4)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hArg

theorem all_blocks_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, 32 ≤ B → ∀ f : ℕ → ℂ,
      (∀ p ∈ FinalPrimeBandGeometry.primes B N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u844} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N),
        FinalSmallPrimeSamples.threshold N ≤
        ‖DirichletPolynomialMeanValue.value
          (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) j) f (τ r)‖) →
      (R.card : ℝ) ≤ Real.exp (1001*(SlowPrimeBandSieve.lower N)^2) := by
  obtain ⟨NM,hNM,hM⟩ := FinalPrimeLargeValueCardinality.per_block_uniform.{u844}
  have hGeometry : ∀ᶠ N : ℕ in atTop,
      10 ≤ SlowPrimeBandSieve.lower N ∧ 1 ≤ SlowPrimeBandSieve.upper N ∧
      (GrowingFirstGoodRegion.width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 := by
    filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 10),
      SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1),GrowingFirstGoodRegion.width_geometry] with N hx hz hw
    exact ⟨hx,hz,hw.2.1⟩
  obtain ⟨NG,hG⟩ := eventually_atTop.mp hGeometry
  refine ⟨max NM NG,by omega,?_⟩
  intro N hN B hB f hf ι R τ T hT hTN htau hsep hAny
  let H := GrowingFirstGoodRegion.width N
  let J := NarrowPrimeBands.indices H (FinalPrimeBandGeometry.primes B N)
  let S (j : ℕ) := R.filter (fun r ↦ FinalSmallPrimeSamples.threshold N ≤
    ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FinalPrimeBandGeometry.primes B N) j) f (τ r)‖)
  have hCover : R ⊆ J.biUnion S := by
    intro r hr
    obtain ⟨j,hj,hLarge⟩ := hAny r hr
    exact mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hr,hLarge⟩⟩
  have hCard : (R.card : ℝ) ≤ ∑ j ∈ J, ((S j).card : ℝ) := by
    have hh := (card_le_card hCover).trans (card_biUnion_le)
    exact_mod_cast hh
  have hEach (j : ℕ) (hj : j ∈ J) : ((S j).card : ℝ) ≤ Real.exp (1000*(SlowPrimeBandSieve.lower N)^2) :=
    hM N (by omega) B j hj f hf (S j) τ T hT hTN
      (fun r hr ↦ htau r (mem_filter.mp hr).1)
      (fun r hr s hs hne ↦ hsep r (mem_filter.mp hr).1 s (mem_filter.mp hs).1 hne)
      (fun r hr ↦ (mem_filter.mp hr).2)
  obtain ⟨hx,hz,hHcap⟩ := hG N (by omega)
  have hJ := FinalNarrowBandGeometry.index_card_bound B N H hB (by omega) hz hHcap
  have hzp : 0 < SlowPrimeBandSieve.upper N := by linarith only [hz]
  have hFactor := band_count_factor (SlowPrimeBandSieve.lower N) (SlowPrimeBandSieve.upper N) hx hzp rfl
  calc
    _ ≤ ∑ j ∈ J, ((S j).card : ℝ) := hCard
    _ ≤ ∑ _j ∈ J, Real.exp (1000*(SlowPrimeBandSieve.lower N)^2) := sum_le_sum hEach
    _ = (J.card : ℝ)*Real.exp (1000*(SlowPrimeBandSieve.lower N)^2) := by simp
    _ ≤ (2*(SlowPrimeBandSieve.upper N)^4)*Real.exp (1000*(SlowPrimeBandSieve.lower N)^2) :=
      mul_le_mul_of_nonneg_right hJ (Real.exp_pos _).le
    _ ≤ Real.exp ((SlowPrimeBandSieve.lower N)^2)*Real.exp (1000*(SlowPrimeBandSieve.lower N)^2) :=
      mul_le_mul_of_nonneg_right hFactor (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
end PaperP1.FinalBadFrequencyCardinality
