module

public import PaperP1.Analysis.TripleLargeFrequencyReduction
public import PaperP1.Analysis.SeparatedIntegralBound
public import PaperP1.PNT.LogGrowth
public import PaperP1.Analysis.FinalBadFrequencyCardinality

set_option autoImplicit false
@[expose] public noncomputable section
universe u845
namespace PaperP1.TripleLargeSparseCardinality
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem frequency_card_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, 32 ≤ B → ∀ f : ℕ → ℂ,
      (∀ p ∈ FinalPrimeBandGeometry.primes B N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u845} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ TripleLargeFrequencyReduction.largeRegion B N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (R.card : ℝ) ≤ Real.exp (1001*(SlowPrimeBandSieve.lower N)^2) := by
  obtain ⟨N₀,hN₀,hCard⟩ := FinalBadFrequencyCardinality.all_blocks_uniform.{u845}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN B hB f hf ι R τ T hT hTN hInside hsep
  have htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T := by
    intro r hr
    have hh := ((TripleLargeFrequencyReduction.largeRegion_iff B N f T (τ r)).mp (hInside r hr)).1
    exact ⟨hh.1.le,hh.2⟩
  apply hCard N hN B hB f hf R τ T hT hTN htau hsep
  intro r hr
  obtain ⟨j,hj,hLarge⟩ := ((TripleLargeFrequencyReduction.largeRegion_iff B N f T (τ r)).mp (hInside r hr)).2.2.2
  exact ⟨j,hj,hLarge.le⟩

theorem subpower_frequency_card_uniform (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, 32 ≤ B → ∀ f : ℕ → ℂ,
      (∀ p ∈ FinalPrimeBandGeometry.primes B N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u845} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ TripleLargeFrequencyReduction.largeRegion B N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) → (R.card : ℝ) ≤ (N : ℝ)^η := by
  obtain ⟨NC,hNC,hCard⟩ := frequency_card_uniform.{u845}
  have hBase := (PNT.tendsto_pow_log_div_pow_atTop 1 2 (by norm_num)).comp SlowPrimeBandSieve.upper_tendsto
  have hLim : Tendsto (fun N : ℕ ↦ 1001*(SlowPrimeBandSieve.lower N)^2/SlowPrimeBandSieve.upper N) atTop (nhds 0) := by
    simpa only [Function.comp_def,SlowPrimeBandSieve.lower,SlowPrimeBandSieve.upper,Real.rpow_ofNat,Real.rpow_one,mul_div_assoc,mul_zero] using hBase.const_mul 1001
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (hLim.eventually (eventually_lt_nhds hη))
  obtain ⟨NZ,hZ⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨max NC (max NL NZ),by omega,?_⟩
  intro N hN B hB f hf ι R τ T hT hTN hInside hsep
  have hz1 := hZ N (by omega)
  have hzp : 0 < SlowPrimeBandSieve.upper N := by linarith only [hz1]
  have hSmall := (div_lt_iff₀ hzp).mp (hL N (by omega))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ Real.exp (1001*(SlowPrimeBandSieve.lower N)^2) := hCard N (by omega) B hB f hf R τ T hT hTN hInside hsep
    _ ≤ Real.exp (η*SlowPrimeBandSieve.upper N) := Real.exp_le_exp.mpr hSmall.le
    _ = _ := by
      rw [Real.rpow_def_of_pos hNp]
      change Real.exp (η*Real.log (N : ℝ))=Real.exp (Real.log (N : ℝ)*η)
      rw [mul_comm]

theorem measure_bound_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, 32 ≤ B → ∀ f : ℕ → ℂ,
      (∀ p ∈ FinalPrimeBandGeometry.primes B N, ‖f p‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ) →
      volume.real (TripleLargeFrequencyReduction.largeRegion B N f T) ≤
        4*Real.exp (1001*(SlowPrimeBandSieve.lower N)^2) := by
  obtain ⟨N₀,hN₀,hCard⟩ := frequency_card_uniform.{0}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN B hB f hf T hT hTN
  have hI := SeparatedIntegralBound.bound (TripleLargeFrequencyReduction.largeRegion B N f T) T
    (fun _ ↦ (1 : ℝ)) continuous_const (fun _ ↦ zero_le_one)
    (TripleLargeFrequencyReduction.largeRegion_measurable B N f T)
    (fun t ht ↦ ((TripleLargeFrequencyReduction.largeRegion_iff B N f T t).mp ht).1)
    (Real.exp (1001*(SlowPrimeBandSieve.lower N)^2)) (by
      intro R τ hInside hsep
      simpa only [sum_const,nsmul_eq_mul,mul_one] using hCard N hN B hB f hf R τ T hT hTN hInside hsep)
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using hI

theorem subpower_measure_uniform (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, 32 ≤ B → ∀ f : ℕ → ℂ,
      (∀ p ∈ FinalPrimeBandGeometry.primes B N, ‖f p‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ) →
      volume.real (TripleLargeFrequencyReduction.largeRegion B N f T) ≤ (N : ℝ)^η := by
  obtain ⟨NC,hNC,hCard⟩ := subpower_frequency_card_uniform.{0} (η/2) (by positivity)
  have hPow : Tendsto (fun N : ℕ ↦ (N : ℝ)^(η/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < η/2)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NP,hP⟩ := eventually_atTop.mp (hPow.eventually (eventually_ge_atTop 4))
  refine ⟨max NC NP,by omega,?_⟩
  intro N hN B hB f hf T hT hTN
  have hI := SeparatedIntegralBound.bound (TripleLargeFrequencyReduction.largeRegion B N f T) T
    (fun _ ↦ (1 : ℝ)) continuous_const (fun _ ↦ zero_le_one)
    (TripleLargeFrequencyReduction.largeRegion_measurable B N f T)
    (fun t ht ↦ ((TripleLargeFrequencyReduction.largeRegion_iff B N f T t).mp ht).1)
    ((N : ℝ)^(η/2)) (by
      intro R τ hInside hsep
      simpa only [sum_const,nsmul_eq_mul,mul_one] using hCard N (by omega) B hB f hf R τ T hT hTN hInside hsep)
  have hMeasure : volume.real (TripleLargeFrequencyReduction.largeRegion B N f T) ≤ 4*(N : ℝ)^(η/2) := by
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using hI
  have hLarge := hP N (by omega)
  have hNN := Real.rpow_nonneg (Nat.cast_nonneg N) (η/2)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ 4*(N : ℝ)^(η/2) := hMeasure
    _ ≤ (N : ℝ)^(η/2)*(N : ℝ)^(η/2) := mul_le_mul_of_nonneg_right hLarge hNN
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
end PaperP1.TripleLargeSparseCardinality
