module

public import PaperP1.Analysis.JointLargeSparseCofactors
public import PaperP1.Analysis.FiniteProductSampleBound
public import PaperP1.Analysis.FixedPowerNarrowGeometry
public import PaperP1.Analysis.FixedWidthLargeFrequencyCardinality


set_option autoImplicit false
@[expose] public noncomputable section
universe u945
namespace PaperP1.FixedPowerSmallSamples
open Finset Filter PaperP1
open scoped Classical

def envelope (H N : ℕ) : ℝ := 20*((H : ℝ)+1)^2/(Real.log (N : ℝ))^197

theorem scalar_bound (H : ℕ) (z c : ℝ) (hz : 1 ≤ z) (hc0 : 0 ≤ c) (hc : c ≤ ((H : ℝ)+1)*z) :
    c^2*(1/z^100)^2*(10*(1+z)) ≤ 20*((H : ℝ)+1)^2/z^197 := by
  have hzp : 0 < z := by linarith only [hz]
  have hSq := pow_le_pow_left₀ hc0 hc 2
  have hOne : 1+z ≤ 2*z := by linarith only [hz]
  calc
    _ ≤ (((H : ℝ)+1)*z)^2*(1/z^100)^2*(10*(2*z)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hSq (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hOne (by norm_num : (0 : ℝ) ≤ 10)) (by positivity) (by positivity)
    _ = _ := by field_simp [hzp.ne']; ring

theorem envelope_tendsto (H : ℕ) : Tendsto (envelope H) atTop (nhds 0) := by
  change Tendsto (fun N : ℕ ↦ 20*((H : ℝ)+1)^2/(Real.log (N : ℝ))^197) atTop (nhds 0)
  have hLog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := ((tendsto_inv_atTop_zero.comp hLog).pow 197).const_mul (20*((H : ℝ)+1)^2)
  simpa only [Function.comp_def,div_eq_mul_inv,inv_pow,zero_pow (by decide : 197 ≠ 0),mul_zero] using hh

theorem sampled_bound {ι : Type u945} (a b : ℝ) (hb : b ≤ 1/16) (H : ℕ) (hH : 4 ≤ H) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ JointLargeFrequencyReduction.largeRegion N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∀ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f (τ r)‖ ≤
          1/(Real.log (N : ℝ))^100) →
      (∑ r ∈ R, ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q f (τ r)‖^2) ≤ envelope H N := by
  obtain ⟨NS,hNS,hSample⟩ := JointLargeSparseCofactors.cofactor_mean_uniform.{u945}
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop 1))
  refine ⟨max 2 (max NS NL),by omega,?_⟩
  intro N hN Q f hf R τ T hT hTN hInside hsep hSmall
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hLog1 : 1 ≤ Real.log (N : ℝ) := hLog N (by omega)
  let P := FixedPowerPrimeBand.primes a b N
  let J := NarrowPrimeBands.indices H P
  let A (j : ℕ) (r : ι) := DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)
  let F (j : ℕ) (r : ι) := DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N H j)
    (NarrowRamareRectangle.coefficient P Q f) (τ r)
  have hfSecond : ∀ p ∈ TwoPrimeBandPopulation.second N, ‖f p‖ ≤ 1 := fun p hp ↦ hf p (mem_filter.mp hp).2.pos
  have hCof (j : ℕ) (hj : j ∈ J) : (∑ r ∈ R, ‖F j r‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
    apply hSample N (by omega) f hfSecond R τ T hT hTN hInside hsep H j
      (FixedPowerNarrowGeometry.upper_anchor a b H N j (by omega) hN1 hb hj) P Q f
    intro n hn
    apply hf n
    have hh := (mem_Icc.mp (mem_filter.mp hn).1).1
    omega
  have hProduct := FiniteProductSampleBound.bound J R A F (1/(Real.log (N : ℝ))^100) (10*(1+Real.log (N : ℝ)))
    (fun j hj r hr ↦ hSmall r hr j hj) hCof
  have hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ N := by
    intro p hp
    have hh := FixedPowerPrimeBand.mem_primes a b N p hp
    have hUpper : (N : ℝ)^b ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR (show b ≤ 1 by linarith only [hb])
    exact ⟨hh.1,hh.2.2.trans hUpper⟩
  have hJ : (J.card : ℝ) ≤ ((H : ℝ)+1)*Real.log (N : ℝ) := FixedWidthLargeFrequencyCardinality.index_card_bound H N P hP hLog1
  have hScalar := scalar_bound H (Real.log (N : ℝ)) (J.card : ℝ) hLog1 (Nat.cast_nonneg _) hJ
  exact hProduct.trans hScalar

theorem sampled_small_uniform {ι : Type u945} (a b : ℝ) (hb : b ≤ 1/16) (H : ℕ) (hH : 4 ≤ H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ JointLargeFrequencyReduction.largeRegion N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∀ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f (τ r)‖ ≤
          1/(Real.log (N : ℝ))^100) →
      (∑ r ∈ R, ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q f (τ r)‖^2) ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := sampled_bound (ι := ι) a b hb H hH
  obtain ⟨NE,hE⟩ := eventually_atTop.mp ((envelope_tendsto H).eventually (eventually_lt_nhds hε))
  refine ⟨max NB NE,by omega,?_⟩
  intro N hN Q f hf R τ T hT hTN hInside hsep hSmall
  exact (hBound N (by omega) Q f hf R τ T hT hTN hInside hsep hSmall).trans (hE N (by omega)).le
end PaperP1.FixedPowerSmallSamples
