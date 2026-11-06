module

public import PaperP1.Analysis.FinalPrimeOrderGeometry
public import PaperP1.Analysis.NarrowPrimeLargeValues
public import PaperP1.Analysis.FinalSmallPrimeSamples
public import PaperP1.Analysis.FinalPrimeCardBudget

set_option autoImplicit false
@[expose] public noncomputable section
universe u843
namespace PaperP1.FinalPrimeLargeValueCardinality
open Finset Filter PaperP1
open scoped Classical

theorem per_block_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ,
      ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N),
      ∀ f : ℕ → ℂ, (∀ p ∈ FinalPrimeBandGeometry.primes B N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u843} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, FinalSmallPrimeSamples.threshold N ≤
        ‖DirichletPolynomialMeanValue.value
          (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) j) f (τ r)‖) →
      (R.card : ℝ) ≤ Real.exp (1000*(SlowPrimeBandSieve.lower N)^2) := by
  obtain ⟨NG,hG⟩ := eventually_atTop.mp FinalPrimeOrderGeometry.eventual_geometry
  obtain ⟨NP,hP⟩ := eventually_atTop.mp (PowerLogPrimeBand.geometry_eventually 5 (by norm_num))
  have hPow : Tendsto (fun N : ℕ ↦ (SlowPrimeBandSieve.lower N)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp SlowPrimeBandSieve.lower_tendsto
  obtain ⟨NC,hC⟩ := eventually_atTop.mp ((Real.tendsto_exp_atTop.comp hPow).eventually
    (eventually_ge_atTop (54*BoundedAmplificationFactor.constant)))
  refine ⟨max 1 (max NG (max NP NC)),by omega,?_⟩
  intro N hN B j hj f hf ι R τ T hT hTN htau hsep hLarge
  obtain ⟨hN1,hx,hH,hall⟩ := hG N (by omega)
  obtain ⟨hHu,hu,hlogu,hkH,hkR,hPower⟩ := hall B j hj
  let H := GrowingFirstGoodRegion.width N
  let u := NarrowPrimeBands.anchor H j
  let k := CeilingAmplificationOrder.order N u
  let P := FinalPrimeBandGeometry.primes B N
  let A := NarrowPrimeBands.band H P j
  have hPrime : ∀ p ∈ P, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hHReal : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hAnchor2 : 2 ≤ u := by linarith only [hHu,hHReal]
  have hMass : (∑ p ∈ A, 1/(p : ℝ)) ≤ 1 :=
    NarrowBandReciprocalMass.mass_le_one H hH P (fun p hp ↦ (hPrime p hp).one_le) j hAnchor2
  have hz5 : (SlowPrimeBandSieve.lower N)^5 ≤ SlowPrimeBandSieve.upper N := (hP N (by omega)).2
  have hxp : 0 < SlowPrimeBandSieve.lower N := by linarith only [hx]
  have hzp : 0 < SlowPrimeBandSieve.upper N := (pow_pos hxp 5).trans_le hz5
  have hV : 0 < FinalSmallPrimeSamples.threshold N := by unfold FinalSmallPrimeSamples.threshold; positivity
  have hMoment := NarrowPrimeLargeValues.sampled_card_bound H j k hH hkH hHu P hPrime
    f hf R τ T (FinalSmallPrimeSamples.threshold N) hT hV (hTN.trans hPower) htau hsep hLarge
  have hK : (k : ℝ) ≤ 3*SlowPrimeBandSieve.lower N := by linarith only [hkR,hx]
  have hScalar := FinalPrimeCardBudget.weighted_bound (SlowPrimeBandSieve.lower N)
    (SlowPrimeBandSieve.upper N) (54*BoundedAmplificationFactor.constant) hx hz5 rfl
    (hC N (by omega)) k hK A hMass
  exact hMoment.trans hScalar
end PaperP1.FinalPrimeLargeValueCardinality
