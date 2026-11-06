module

public import PaperP1.Analysis.FixedPowerLargeFrequencyCardinality
public import PaperP1.Analysis.FixedPowerNarrowGeometry
public import PaperP1.Analysis.FixedPowerSamplingGeometry
public import PaperP1.Analysis.PrimeDirichletLogarithmicSamples


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerPrimeSamples
open Finset Filter PaperP1
open scoped Classical

def constant (a : ℝ) : ℝ := PrimeDirichletLogarithmicSamples.constant (4/a)*(4/a^2)

theorem constant_pos (a : ℝ) (ha : 0 < a) : 0 < constant a :=
  mul_pos (PrimeDirichletLogarithmicSamples.constant_pos (4/a)) (by positivity)

theorem uniform_bound {ι : Type*} (a b : ℝ) (ha : 0 < a) (hb : b ≤ 1)
    (H : ℕ) (hH : 4 ≤ H) (hOrder : 2 ≤ a*(H : ℝ)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ p ∈ FixedPowerPrimeBand.primes a b N, ‖f p‖ ≤ 1) →
      ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ T : ℝ, 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∃ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        1/(Real.log (N : ℝ))^100 ≤
          ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f (τ r)‖) →
      ∀ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f (τ r)‖^2) ≤
          constant a/(Real.log (N : ℝ))^2 := by
  obtain ⟨NC,hNC,hCount⟩ := FixedPowerLargeFrequencyCardinality.uniform_bound (ι := ι) a b ha hb H hH hOrder
  obtain ⟨A₀,hA₀,hPrime⟩ := PrimeDirichletLogarithmicSamples.uniform_bound (ι := ι)
    (4/a) (FixedPowerLargeFrequencyCardinality.exponent H+1) (by positivity)
  obtain ⟨NB,hNB,hCardScale⟩ := FixedPowerSamplingGeometry.cardinality_eventually
    a (FixedPowerLargeFrequencyCardinality.exponent H) ha (FixedPowerLargeFrequencyCardinality.exponent_pos H).le
  obtain ⟨NS,hScale⟩ := eventually_atTop.mp (FixedPowerSamplingGeometry.scale_eventually a A₀ ha)
  obtain ⟨NG,hGeometry⟩ := eventually_atTop.mp (FixedPowerNarrowGeometry.eventual_lower a b ha H (by omega))
  refine ⟨max 2 (max NC (max NB (max NS NG))),by omega,?_⟩
  intro N hN f hf R τ T hT hTN htau hsep hLarge j hj
  have hN2 : 2 ≤ N := by omega
  have hNR2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNR1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let P := FixedPowerPrimeBand.primes a b N
  let u := NarrowPrimeBands.anchor H j
  have hLower : (N : ℝ)^(a/2) ≤ u := hGeometry N (by omega) j hj
  have hCut : A₀ ≤ u := hScale N (by omega) u hLower
  have hCardN := hCount N (by omega) f hf R τ T hT hTN htau hsep hLarge
  have hCard : (R.card : ℝ) ≤ (Real.log u)^(FixedPowerLargeFrequencyCardinality.exponent H+1) :=
    hCardScale N (by omega) u hLower R.card hCardN
  have hHeight : ∀ r ∈ R, ∀ s ∈ R, |τ r-τ s| ≤ u^(4/a) := by
    intro r hr s hs
    have hh : |τ r-τ s| ≤ 2*(N : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith only [(htau r hr).1,(htau r hr).2,(htau s hs).1,(htau s hs).2,hTN]
    exact hh.trans (FixedPowerSamplingGeometry.height_power_bound a N u ha hNR2 hLower)
  have hPrimes : ∀ p ∈ NarrowPrimeBands.band H P j, p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ 2*u := by
    intro p hp
    have hpP := NarrowPrimeBands.band_subset H P j hp
    have hpp := (FixedPowerPrimeBand.mem_primes a b N p hpP).1
    have hBounds := NarrowPrimeBands.band_bounds H (by omega) P
      (fun p hp ↦ (FixedPowerPrimeBand.mem_primes a b N p hp).1.one_le) j p hp
    exact ⟨hpp,hBounds.1,hBounds.2.le.trans
      (mul_le_mul_of_nonneg_right (NarrowPrimeBands.growth_le_two H (by omega)) (NarrowPrimeBands.anchor_pos H j).le)⟩
  have hActual := hPrime u hCut R τ hsep hHeight hCard (NarrowPrimeBands.band H P j) hPrimes f
    (fun p hp ↦ hf p (NarrowPrimeBands.band_subset H P j hp))
  have hLog := FixedPowerSamplingGeometry.logarithmic_square_bound a N u ha hNR1 hLower
  have hK := PrimeDirichletLogarithmicSamples.constant_pos (4/a)
  calc
    _ ≤ PrimeDirichletLogarithmicSamples.constant (4/a)/(Real.log u)^2 := hActual
    _ = PrimeDirichletLogarithmicSamples.constant (4/a)*(1/(Real.log u)^2) := by ring
    _ ≤ PrimeDirichletLogarithmicSamples.constant (4/a)*((4/a^2)/(Real.log (N : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hLog hK.le
    _ = _ := by unfold constant; ring
end PaperP1.FixedPowerPrimeSamples
