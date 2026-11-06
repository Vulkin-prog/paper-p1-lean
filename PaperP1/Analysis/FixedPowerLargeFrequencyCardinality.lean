module

public import PaperP1.Analysis.FixedPowerPrimeBand
public import PaperP1.Analysis.FixedOrderPrimeMoment
public import PaperP1.Analysis.FixedPowerNarrowGeometry
public import PaperP1.Analysis.FixedWidthLargeFrequencyCardinality


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerLargeFrequencyCardinality
open Finset Filter PaperP1
open scoped Classical

def exponent (H : ℕ) : ℝ := ((200*H+2 : ℕ) : ℝ)

theorem exponent_pos (H : ℕ) : 0 < exponent H := by unfold exponent; positivity

theorem uniform_bound {ι : Type*} (a b : ℝ) (ha : 0 < a) (hb : b ≤ 1)
    (H : ℕ) (hH : 4 ≤ H) (hOrder : 2 ≤ a*(H : ℝ)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ p ∈ FixedPowerPrimeBand.primes a b N, ‖f p‖ ≤ 1) →
      ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ T : ℝ, 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∃ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        1/(Real.log (N : ℝ))^100 ≤
          ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f (τ r)‖) →
      (R.card : ℝ) ≤ (Real.log (N : ℝ))^(exponent H) := by
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NG,hG⟩ := eventually_atTop.mp (FixedPowerNarrowGeometry.eventual_geometry a b ha H hH hOrder)
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (hLogLimit.eventually
    (eventually_ge_atTop (max 1 (((H : ℝ)+1)*FixedOrderPrimeMoment.constant H))))
  refine ⟨max 1 (max NG NL),by omega,?_⟩
  intro N hN f hf R τ T hT hTN htau hsep hLarge
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hLog : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans (hL N (by omega))
  have hFactor : ((H : ℝ)+1)*FixedOrderPrimeMoment.constant H ≤ Real.log (N : ℝ) :=
    (le_max_right _ _).trans (hL N (by omega))
  have hP : ∀ p ∈ FixedPowerPrimeBand.primes a b N, p.Prime ∧ (p : ℝ) ≤ N := by
    intro p hp
    have hh := FixedPowerPrimeBand.mem_primes a b N p hp
    have hUpper : (N : ℝ)^b ≤ N := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR hb
    exact ⟨hh.1,hh.2.2.trans hUpper⟩
  have hh := FixedWidthLargeFrequencyCardinality.all_blocks_bound H N hH (FixedPowerPrimeBand.primes a b N)
    hP hLog hFactor (hG N (by omega)) f hf R τ T hT hTN htau hsep hLarge
  simpa only [exponent,Real.rpow_natCast] using hh
end PaperP1.FixedPowerLargeFrequencyCardinality
