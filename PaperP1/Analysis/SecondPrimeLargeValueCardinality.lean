module

public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.GrowingFirstGoodRegion
public import PaperP1.Analysis.ActualVariablePrimeLargeValues
public import PaperP1.Analysis.CeilingAmplificationOrder
public import PaperP1.Analysis.SecondPrimeCeilingGeometry
public import PaperP1.Analysis.SecondThresholdCardBudget
public import PaperP1.Analysis.VariableAmplificationSpan

set_option autoImplicit false
@[expose] public noncomputable section
universe u832
namespace PaperP1.SecondPrimeLargeValueCardinality
open Finset Filter PaperP1
open scoped Classical

theorem per_block_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      ∀ f : ℕ → ℂ, (∀ p ∈ TwoPrimeBandPopulation.second N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u832} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j)^(-1/40 : ℝ) ≤
        ‖DirichletPolynomialMeanValue.value
          (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) j) f (τ r)‖) →
      (R.card : ℝ) ≤ (N : ℝ)^(1/19 : ℝ) := by
  obtain ⟨NG,hG⟩ := eventually_atTop.mp SecondPrimeCeilingGeometry.eventual_geometry
  obtain ⟨NX,hX⟩ := eventually_atTop.mp
    (SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 100000))
  obtain ⟨NC,hC⟩ := eventually_atTop.mp
    ((Real.tendsto_exp_atTop.comp SlowPrimeBandSieve.lower_tendsto).eventually
      (eventually_ge_atTop VariableAmplificationSpan.constant))
  refine ⟨max 1 (max NG (max NX NC)),by omega,?_⟩
  intro N hN j hj f hf ι R τ T hT hTN htau hsep hLarge
  obtain ⟨hN1,hx4,hH4,hz5,hall⟩ := hG N (by omega)
  obtain ⟨hHq,hq,hlogL,hlogU,hk,hkr,hkz,hkLog,hPower⟩ := hall j hj
  let H := GrowingFirstGoodRegion.width N
  let q := NarrowPrimeBands.anchor H j
  let k := CeilingAmplificationOrder.order N q
  let P := TwoPrimeBandPopulation.second N
  let A := NarrowPrimeBands.band H P j
  have hPrime : ∀ p ∈ P, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hHReal : (4 : ℝ) ≤ H := by exact_mod_cast hH4
  have hAnchor2 : 2 ≤ q := by linarith only [hHq,hHReal]
  have hMass : (∑ p ∈ A, 1/(p : ℝ)) ≤ 1 :=
    NarrowBandReciprocalMass.mass_le_one H hH4 P (fun p hp ↦ (hPrime p hp).one_le) j hAnchor2
  have hV : 0 < q^(-1/40 : ℝ) := Real.rpow_pos_of_pos (by linarith only [hq]) _
  have hMoment := ActualVariablePrimeLargeValues.sampled_card_bound H j k hH4 hHq P hPrime
    f hf R τ T (q^(-1/40 : ℝ)) hT hV (hTN.trans hPower) htau hsep hLarge
  have hLog : Real.log (SlowPrimeBandSieve.upper N)=SlowPrimeBandSieve.lower N := rfl
  have hCe : VariableAmplificationSpan.constant ≤ Real.exp (SlowPrimeBandSieve.lower N) := hC N (by omega)
  have hScalar := SecondThresholdCardBudget.weighted_bound (SlowPrimeBandSieve.lower N)
    (SlowPrimeBandSieve.upper N) VariableAmplificationSpan.constant q (hX N (by omega)) hz5
    hLog hCe hq k H hk (by omega) hkz hkr hkLog A hMass
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ Real.exp (SlowPrimeBandSieve.upper N/19) := hMoment.trans hScalar
    _ = _ := by
      rw [Real.rpow_def_of_pos hNp]
      change Real.exp (Real.log (N : ℝ)/19)=Real.exp (Real.log (N : ℝ)*(1/19))
      congr 1
      ring
end PaperP1.SecondPrimeLargeValueCardinality
