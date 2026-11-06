module

public import PaperP1.Analysis.RoundedAmplificationGeometry
public import PaperP1.Analysis.NarrowBandReciprocalMass
public import PaperP1.Analysis.VariableAmplificationSpan
public import PaperP1.Analysis.VariablePrimePowerLargeValues

set_option autoImplicit false
@[expose] public noncomputable section
universe u828
namespace PaperP1.ActualVariablePrimeLargeValues
open Finset PaperP1
open scoped Classical

theorem sampled_card_bound (H j k : ℕ) (hH : 4 ≤ H)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    {ι : Type u828} (R : Finset ι) (τ : ι → ℝ) (T V : ℝ) (hT : 0 < T) (hV : 0 < V)
    (hTL : T ≤ ((⌈NarrowPrimeBands.anchor H j⌉₊^k : ℕ) : ℝ))
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hLarge : ∀ r ∈ R, V ≤ ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)‖) :
    (R.card : ℝ) ≤ VariableAmplificationSpan.constant*Real.exp (6*((k : ℝ)/(H : ℝ)))*
      (2+9*((k : ℝ)/(H : ℝ))^2)*AmplifiedPrimeProductMean.budget k (NarrowPrimeBands.band H P j)/V^(2*k) := by
  let A := NarrowPrimeBands.band H P j
  let L := ⌈NarrowPrimeBands.anchor H j⌉₊
  let U := ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊
  have hu := NarrowPrimeBands.anchor_pos H j
  have hc := NarrowPrimeBands.growth_one_le H
  have hL : 0 < L := by
    have hh := Nat.one_le_ceil_iff.mpr hu
    change 1 ≤ L at hh
    omega
  have hLU : L ≤ U := Nat.ceil_le_ceil (by nlinarith only [hu,hc])
  have hALU : A ⊆ Icc L U := by
    intro p hp
    have hh := mem_Ico.mp (NarrowBandReciprocalMass.band_interval_subset H (by omega) P
      (fun p hp ↦ (hP p hp).one_le) j hp)
    exact mem_Icc.mpr ⟨hh.1,hh.2.le⟩
  have hprime : ∀ p ∈ A, p.Prime := fun p hp ↦ hP p (NarrowPrimeBands.band_subset H P j hp)
  have hunit : ∀ p ∈ A, ‖f p‖ ≤ 1 := fun p hp ↦ hf p (NarrowPrimeBands.band_subset H P j hp)
  have hHReal : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hanchor2 : 2 ≤ NarrowPrimeBands.anchor H j := by linarith only [hHReal,hj]
  have hMass : (∑ p ∈ A, 1/(p : ℝ)) ≤ 1 := NarrowBandReciprocalMass.mass_le_one H hH P
    (fun p hp ↦ (hP p hp).one_le) j hanchor2
  have hr : 0 ≤ (k : ℝ)/(H : ℝ) := by positivity
  have hspan : ((U^k : ℕ) : ℝ) ≤ Real.exp (3*((k : ℝ)/(H : ℝ)))*((L^k : ℕ) : ℝ) := by
    have hh := VariableAmplificationSpan.rounded_power_bound H (by omega) j k hj
    have he : 3*(k : ℝ)/(H : ℝ)=3*((k : ℝ)/(H : ℝ)) := by ring
    simpa only [he] using hh
  exact VariablePrimePowerLargeValues.sampled_large_values_card k A hprime hMass L U hL hLU hALU
    ((k : ℝ)/(H : ℝ)) hr hspan f hunit R τ T V hT hV hTL htau hsep hLarge
end PaperP1.ActualVariablePrimeLargeValues
