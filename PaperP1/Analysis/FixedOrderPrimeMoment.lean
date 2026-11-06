module

public import PaperP1.Analysis.NarrowPrimeLargeValues


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedOrderPrimeMoment
open Finset Filter PaperP1
open scoped Classical

def momentConstant (k : ℕ) : ℝ := (k.factorial : ℝ)^2*(16 : ℝ)^k*((k+1 : ℕ) : ℝ)

def constant (H : ℕ) : ℝ := 54*BoundedAmplificationFactor.constant*momentConstant H

theorem moment_constant_pos (k : ℕ) : 0 < momentConstant k := by
  have hh : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  unfold momentConstant
  positivity

theorem budget_bound (k : ℕ) (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    AmplifiedPrimeProductMean.budget k P ≤ momentConstant k := by
  have hNN : 0 ≤ ∑ p ∈ P, 1/(p : ℝ) := sum_nonneg (fun _ _ ↦ by positivity)
  have hPower : (∑ p ∈ P, 1/(p : ℝ))^k ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hNN hMass k
  change momentConstant k*(∑ p ∈ P, 1/(p : ℝ))^k ≤ momentConstant k
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hPower (moment_constant_pos k).le

theorem constant_pos (H : ℕ) : 0 < constant H :=
  mul_pos (mul_pos (by norm_num) BoundedAmplificationFactor.constant_pos) (moment_constant_pos H)

theorem sampled_card_bound {ι : Type*} (H j : ℕ) (hH : 4 ≤ H)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (R : Finset ι) (τ : ι → ℝ) (T V : ℝ) (hT : 0 < T) (hV : 0 < V)
    (hTL : T ≤ (NarrowPrimeBands.anchor H j)^H)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hLarge : ∀ r ∈ R, V ≤ ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)‖) :
    (R.card : ℝ) ≤ constant H/V^(2*H) := by
  have hu := NarrowPrimeBands.anchor_pos H j
  have hRounded := pow_le_pow_left₀ hu.le (Nat.le_ceil (NarrowPrimeBands.anchor H j)) H
  rw [← Nat.cast_pow] at hRounded
  have hMoment := NarrowPrimeLargeValues.sampled_card_bound H j H hH le_rfl hj P hP f hf R τ T V hT hV
    (hTL.trans hRounded) htau hsep hLarge
  have hHR : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hMass := NarrowBandReciprocalMass.mass_le_one H hH P (fun p hp ↦ (hP p hp).one_le) j
    (by linarith only [hHR,hj] : 2 ≤ NarrowPrimeBands.anchor H j)
  have hBudget := budget_bound H (NarrowPrimeBands.band H P j) hMass
  exact hMoment.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBudget (by have hh := BoundedAmplificationFactor.constant_pos; positivity))
    (pow_nonneg hV.le _))

theorem threshold_bound {ι : Type*} (H j : ℕ) (hH : 4 ≤ H)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (R : Finset ι) (τ : ι → ℝ) (T z : ℝ) (hT : 0 < T) (hz : 0 < z)
    (hTL : T ≤ (NarrowPrimeBands.anchor H j)^H)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hLarge : ∀ r ∈ R, 1/z^100 ≤ ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)‖) :
    (R.card : ℝ) ≤ constant H*z^(200*H) := by
  have hh := sampled_card_bound H j hH hj P hP f hf R τ T (1/z^100) hT (by positivity) hTL htau hsep hLarge
  have he : constant H/(1/z^100)^(2*H)=constant H*z^(200*H) := by
    rw [div_eq_mul_inv]
    simp only [one_div,inv_pow,inv_inv]
    rw [← pow_mul,show 100*(2*H)=200*H by omega]
  exact hh.trans_eq he
end PaperP1.FixedOrderPrimeMoment
