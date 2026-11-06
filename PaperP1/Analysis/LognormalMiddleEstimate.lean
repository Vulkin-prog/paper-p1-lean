module

public import PaperP1.Analysis.ZetaCutoffGeometry
public import PaperP1.Analysis.LognormalPhaseVariation
public import PaperP1.Analysis.LognormalLongCancellation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalMiddleEstimate
open Finset Filter PaperP1 PolynomialLogarithmicCancellation ZetaCutoffGeometry
open scoped Classical

def exponent (κ B : ℝ) : ℝ := decay (κ/4) (2*B)/2

theorem exponent_pos (κ B : ℝ) (hκ : 0 < κ) : 0 < exponent κ B :=
  div_pos (decay_pos (κ/4) (2*B) (by positivity)) (by norm_num)

theorem uniform_bound (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ t : ℝ,
      A^κ ≤ |t| → |t| ≤ A^B →
      ‖∑ n ∈ Ico ⌈Real.sqrt A⌉₊ ⌈A^2⌉₊, LognormalPhaseVariation.function A t n‖ ≤
        ((Real.log 2+2*Real.log A)/Real.log 2+1)*LognormalLongCancellation.coefficient (2*B)*A/
          A^(exponent κ B) := by
  obtain ⟨N₀,hN₀,hLong⟩ := LognormalLongCancellation.uniform_bound (κ/4) (2*B) (by positivity) (by positivity)
  obtain ⟨A₁,hA₁⟩ := eventually_atTop.mp (lower_eventually (1/2) (by norm_num) N₀)
  refine ⟨max 8 A₁,le_max_left _ _,?_⟩
  intro A hA t hLower hUpper
  have hA8 : 8 ≤ A := (le_max_left _ _).trans hA
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hAP : 0 < A := by linarith only [hA8]
  let N := lower (1/2) A
  let M := upper A
  have hCut : N₀ ≤ N := hA₁ A ((le_max_right _ _).trans hA)
  have hNM : N ≤ M := ordered (1/2) A (by norm_num) hA1
  have hProduct : (((2*M*N : ℕ) : ℝ)) ≤ A^4 := product_bound (1/2) A (by norm_num) (by norm_num) hA8
  have hFrequencyLower : (((2*M*N : ℕ) : ℝ))^(κ/4) ≤ |t| := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg _) hProduct (by positivity : 0 ≤ κ/4)
    have he : (A^4)^(κ/4)=A^κ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hAP.le]
      congr 1
      ring
    exact (hh.trans_eq he).trans hLower
  have hBase : A ≤ (N : ℝ)^(2 : ℝ) := by
    have hh := upper_frequency (1/2) A (by norm_num) hA1
    norm_num at hh
    simpa only [Real.rpow_two] using hh
  have hFrequencyUpper : |t| ≤ (N : ℝ)^(2*B) := by
    have hh := Real.rpow_le_rpow hAP.le hBase hB.le
    rw [← Real.rpow_mul (Nat.cast_nonneg N)] at hh
    exact hUpper.trans hh
  have hBound := hLong N hCut M hNM t hFrequencyLower hFrequencyUpper A hAP
  have hLowerCut := (lower_bounds (1/2) A (by norm_num) hA1).2.1
  have hPower : A^(exponent κ B) ≤ (N : ℝ)^(decay (κ/4) (2*B)) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hAP.le (1/2 : ℝ)) hLowerCut
      (decay_pos (κ/4) (2*B) (by positivity)).le
    rw [← Real.rpow_mul hAP.le] at hh
    rw [show (1/2 : ℝ)*decay (κ/4) (2*B)=decay (κ/4) (2*B)/2 by ring] at hh
    exact hh
  have hLog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hLogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hLog := div_le_div_of_nonneg_right (logarithmic_upper A hA1) hLog2.le
  have hCP := LognormalLongCancellation.coefficient_pos (2*B)
  have hFactor : 0 ≤ ((Real.log 2+2*Real.log A)/Real.log 2+1)*LognormalLongCancellation.coefficient (2*B)*A := by positivity
  rw [Real.sqrt_eq_rpow]
  calc
    _ ≤ (Real.log (M : ℝ)/Real.log 2+1)*LognormalLongCancellation.coefficient (2*B)*A/
        (N : ℝ)^(decay (κ/4) (2*B)) := hBound
    _ ≤ ((Real.log 2+2*Real.log A)/Real.log 2+1)*LognormalLongCancellation.coefficient (2*B)*A/
        (N : ℝ)^(decay (κ/4) (2*B)) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (add_le_add hLog (le_refl 1)) hCP.le) hAP.le)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ ≤ _ := div_le_div_of_nonneg_left hFactor (Real.rpow_pos_of_pos hAP _) hPower
end PaperP1.LognormalMiddleEstimate
