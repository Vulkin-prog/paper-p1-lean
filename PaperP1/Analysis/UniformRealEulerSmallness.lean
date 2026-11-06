module

public import PaperP1.Analysis.UniformZetaSublogarithmic
public import PaperP1.Analysis.RealPrimeEulerBound
public import PaperP1.Analysis.DampedEulerZetaComparison
public import PaperP1.Analysis.PositiveZetaBound
public import PaperP1.Analysis.RealEulerDamping

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformRealEulerSmallness
open Finset Filter PaperP1
open scoped Classical

theorem fourth_power_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ X : ℕ, 2 ≤ X → 1 ≤ Real.log (X : ℝ) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ X) → ∀ f : ℕ → ℝ,
      (∀ p ∈ P, |f p| ≤ 1) → ∀ t : ℝ, T₀ ≤ |t| → |t| ≤ (X : ℝ)^B →
      ‖RealPrimeEulerBound.product P f t‖^4 ≤ ε*(Real.log (X : ℝ))^4 := by
  let D := RealEulerDamping.constant
  have hDP : 0 < D := RealEulerDamping.constant_pos
  let η : ℝ := ε/(27*D^4*Real.exp 8)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨T₀,hT₀,hZeta⟩ := UniformZetaSublogarithmic.polynomial_height_bound (B+1) η (by linarith only [hB]) hη
  refine ⟨T₀,hT₀,?_⟩
  intro X hX hLog P hP f hf t ht hUpper
  have hXP : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hLP : 0 < Real.log (X : ℝ) := by linarith only [hLog]
  have hSigma : 1/Real.log (X : ℝ) ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hLog
    simpa only [div_one] using hh
  have hD := RealEulerDamping.logarithmic_norm_comparison X (by omega) hLog P hP f hf t
  have hD4 := pow_le_pow_left₀ (norm_nonneg _) hD 4
  have hFull := DampedEulerZetaComparison.fourth_power_bound P (fun p hp ↦ (hP p hp).1)
    f hf (1/Real.log (X : ℝ)) t (by positivity)
  have hReal := PositiveZetaBound.logarithmic_norm_bound X hLog
  have htP : 0 < |t| := by linarith only [hT₀.trans ht]
  have hTwoLower : T₀ ≤ |2*t| := by rw [abs_mul]; norm_num; linarith only [ht,htP]
  have hTwoUpper : |2*t| ≤ (X : ℝ)^(B+1) := by
    rw [abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (X : ℝ)*(X : ℝ)^B := mul_le_mul (by exact_mod_cast hX) hUpper (abs_nonneg t) (Nat.cast_nonneg X)
      _ = _ := by rw [Real.rpow_add hXP,Real.rpow_one]; ring
  have hShift := hZeta X (by omega) (2*t) hTwoLower hTwoUpper (1/Real.log (X : ℝ)) (by positivity) hSigma
  have hProduct := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hReal 3) hShift (norm_nonneg _) (by positivity)
  have hFinal : ‖RealEulerDamping.product P f (1/Real.log (X : ℝ)) t‖^4 ≤
      Real.exp 8*((3*Real.log (X : ℝ))^3*(η*Real.log (X : ℝ))) := by
    exact hFull.trans (by
      have hh := mul_le_mul_of_nonneg_left hProduct (Real.exp_pos 8).le
      simpa only [mul_assoc] using hh)
  calc
    _ ≤ D^4*‖RealEulerDamping.product P f (1/Real.log (X : ℝ)) t‖^4 := by
      simpa only [mul_pow] using hD4
    _ ≤ D^4*(Real.exp 8*((3*Real.log (X : ℝ))^3*(η*Real.log (X : ℝ)))) :=
      mul_le_mul_of_nonneg_left hFinal (by positivity)
    _ = _ := by
      dsimp only [η]
      field_simp [hDP.ne',(Real.exp_pos (8 : ℝ)).ne']
      ring

theorem uniform_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ X : ℕ, 2 ≤ X → 1 ≤ Real.log (X : ℝ) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ X) → ∀ f : ℕ → ℝ,
      (∀ p ∈ P, |f p| ≤ 1) → ∀ t : ℝ, T₀ ≤ |t| → |t| ≤ (X : ℝ)^B →
      ‖RealPrimeEulerBound.product P f t‖ ≤ ε*Real.log (X : ℝ) := by
  obtain ⟨T₀,hT₀,hBound⟩ := fourth_power_bound B (ε^4) hB (by positivity)
  refine ⟨T₀,hT₀,?_⟩
  intro X hX hLog P hP f hf t ht hUpper
  have hh := hBound X hX hLog P hP f hf t ht hUpper
  rw [← mul_pow] at hh
  exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity) hh
end PaperP1.UniformRealEulerSmallness
