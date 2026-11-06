module

public import PaperP1.Analysis.LognormalSelbergKernel
public import PaperP1.Analysis.LognormalMellinIntegral


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformSelbergKernelEnvelope
open Finset Filter PaperP1
open scoped Classical

def decay (B : ℝ) : ℝ := DilatedFarLognormalKernel.decay (1/8) B

def coefficient (B : ℝ) : ℝ := NearLognormalKernel.constant+FarLognormalKernel.coefficient (2*B)

theorem decay_pos (B : ℝ) : 0 < decay B := DilatedFarLognormalKernel.decay_pos (1/8) B (by norm_num)

theorem decay_le_quarter (B : ℝ) : decay B ≤ 1/4 := DilatedFarLognormalKernel.decay_le_quarter (1/8) B

theorem coefficient_pos (B : ℝ) : 0 < coefficient B :=
  add_pos NearLognormalKernel.constant_pos (FarLognormalKernel.coefficient_pos (2*B))

theorem main_norm (A t : ℝ) (hA : 0 < A) :
    ‖LognormalDilatedKernel.mainValue A t‖=A*Real.sqrt Real.pi*Real.exp (-(t^2/4)) := by
  have hh := LognormalMellinIntegral.integral_norm A t hA
  rw [LognormalMellinIntegral.integral_identity A t hA] at hh
  exact hh

theorem normalized_main_norm (A t : ℝ) (Z : ℕ) (hA : 0 < A) (hZ : 1 ≤ Z) :
    ‖(1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t‖=
      (A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z)*Real.exp (-(t^2/4)) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (PrimeSelbergCoefficients.denominator_pos Z hZ)),main_norm A t hA]
  ring

theorem uniform_bound (B : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ Z : ℕ, 1 ≤ Z → (Z : ℝ)^2 ≤ Real.sqrt A →
      ∀ t : ℝ, |t| ≤ A^B →
        ‖LognormalSelbergKernel.value A t Z‖ ≤
          (A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z)*Real.exp (-(t^2/4))+
          coefficient B*(Z : ℝ)^4*A^(1-decay B) := by
  obtain ⟨A₀,hA₀,hFar⟩ := LognormalSelbergKernel.far_bound (1/8) B (by norm_num) hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA Z hZ hScale t hUpper
  have hA8 : 8 ≤ A := hA₀.trans hA
  have hAP : 0 < A := by linarith only [hA8]
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hZ2 : 0 < (Z : ℝ)^2 := by positivity
  have hG := PrimeSelbergCoefficients.denominator_pos Z hZ
  have hC := NearLognormalKernel.constant_pos
  have hF := FarLognormalKernel.coefficient_pos (2*B)
  have hNearC : NearLognormalKernel.constant ≤ coefficient B := by unfold coefficient; linarith only [hF]
  have hFarC : FarLognormalKernel.coefficient (2*B) ≤ coefficient B := by unfold coefficient; linarith only [hC]
  have hMainNN : 0 ≤ (A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z)*Real.exp (-(t^2/4)) := by positivity
  by_cases hNear : |t| ≤ A^(1/8 : ℝ)
  · have hSqrt : 2 ≤ Real.sqrt A := Real.le_sqrt_of_sq_le (by linarith only [hA8] : (2 : ℝ)^2 ≤ A)
    have hScaled : Real.sqrt A ≤ A/(Z : ℝ)^2 := by
      apply (le_div_iff₀ hZ2).mpr
      calc
        _ ≤ Real.sqrt A*Real.sqrt A := mul_le_mul_of_nonneg_left hScale (Real.sqrt_nonneg A)
        _ = A := Real.mul_self_sqrt hAP.le
    have hLocalScale : 2*(Z : ℝ)^2 ≤ A := (le_div_iff₀ hZ2).mp (hSqrt.trans hScaled)
    have hFrequency : A^(1/8 : ℝ) ≤ (A/(Z : ℝ)^2)^(1/4 : ℝ) := by
      have hh := Real.rpow_le_rpow (Real.sqrt_nonneg A) hScaled (by norm_num : (0 : ℝ) ≤ 1/4)
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hAP.le,show (1/2 : ℝ)*(1/4)=1/8 by norm_num] at hh
      exact hh
    have hBound := LognormalSelbergKernel.near_bound A t Z hZ hAP hLocalScale (hNear.trans hFrequency)
    have hPower := Real.rpow_le_rpow_of_exponent_le hA1
      (show (3/4 : ℝ) ≤ 1-decay B by linarith only [decay_le_quarter B])
    have hError : NearLognormalKernel.constant*(Z : ℝ)^4*A^(3/4 : ℝ) ≤
        coefficient B*(Z : ℝ)^4*A^(1-decay B) := by
      calc
        _ ≤ NearLognormalKernel.constant*(Z : ℝ)^4*A^(1-decay B) :=
          mul_le_mul_of_nonneg_left hPower (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNearC (by positivity))
          (Real.rpow_nonneg hAP.le _)
    have hTriangle : ‖LognormalSelbergKernel.value A t Z‖ ≤
        ‖LognormalSelbergKernel.value A t Z-(1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t‖+
        ‖(1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (LognormalSelbergKernel.value A t Z-(1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t)
        ((1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t)
    calc
      _ ≤ _ := hTriangle
      _ ≤ NearLognormalKernel.constant*(Z : ℝ)^4*A^(3/4 : ℝ)+
          (A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z)*Real.exp (-(t^2/4)) :=
        add_le_add hBound (normalized_main_norm A t Z hAP hZ).le
      _ ≤ coefficient B*(Z : ℝ)^4*A^(1-decay B)+
          (A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z)*Real.exp (-(t^2/4)) := add_le_add hError (le_refl _)
      _ = _ := by ring
  · have hBound := hFar A hA Z hZ hScale t (lt_of_not_ge hNear).le hUpper
    change ‖LognormalSelbergKernel.value A t Z‖ ≤ FarLognormalKernel.coefficient (2*B)*(Z : ℝ)^4*A^(1-decay B) at hBound
    have hError := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFarC (by positivity : 0 ≤ (Z : ℝ)^4))
      (Real.rpow_nonneg hAP.le (1-decay B))
    exact hBound.trans (hError.trans (le_add_of_nonneg_left hMainNN))
end PaperP1.UniformSelbergKernelEnvelope
