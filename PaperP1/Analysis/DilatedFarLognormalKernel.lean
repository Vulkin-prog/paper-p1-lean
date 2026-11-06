module

public import PaperP1.Analysis.FarLognormalKernel
public import PaperP1.Analysis.LognormalDilatedKernel


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DilatedFarLognormalKernel
open Finset Filter PaperP1
open scoped Classical

def decay (κ B : ℝ) : ℝ := LognormalPowerBudget.decay κ (2*B)

theorem decay_pos (κ B : ℝ) (hκ : 0 < κ) : 0 < decay κ B :=
  LognormalPowerBudget.decay_pos κ (2*B) hκ

theorem decay_le_quarter (κ B : ℝ) : decay κ B ≤ 1/4 :=
  LognormalPowerBudget.decay_le_quarter κ (2*B)

theorem uniform_bound (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ D : ℕ, 1 ≤ D → (D : ℝ) ≤ Real.sqrt A →
      ∀ t : ℝ, A^κ ≤ |t| → |t| ≤ A^B →
        ‖LognormalDilatedKernel.multipleValue A t D‖ ≤
          FarLognormalKernel.coefficient (2*B)*A^(1-decay κ B) := by
  obtain ⟨A₁,hA₁,hFar⟩ := FarLognormalKernel.uniform_bound κ (2*B) hκ (by positivity)
  refine ⟨max 8 (A₁^2),le_max_left _ _,?_⟩
  intro A hA D hD1 hD t hLower hUpper
  have hA8 : 8 ≤ A := (le_max_left _ _).trans hA
  have hAP : 0 < A := by linarith only [hA8]
  have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDP : (0 : ℝ) < D := by linarith only [hD1R]
  have hSqrt : A₁ ≤ Real.sqrt A := (Real.le_sqrt (by linarith only [hA₁]) hAP.le).mpr
    ((le_max_right _ _).trans hA)
  have hScale : Real.sqrt A ≤ A/(D : ℝ) := by
    apply (le_div_iff₀ hDP).mpr
    calc
      _ ≤ Real.sqrt A*Real.sqrt A := mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg A)
      _ = A := Real.mul_self_sqrt hAP.le
  have hCut : A₁ ≤ A/(D : ℝ) := hSqrt.trans hScale
  have hSP : 0 < A/(D : ℝ) := div_pos hAP hDP
  have hSA : A/(D : ℝ) ≤ A := div_le_self hAP.le hD1R
  have hSquare : A ≤ (A/(D : ℝ))^2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg A) hScale 2
    rw [Real.sq_sqrt hAP.le] at hh
    exact hh
  have hFLower : (A/(D : ℝ))^κ ≤ |t| :=
    (Real.rpow_le_rpow hSP.le hSA hκ.le).trans hLower
  have hFUpper : |t| ≤ (A/(D : ℝ))^(2*B) := by
    have hh := Real.rpow_le_rpow hAP.le hSquare hB.le
    rw [← Real.rpow_natCast,← Real.rpow_mul hSP.le] at hh
    exact hUpper.trans hh
  have hExponent : 0 ≤ 1-decay κ B := by linarith only [decay_le_quarter κ B]
  have hPower := Real.rpow_le_rpow hSP.le hSA hExponent
  rw [LognormalDilatedKernel.value_dilation A t D hAP hDP,norm_mul,
    LogarithmicExponentialSum.function_norm,one_mul]
  exact (hFar (A/(D : ℝ)) hCut t hFLower hFUpper).trans
    (mul_le_mul_of_nonneg_left hPower (FarLognormalKernel.coefficient_pos (2*B)).le)
end PaperP1.DilatedFarLognormalKernel
