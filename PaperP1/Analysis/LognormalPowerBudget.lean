module

public import PaperP1.Analysis.LognormalMiddleEstimate
public import PaperP1.PNT.LogGrowth


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalPowerBudget
open Finset Filter PaperP1
open scoped Classical

def decay (κ B : ℝ) : ℝ := LognormalMiddleEstimate.exponent κ B/2

def logarithmicConstant : ℝ := 2+2/Real.log 2

def coefficient (B : ℝ) : ℝ := logarithmicConstant*LognormalLongCancellation.coefficient (2*B)

theorem decay_pos (κ B : ℝ) (hκ : 0 < κ) : 0 < decay κ B :=
  div_pos (LognormalMiddleEstimate.exponent_pos κ B hκ) (by norm_num)

theorem decay_le_quarter (κ B : ℝ) : decay κ B ≤ 1/4 := by
  have hh := (PolynomialLogarithmicCancellation.decay_bounds (κ/4) (2*B)).2.1
  unfold decay LognormalMiddleEstimate.exponent
  linarith only [hh]

theorem logarithmic_constant_pos : 0 < logarithmicConstant := by
  have hh : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold logarithmicConstant
  positivity

theorem coefficient_pos (B : ℝ) : 0 < coefficient B :=
  mul_pos logarithmic_constant_pos (LognormalLongCancellation.coefficient_pos (2*B))

theorem logarithmic_factor_bound (A : ℝ) (hA : 1 ≤ A) :
    (Real.log 2+2*Real.log A)/Real.log 2+1 ≤ logarithmicConstant*(1+Real.log A) := by
  have hLog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hLogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hRatio : 0 ≤ 2/Real.log (2 : ℝ) := by positivity
  have hIdentity : (Real.log 2+2*Real.log A)/Real.log 2+1=2+(2/Real.log 2)*Real.log A := by
    rw [add_div,div_self hLog2.ne']
    ring
  rw [hIdentity]
  unfold logarithmicConstant
  nlinarith only [hLogA,hRatio]

theorem log_ratio_tendsto (q : ℝ) (hq : 0 < q) :
    Tendsto (fun A : ℝ ↦ (1+Real.log A)/A^q) atTop (nhds 0) := by
  have hInv := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hq)
  have hOne : Tendsto (fun A : ℝ ↦ 1/A^q) atTop (nhds 0) := by
    simpa only [Function.comp_def,one_div] using hInv
  have hLog : Tendsto (fun A : ℝ ↦ Real.log A/A^q) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using PNT.tendsto_pow_log_div_pow_atTop q 1 hq
  simpa only [add_div,zero_add] using hOne.add hLog

theorem uniform_bound (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ t : ℝ,
      A^κ ≤ |t| → |t| ≤ A^B →
      ‖∑ n ∈ Ico ⌈Real.sqrt A⌉₊ ⌈A^2⌉₊, LognormalPhaseVariation.function A t n‖ ≤
        coefficient B*A^(1-decay κ B) := by
  obtain ⟨A₁,hA₁,hMiddle⟩ := LognormalMiddleEstimate.uniform_bound κ B hκ hB
  have hLimit := log_ratio_tendsto (decay κ B) (decay_pos κ B hκ)
  obtain ⟨A₂,hA₂⟩ := eventually_atTop.mp (hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)))
  refine ⟨max A₁ A₂,hA₁.trans (le_max_left _ _),?_⟩
  intro A hA t hLower hUpper
  have hAM : A₁ ≤ A := (le_max_left _ _).trans hA
  have hA8 : 8 ≤ A := hA₁.trans hAM
  have hAP : 0 < A := by linarith only [hA8]
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hPowerP := Real.rpow_pos_of_pos hAP (decay κ B)
  have hLog : 1+Real.log A ≤ A^(decay κ B) :=
    ((div_lt_one hPowerP).mp (hA₂ A ((le_max_right _ _).trans hA))).le
  have hFactor : (Real.log 2+2*Real.log A)/Real.log 2+1 ≤ logarithmicConstant*A^(decay κ B) :=
    (logarithmic_factor_bound A hA1).trans (mul_le_mul_of_nonneg_left hLog logarithmic_constant_pos.le)
  have hC := LognormalLongCancellation.coefficient_pos (2*B)
  have hExponent : LognormalMiddleEstimate.exponent κ B=decay κ B+decay κ B := by
    unfold decay
    ring
  calc
    _ ≤ ((Real.log 2+2*Real.log A)/Real.log 2+1)*LognormalLongCancellation.coefficient (2*B)*A/
        A^(LognormalMiddleEstimate.exponent κ B) := hMiddle A hAM t hLower hUpper
    _ ≤ (logarithmicConstant*A^(decay κ B))*LognormalLongCancellation.coefficient (2*B)*A/
        A^(LognormalMiddleEstimate.exponent κ B) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFactor hC.le) hAP.le)
      (Real.rpow_nonneg hAP.le _)
    _ = _ := by
      rw [hExponent,Real.rpow_add hAP,Real.rpow_sub hAP,Real.rpow_one]
      unfold coefficient
      field_simp [hPowerP.ne']
end PaperP1.LognormalPowerBudget
