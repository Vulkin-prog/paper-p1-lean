module

public import PaperP1.PNT.LogGrowth
public import PaperP1.Analysis.PowerSelbergLevel
public import PaperP1.Analysis.SelbergPrimeOperator
public import PaperP1.Analysis.UniformSelbergKernelEnvelope


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SelbergLogarithmicBudget
open Finset Filter PaperP1
open scoped Classical

def exponent (B : ℝ) : ℝ := min (1/32) (UniformSelbergKernelEnvelope.decay B/8)

def constant (B : ℝ) : ℝ := (2*Real.sqrt Real.pi/exponent B)*SeparatedGaussianBudget.constant+1

theorem exponent_bounds (B : ℝ) :
    0 < exponent B ∧ exponent B ≤ 1/32 ∧ 4*exponent B ≤ UniformSelbergKernelEnvelope.decay B/2 := by
  have hD := UniformSelbergKernelEnvelope.decay_pos B
  have hLeft : exponent B ≤ 1/32 := min_le_left _ _
  have hRight : exponent B ≤ UniformSelbergKernelEnvelope.decay B/8 := min_le_right _ _
  refine ⟨lt_min (by norm_num) (by positivity),hLeft,?_⟩
  linarith only [hRight]

theorem constant_pos (B : ℝ) : 0 < constant B := by
  have hE := (exponent_bounds B).1
  have hL := SeparatedGaussianBudget.constant_pos
  unfold constant
  positivity

theorem budget_bound (B C : ℝ) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ m : ℕ, (m : ℝ) ≤ (Real.log A)^C →
      SelbergPrimeOperator.budget A B (PowerSelbergLevel.level (exponent B) A) m ≤
        constant B*A/Real.log A := by
  let q := UniformSelbergKernelEnvelope.decay B/2
  have hq : 0 < q := div_pos (UniformSelbergKernelEnvelope.decay_pos B) (by norm_num)
  have hCE := UniformSelbergKernelEnvelope.coefficient_pos B
  have hL := SeparatedGaussianBudget.constant_pos
  have hη := (exponent_bounds B).1
  have hη4 : 4*exponent B ≤ q := (exponent_bounds B).2.2
  have hLimit : Tendsto (fun A : ℝ ↦ UniformSelbergKernelEnvelope.coefficient B*(Real.log A)^(C+1)/A^q)
      atTop (nhds 0) := by
    simpa only [mul_zero,mul_div_assoc] using (PNT.tendsto_pow_log_div_pow_atTop q (C+1) hq).const_mul
      (UniformSelbergKernelEnvelope.coefficient B)
  obtain ⟨A₁,hA₁⟩ := eventually_atTop.mp (hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)))
  refine ⟨max 8 A₁,le_max_left _ _,?_⟩
  intro A hA m hCard
  have hA8 : 8 ≤ A := (le_max_left _ _).trans hA
  have hAP : 0 < A := by linarith only [hA8]
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hA1P : 1 < A := by linarith only [hA8]
  have hLog : 0 < Real.log A := Real.log_pos hA1P
  have hPow : 0 < A^q := Real.rpow_pos_of_pos hAP q
  have hSmall : UniformSelbergKernelEnvelope.coefficient B*(Real.log A)^(C+1)/A^q ≤ 1 :=
    (hA₁ A ((le_max_right _ _).trans hA)).le
  have hNum : UniformSelbergKernelEnvelope.coefficient B*(Real.log A)^(C+1) ≤ A^q :=
    (div_le_one hPow).mp hSmall
  have hGrowth : UniformSelbergKernelEnvelope.coefficient B*(Real.log A)^C ≤ A^q/Real.log A := by
    apply (le_div_iff₀ hLog).mpr
    calc
      _ = UniformSelbergKernelEnvelope.coefficient B*((Real.log A)^C*Real.log A) := by ring
      _ = UniformSelbergKernelEnvelope.coefficient B*(Real.log A)^(C+1) := by
        rw [Real.rpow_add hLog,Real.rpow_one]
      _ ≤ _ := hNum
  have hLevel : (PowerSelbergLevel.level (exponent B) A : ℝ)^4 ≤ A^q :=
    (PowerSelbergLevel.level_fourth_bound (exponent B) A hAP).trans
      (Real.rpow_le_rpow_of_exponent_le hA1 hη4)
  have hMerge : A^q*A^(1-UniformSelbergKernelEnvelope.decay B)=A^(1-q) := by
    rw [← Real.rpow_add hAP]
    congr 1
    dsimp only [q]
    ring
  have hError : (m : ℝ)*UniformSelbergKernelEnvelope.coefficient B*
      (PowerSelbergLevel.level (exponent B) A : ℝ)^4*A^(1-UniformSelbergKernelEnvelope.decay B) ≤
      A/Real.log A := by
    calc
      _ ≤ ((Real.log A)^C*UniformSelbergKernelEnvelope.coefficient B)*A^q*
          A^(1-UniformSelbergKernelEnvelope.decay B) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right hCard hCE.le) hLevel (by positivity)
            (mul_nonneg (Real.rpow_nonneg hLog.le C) hCE.le))
          (Real.rpow_nonneg hAP.le _)
      _ = (UniformSelbergKernelEnvelope.coefficient B*(Real.log A)^C)*A^(1-q) := by
        rw [mul_assoc _ (A^q),hMerge]
        ring
      _ ≤ (A^q/Real.log A)*A^(1-q) := mul_le_mul_of_nonneg_right hGrowth (Real.rpow_nonneg hAP.le _)
      _ = (A^q*A^(1-q))/Real.log A := by ring
      _ = _ := by rw [← Real.rpow_add hAP,show q+(1-q)=1 by ring,Real.rpow_one]
  have hMain := mul_le_mul_of_nonneg_right (PowerSelbergLevel.main_bound (exponent B) A hη hA1P) hL.le
  unfold SelbergPrimeOperator.budget
  calc
    _ ≤ ((2*Real.sqrt Real.pi/exponent B)*A/Real.log A)*SeparatedGaussianBudget.constant+A/Real.log A :=
      add_le_add hMain hError
    _ = _ := by unfold constant; ring
end PaperP1.SelbergLogarithmicBudget
