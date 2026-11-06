module

public import PaperP1.Analysis.LognormalExactTruncation
public import PaperP1.Analysis.LognormalLowerTail
public import PaperP1.Analysis.LognormalUpperTail
public import PaperP1.Analysis.LognormalPowerBudget


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FarLognormalKernel
open Finset Filter PaperP1
open scoped Classical

def coefficient (B : ℝ) : ℝ := Real.exp 4+8*Real.exp 1+LognormalPowerBudget.coefficient B

theorem coefficient_pos (B : ℝ) : 0 < coefficient B := by
  have hh := LognormalPowerBudget.coefficient_pos B
  unfold coefficient
  positivity

theorem uniform_bound (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ t : ℝ,
      A^κ ≤ |t| → |t| ≤ A^B →
      ‖LognormalSumIntegrability.value A t‖ ≤
        coefficient B*A^(1-LognormalPowerBudget.decay κ B) := by
  obtain ⟨A₀,hA₀,hMiddle⟩ := LognormalPowerBudget.uniform_bound κ B hκ hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA t hLower hUpper
  have hA8 : 8 ≤ A := hA₀.trans hA
  have hA2 : 2 ≤ A := by linarith only [hA8]
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hAP : 0 < A := by linarith only [hA8]
  have hN : 1 ≤ ⌈Real.sqrt A⌉₊ := by
    simpa only [ZetaCutoffGeometry.lower,Real.sqrt_eq_rpow] using
      (ZetaCutoffGeometry.lower_bounds (1/2) A (by norm_num) hA1).1
  have hNM : ⌈Real.sqrt A⌉₊ ≤ ⌈A^2⌉₊ := by
    simpa only [ZetaCutoffGeometry.lower,ZetaCutoffGeometry.upper,Real.sqrt_eq_rpow] using
      ZetaCutoffGeometry.ordered (1/2) A (by norm_num) hA1
  have hSplit := LognormalExactTruncation.series_split A t hAP ⌈A^2⌉₊ (by omega)
  rw [LognormalExactTruncation.head_interval_split ⌈Real.sqrt A⌉₊ ⌈A^2⌉₊ hN hNM] at hSplit
  have hHead := LognormalLowerTail.sqrt_head_bound A t hAP
  change ‖∑ n ∈ Icc 1 (⌈Real.sqrt A⌉₊-1), LognormalPhaseVariation.function A t n‖ ≤ Real.exp 4/A at hHead
  have hTail := LognormalUpperTail.square_cutoff_bound A t hA2
  have hPower : 1 ≤ A^(1-LognormalPowerBudget.decay κ B) :=
    Real.one_le_rpow hA1 (by linarith only [LognormalPowerBudget.decay_le_quarter κ B])
  have hInv : 1/A ≤ 1 := (div_le_one hAP).mpr hA1
  have hScale : 1/A ≤ A^(1-LognormalPowerBudget.decay κ B) := hInv.trans hPower
  have hTailC : 0 ≤ Real.exp 4+8*Real.exp 1 := by positivity
  rw [hSplit]
  calc
    _ ≤ (‖∑ n ∈ Icc 1 (⌈Real.sqrt A⌉₊-1), LognormalPhaseVariation.function A t n‖+
        ‖∑ n ∈ Ico ⌈Real.sqrt A⌉₊ ⌈A^2⌉₊, LognormalPhaseVariation.function A t n‖)+
        ‖LognormalUpperTail.tail A t ⌈A^2⌉₊‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (Real.exp 4/A+LognormalPowerBudget.coefficient B*A^(1-LognormalPowerBudget.decay κ B))+
        8*Real.exp 1/A := add_le_add (add_le_add hHead (hMiddle A hA t hLower hUpper)) hTail
    _ = (Real.exp 4+8*Real.exp 1)*(1/A)+
        LognormalPowerBudget.coefficient B*A^(1-LognormalPowerBudget.decay κ B) := by ring
    _ ≤ (Real.exp 4+8*Real.exp 1)*A^(1-LognormalPowerBudget.decay κ B)+
        LognormalPowerBudget.coefficient B*A^(1-LognormalPowerBudget.decay κ B) :=
      add_le_add (mul_le_mul_of_nonneg_left hScale hTailC) (le_refl _)
    _ = _ := by unfold coefficient; ring

theorem power_gain (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ ∃ A₀ : ℝ, 8 ≤ A₀ ∧
      ∀ A ≥ A₀, ∀ t : ℝ, A^κ ≤ |t| → |t| ≤ A^B →
        ‖LognormalSumIntegrability.value A t‖ ≤ C*A^(1-δ) := by
  obtain ⟨A₀,hA₀,hBound⟩ := uniform_bound κ B hκ hB
  exact ⟨coefficient B,coefficient_pos B,LognormalPowerBudget.decay κ B,
    LognormalPowerBudget.decay_pos κ B hκ,LognormalPowerBudget.decay_le_quarter κ B,A₀,hA₀,hBound⟩
end PaperP1.FarLognormalKernel
