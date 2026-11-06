module

public import PaperP1.Analysis.LognormalMellinIntegral
public import PaperP1.Analysis.LognormalSumIntegrability
public import PaperP1.Analysis.LognormalPhaseVariation
public import PaperP1.Analysis.LognormalExactTruncation
public import PaperP1.Analysis.LognormalFiniteQuadrature
public import PaperP1.Analysis.LognormalIntegralTails
public import PaperP1.Analysis.LognormalLowerTail
public import PaperP1.Analysis.LognormalUpperTail
public import PaperP1.Analysis.LognormalWeightVariation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalMellinError
open Finset Filter MeasureTheory PaperP1 LognormalPhaseVariation
open scoped Classical

def constant : ℝ := 5*Real.exp 4+9*Real.exp 1

theorem constant_pos : 0 < constant := by unfold constant; positivity

theorem difference_bound (A t : ℝ) (hA : 2 ≤ A) :
    ‖LognormalSumIntegrability.value A t-(∫ x in Set.Ioi (0 : ℝ), function A t x)‖ ≤
      constant/A+2*(LognormalWeightVariation.constant+|t|)*Real.sqrt A := by
  have hAP : 0 < A := by linarith only [hA]
  let N : ℕ := ⌈Real.sqrt A⌉₊
  let M : ℕ := ⌈A^2⌉₊
  have hNP : 0 < N := Nat.ceil_pos.mpr (Real.sqrt_pos.mpr hAP)
  have hMP : 0 < M := Nat.ceil_pos.mpr (sq_pos_of_pos hAP)
  have hNM : N ≤ M := by
    apply Nat.ceil_mono
    have hSA : Real.sqrt A ≤ A := (Real.sqrt_le_left hAP.le).mpr (by nlinarith only [hA])
    exact hSA.trans (by nlinarith only [hA] : A ≤ A^2)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNP
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMP
  let headPart := ∑ n ∈ Icc 1 (N-1), function A t n
  let middlePart := ∑ n ∈ Ico N M, function A t n
  let tailPart := LognormalUpperTail.tail A t M
  let lowIntegral := ∫ x in (0 : ℝ)..(N : ℝ), function A t x
  let middleIntegral := ∫ x in (N : ℝ)..(M : ℝ), function A t x
  let highIntegral := ∫ x in Set.Ioi (M : ℝ), function A t x
  have hSeries : LognormalSumIntegrability.value A t=(headPart+middlePart)+tailPart := by
    have hh := LognormalExactTruncation.series_split A t hAP M (by omega)
    rw [LognormalExactTruncation.head_interval_split N M (by omega) hNM] at hh
    exact hh
  have hIntegral : (∫ x in Set.Ioi (0 : ℝ), function A t x)=(lowIntegral+middleIntegral)+highIntegral :=
    LognormalExactTruncation.integral_split A t N M hAP hNR hMR
  have hDifference : LognormalSumIntegrability.value A t-(∫ x in Set.Ioi (0 : ℝ), function A t x)=
      ((headPart-lowIntegral)+(middlePart-middleIntegral))+(tailPart-highIntegral) := by
    rw [hSeries,hIntegral]
    abel
  have hHead : ‖headPart‖ ≤ Real.exp 4/A := LognormalLowerTail.sqrt_head_bound A t hAP
  have hLow : ‖lowIntegral‖ ≤ 4*Real.exp 4/A := LognormalIntegralTails.sqrt_cutoff_bound A t (by linarith only [hA])
  have hMiddle : ‖middlePart-middleIntegral‖ ≤
      2*(LognormalWeightVariation.constant+|t|)*Real.sqrt A :=
    LognormalFiniteQuadrature.sqrt_cutoff_error A t hAP M hNM
  have hTail : ‖tailPart‖ ≤ 8*Real.exp 1/A := LognormalUpperTail.square_cutoff_bound A t hA
  have hHigh : ‖highIntegral‖ ≤ Real.exp 1/A :=
    (LognormalIntegralTails.square_cutoff_bound A t hAP).trans
      (div_le_div_of_nonneg_left (Real.exp_pos 1).le hAP (by linarith only [hAP] : A ≤ 2*A))
  rw [hDifference]
  calc
    _ ≤ ‖headPart-lowIntegral‖+‖middlePart-middleIntegral‖+‖tailPart-highIntegral‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (Real.exp 4/A+4*Real.exp 4/A)+
        2*(LognormalWeightVariation.constant+|t|)*Real.sqrt A+(8*Real.exp 1/A+Real.exp 1/A) :=
      add_le_add (add_le_add ((norm_sub_le _ _).trans (add_le_add hHead hLow)) hMiddle)
        ((norm_sub_le _ _).trans (add_le_add hTail hHigh))
    _ = _ := by unfold constant; ring

theorem value_norm_bound (A t : ℝ) (hA : 2 ≤ A) :
    ‖LognormalSumIntegrability.value A t‖ ≤
      A*Real.sqrt Real.pi*Real.exp (-(t^2/4))+constant/A+
        2*(LognormalWeightVariation.constant+|t|)*Real.sqrt A := by
  let I := ∫ x in Set.Ioi (0 : ℝ), function A t x
  have hTriangle : ‖LognormalSumIntegrability.value A t‖ ≤
      ‖LognormalSumIntegrability.value A t-I‖+‖I‖ := by
    simpa only [sub_add_cancel] using norm_add_le (LognormalSumIntegrability.value A t-I) I
  have hDifference := difference_bound A t hA
  have hIntegral : ‖I‖=A*Real.sqrt Real.pi*Real.exp (-(t^2/4)) :=
    LognormalMellinIntegral.integral_norm A t (by linarith only [hA])
  exact hTriangle.trans ((add_le_add hDifference hIntegral.le).trans_eq (by ring))
end PaperP1.LognormalMellinError
