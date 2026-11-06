module

public import PaperP1.Analysis.LogarithmicShiftPhase
public import PaperP1.Analysis.ReciprocalDifferenceBounds
public import PaperP1.Analysis.ReciprocalFiniteDifferences

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IteratedLogarithmicPhase
open PaperP1 LogarithmicPhase ReciprocalFiniteDifferences

def logarithm : List ℝ → ℝ → ℝ
  | [],x => -Real.log x
  | h::hs,x => logarithm hs x-logarithm hs (x+h)

def function (hs : List ℝ) (t x : ℝ) : ℂ := phase (logarithm hs x) t

theorem function_norm (hs : List ℝ) (t x : ℝ) : ‖function hs t x‖=1 := phase_norm _ _

theorem function_nil (t x : ℝ) : function [] t x=LogarithmicExponentialSum.function t x := rfl

theorem function_cons (h : ℝ) (hs : List ℝ) (t x : ℝ) :
    function (h::hs) t x=function hs t x*star (function hs t (x+h)) := by
  rw [function,logarithm,function,function,phase_conj,← phase_add]
  congr 1

theorem hasDerivAt_logarithm (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (logarithm hs) (-kernel hs 1 x) x := by
  induction hs generalizing x with
  | nil =>
    convert (Real.hasDerivAt_log hx.ne').neg using 1
    · rfl
    · simp only [kernel,pow_one,one_div]
  | cons h hs ih =>
    have hh0 : 0 ≤ h := hhs h List.mem_cons_self
    have hTail : ∀ v ∈ hs, 0 ≤ v := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    have hxp : 0 < x+h := by linarith only [hx,hh0]
    have hFirst := ih hTail x hx
    have hSecond : HasDerivAt (fun y : ℝ ↦ logarithm hs (y+h)) (-kernel hs 1 (x+h)) x := by
      simpa only [Function.comp_def,id_eq,mul_one,one_smul] using
        (ih hTail (x+h) hxp).scomp x ((hasDerivAt_id x).add_const h)
    convert hFirst.sub hSecond using 1
    · rfl
    · dsimp only [kernel]
      ring

theorem hasDerivAt_function (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (function hs t)
      (function hs t x*((-Complex.I*(t : ℂ))*(kernel hs 1 x : ℂ))) x := by
  have he (y : ℝ) : function hs t y=Complex.exp ((Complex.I*(t : ℂ))*(logarithm hs y : ℂ)) := by
    rw [function,phase]
    congr 1
    ring
  have hh := (((hasDerivAt_logarithm hs hhs x hx).ofReal_comp).const_mul (Complex.I*(t : ℂ))).cexp
  simp_rw [← he] at hh
  convert hh using 1
  push_cast
  ring

theorem derivative_norm (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t x : ℝ) (hx : 0 < x) :
    ‖function hs t x*((-Complex.I*(t : ℂ))*(kernel hs 1 x : ℂ))‖=|t| * kernel hs 1 x := by
  have hSum := ReciprocalDifferenceBounds.shifts_sum_nonneg hs hhs
  have hCoeff := coefficient_nonneg 1 hs hhs
  have hBound := (ReciprocalDifferenceBounds.kernel_bounds hs hhs 1 x hx).1
  have hK : 0 ≤ kernel hs 1 x := (div_nonneg hCoeff (by positivity)).trans hBound
  simp only [norm_mul,function_norm,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hK,one_mul]

theorem hasDerivAt_logarithm_slope (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y ↦ -kernel hs 1 y) (kernel hs 2 x) x := by
  convert (hasDerivAt_kernel hs hhs 1 x hx).neg using 1
  simp only [Nat.cast_one,neg_mul,one_mul,neg_neg]
end PaperP1.IteratedLogarithmicPhase
