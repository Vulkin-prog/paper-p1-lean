module

public import PaperP1.Analysis.LogarithmicPhase
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-! # An actual Gaussian-Laplace kernel with checked Fubini and positive normalization -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GaussianLaplaceKernel
open MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

def vertical (t : ℝ) : ℂ := 1+Complex.I*(t : ℂ)

def laplace (t u : ℝ) : ℂ := (Real.exp (-u) : ℂ)*phase (-u) t

def joint (b v : ℝ) (z : ℝ × ℝ) : ℂ :=
  (Real.exp (-b*z.1^2) : ℂ)*(Real.exp (-z.2) : ℂ)*phase (v-z.2) z.1

theorem laplace_eq_exp (t u : ℝ) : laplace t u=Complex.exp ((-vertical t)*(u : ℂ)) := by
  unfold laplace phase vertical
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem laplace_integrable (t : ℝ) : IntegrableOn (laplace t) (Set.Ioi 0) := by
  have hh := integrableOn_exp_mul_complex_Ioi (a := -vertical t) (by simp [vertical]) 0
  simpa only [← laplace_eq_exp] using hh

theorem laplace_integral (t : ℝ) : (∫ u in Set.Ioi 0, laplace t u)=1/vertical t := by
  simp_rw [laplace_eq_exp]
  rw [integral_exp_mul_complex_Ioi (a := -vertical t) (by simp [vertical]) 0]
  simp

theorem joint_integrable (b v : ℝ) (hb : 0 < b) :
    Integrable (joint b v) (volume.prod (volume.restrict (Set.Ioi 0))) := by
  have hh := (integrable_exp_neg_mul_sq hb).mul_prod (integrableOn_exp_neg_Ioi 0)
  have hc : Continuous (joint b v) := by unfold joint phase; fun_prop
  apply hh.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  simp only [joint,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact le_rfl

theorem joint_integral_right (b v t : ℝ) :
    (∫ u in Set.Ioi 0, joint b v (t,u))=(Real.exp (-b*t^2) : ℂ)*phase v t/vertical t := by
  have he (u : ℝ) : joint b v (t,u)=(Real.exp (-b*t^2) : ℂ)*phase v t*laplace t u := by
    dsimp only [joint,laplace]
    rw [sub_eq_add_neg,phase_add]
    ring
  simp_rw [he]
  rw [integral_const_mul,laplace_integral]
  ring

theorem joint_integral_left (b v u : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, joint b v (t,u))=
      (Real.exp (-u) : ℂ)*(Real.sqrt (Real.pi/b) : ℂ)*
        (Real.exp (-(v-u)^2/(4*b)) : ℂ) := by
  have he (t : ℝ) : joint b v (t,u)=(Real.exp (-u) : ℂ)*
      (phase (v-u) t*Complex.exp (-(b : ℂ)*(t : ℂ)^2)) := by
    have hg : (Real.exp (-b*t^2) : ℂ)=Complex.exp (-(b : ℂ)*(t : ℂ)^2) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [joint,hg]
    ring
  simp_rw [he]
  rw [integral_const_mul,gaussian_integral b (v-u) hb]
  have heq : Complex.exp (-(((v-u)^2/(4*b) : ℝ) : ℂ))=
      (Real.exp (-(v-u)^2/(4*b)) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [heq]
  ring

def rawKernel (b v : ℝ) : ℂ :=
  ∫ t : ℝ, (Real.exp (-b*t^2) : ℂ)*phase v t/vertical t

def realKernel (b v : ℝ) : ℝ :=
  Real.sqrt (Real.pi/b)*(∫ u in Set.Ioi 0, Real.exp (-u)*Real.exp (-(v-u)^2/(4*b)))

theorem raw_eq_real (b v : ℝ) (hb : 0 < b) : rawKernel b v=(realKernel b v : ℂ) := by
  have hh : (∫ t : ℝ, ∫ u in Set.Ioi 0, joint b v (t,u))=
      ∫ u in Set.Ioi 0, ∫ t : ℝ, joint b v (t,u) :=
    integral_integral_swap (joint_integrable b v hb)
  simp_rw [joint_integral_right,joint_integral_left b v _ hb] at hh
  have he : (fun u : ℝ ↦ (Real.exp (-u) : ℂ)*(Real.sqrt (Real.pi/b) : ℂ)*
      (Real.exp (-(v-u)^2/(4*b)) : ℂ))=
      (fun u : ℝ ↦ (Real.sqrt (Real.pi/b) : ℂ)*
        ((Real.exp (-u)*Real.exp (-(v-u)^2/(4*b)) : ℝ) : ℂ)) := by
    funext u
    push_cast
    ring
  rw [he,integral_const_mul,integral_complex_ofReal,← Complex.ofReal_mul] at hh
  exact hh

theorem realKernel_nonneg (b v : ℝ) : 0 ≤ realKernel b v := by
  unfold realKernel
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply integral_nonneg
  intro u
  positivity

theorem raw_norm_eq_real (b v : ℝ) (hb : 0 < b) : ‖rawKernel b v‖=realKernel b v := by
  rw [raw_eq_real b v hb,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (realKernel_nonneg b v)]

def gaussian (b c u : ℝ) : ℝ := Real.exp (-(u-c)^2/(4*b))

def prefactor (b : ℝ) : ℝ := Real.sqrt (Real.pi/b)/(2*Real.pi)

def kernel (b v : ℝ) : ℝ := Real.exp v/(2*Real.pi)*realKernel b v

theorem gaussian_integrable (b c : ℝ) (hb : 0 < b) : Integrable (gaussian b c) := by
  have hh := (integrable_exp_neg_mul_sq (by positivity : 0 < 1/(4*b))).comp_sub_right c
  convert hh using 1
  funext u
  dsimp only [gaussian]
  congr 1
  ring

theorem gaussian_integral_real (b c : ℝ) :
    (∫ u : ℝ, gaussian b c u)=Real.sqrt (Real.pi/(1/(4*b))) := by
  calc
    _ = ∫ u : ℝ, Real.exp (-(1/(4*b))*(u-c)^2) := by
      congr 1
      funext u
      dsimp only [gaussian]
      congr 1
      ring
    _ = ∫ u : ℝ, Real.exp (-(1/(4*b))*u^2) := by
      simpa only using (integral_sub_right_eq_self (μ := volume)
        (fun u : ℝ ↦ Real.exp (-(1/(4*b))*u^2)) c)
    _ = _ := integral_gaussian _

theorem prefactor_pos (b : ℝ) (hb : 0 < b) : 0 < prefactor b := by
  dsimp only [prefactor]
  positivity

theorem gaussian_normalized (b c : ℝ) (hb : 0 < b) :
    prefactor b*(∫ u : ℝ, gaussian b c u)=1 := by
  rw [gaussian_integral_real b c]
  unfold prefactor
  have hr : Real.sqrt (Real.pi/b)*Real.sqrt (Real.pi/(1/(4*b)))=2*Real.pi := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi/b)]
    have he : (Real.pi/b)*(Real.pi/(1/(4*b)))=(2*Real.pi)^2 := by field_simp; ring
    rw [he,Real.sqrt_sq (by positivity : 0 ≤ 2*Real.pi)]
  calc
    _ = (Real.sqrt (Real.pi/b)*Real.sqrt (Real.pi/(1/(4*b))))/(2*Real.pi) := by ring
    _ = _ := by rw [hr]; field_simp

theorem kernel_completed_square (b v : ℝ) (hb : 0 < b) :
    kernel b v=Real.exp b*prefactor b*(∫ u in Set.Ioi 0, gaussian b (v-2*b) u) := by
  have he (u : ℝ) : Real.exp v*(Real.exp (-u)*Real.exp (-(v-u)^2/(4*b)))=
      Real.exp b*gaussian b (v-2*b) u := by
    rw [gaussian,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    field_simp
    ring
  calc
    _ = prefactor b*(∫ u in Set.Ioi 0,
        Real.exp v*(Real.exp (-u)*Real.exp (-(v-u)^2/(4*b)))) := by
      rw [integral_const_mul]
      dsimp only [kernel,realKernel,prefactor]
      ring
    _ = prefactor b*(∫ u in Set.Ioi 0, Real.exp b*gaussian b (v-2*b) u) := by simp_rw [he]
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_nonneg (b v : ℝ) : 0 ≤ kernel b v := by
  dsimp only [kernel]
  exact mul_nonneg (by positivity) (realKernel_nonneg b v)

theorem kernel_le_exp (b v : ℝ) (hb : 0 < b) : kernel b v ≤ Real.exp b := by
  rw [kernel_completed_square b v hb]
  have hh := setIntegral_le_integral (gaussian_integrable b (v-2*b) hb)
    (Filter.Eventually.of_forall (fun u ↦ (Real.exp_pos _).le)) (s := Set.Ioi 0)
  calc
    _ ≤ Real.exp b*prefactor b*(∫ u : ℝ, gaussian b (v-2*b) u) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.exp_pos _).le (prefactor_pos b hb).le)
    _ = Real.exp b*(prefactor b*(∫ u : ℝ, gaussian b (v-2*b) u)) := by ring
    _ = _ := by rw [gaussian_normalized b (v-2*b) hb,mul_one]

theorem raw_integrable (b v : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ ↦ (Real.exp (-b*t^2) : ℂ)*phase v t/vertical t) := by
  have hh := (joint_integrable b v hb).integral_prod_left
  simpa only [joint_integral_right] using hh

theorem vertical_norm (t : ℝ) : ‖vertical t‖=Real.sqrt (1+t^2) := by
  simp [vertical,Complex.norm_def,Complex.normSq_apply,pow_two]

theorem vertical_ne_zero (t : ℝ) : vertical t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [vertical_norm]
  positivity

theorem kernel_complex_formula (b v : ℝ) (hb : 0 < b) :
    (kernel b v : ℂ)=((Real.exp v/(2*Real.pi) : ℝ) : ℂ)*rawKernel b v := by
  rw [raw_eq_real b v hb,← Complex.ofReal_mul]
  rfl
end PaperP1.GaussianLaplaceKernel




