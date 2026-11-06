module

public import PaperP1.Analysis.DirichletPolynomialMeanValue


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianDirichletTail
open Finset MeasureTheory PaperP1 GaussianExponentialSums GaussianFrequencyRowBound
open scoped Classical

def budget (N : ℕ) (b : ℝ) : ℝ := Real.sqrt (Real.pi/b)/(N : ℝ)+4*Real.pi

theorem gaussian_bound (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, Real.exp (-b*t^2)*‖DirichletPolynomialMeanValue.value S a t‖^2) ≤ budget N b := by
  let δ : ℝ := 1/(2*(N : ℝ))
  let L : ℝ := 1+Real.sqrt (Real.pi/(δ^2/(4*b)))
  have hNP : 0 < (N : ℝ) := by exact_mod_cast hN
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hrow : ∀ i ∈ S, (∑ j ∈ S,
      Real.exp (-(((-Real.log (i : ℝ))-(-Real.log (j : ℝ)))^2/(4*b)))) ≤ L := by
    intro i hi
    apply separated_row_bound S (fun n ↦ -Real.log (n : ℝ)) i b δ hb hδ
    intro j hj
    have hiI := mem_Ico.mp (hS hi)
    have hjI := mem_Ico.mp (hS hj)
    have hg := integer_log_gap (2*N) i j (by omega) (by omega) (by omega) (by omega)
    simpa only [δ,Nat.cast_mul,Nat.cast_ofNat,neg_sub_neg,abs_sub_comm,div_eq_mul_inv,mul_comm]
      using hg
  have hRaw := gaussian_mean_square_le S (fun n ↦ a n/(n : ℂ))
    (fun n ↦ -Real.log (n : ℝ)) b L hb hrow
  have hCoeff := DirichletPolynomialMeanValue.unit_coefficient_square_budget N hN S hS a ha
  have hProduct : Real.sqrt (Real.pi/b)*Real.sqrt (Real.pi/(δ^2/(4*b))) =
      4*Real.pi*(N : ℝ) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi/b)]
    have he : (Real.pi/b)*(Real.pi/(δ^2/(4*b)))=(4*Real.pi*(N : ℝ))^2 := by
      dsimp only [δ]
      field_simp
      ring
    rw [he,Real.sqrt_sq (by positivity)]
  calc
    _ ≤ Real.sqrt (Real.pi/b)*L*∑ n ∈ S, ‖a n/(n : ℂ)‖^2 := hRaw
    _ ≤ Real.sqrt (Real.pi/b)*L*(1/(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hCoeff (by dsimp only [L]; positivity)
    _ = _ := by
      dsimp only [L,budget]
      rw [mul_add,mul_one,hProduct]
      field_simp

theorem tail_bound (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T)
    (E : Set ℝ) (hE : MeasurableSet E) (hAway : ∀ t ∈ E, T ≤ |t|) :
    (∫ t in E, Real.exp (-(2*b)*t^2)*‖DirichletPolynomialMeanValue.value S a t‖^2) ≤
      Real.exp (-b*T^2)*budget N b := by
  let F := DirichletPolynomialMeanValue.value S a
  have hI : Integrable (fun t ↦ Real.exp (-b*t^2)*‖F t‖^2) :=
    gaussian_integrable S (fun n ↦ a n/(n : ℂ)) (fun n ↦ -Real.log (n : ℝ)) b hb
  have hI2 : Integrable (fun t ↦ Real.exp (-(2*b)*t^2)*‖F t‖^2) :=
    gaussian_integrable S (fun n ↦ a n/(n : ℂ)) (fun n ↦ -Real.log (n : ℝ)) (2*b) (by positivity)
  have hPoint (t : ℝ) (ht : t ∈ E) :
      Real.exp (-(2*b)*t^2)*‖F t‖^2 ≤
        Real.exp (-b*T^2)*(Real.exp (-b*t^2)*‖F t‖^2) := by
    have hSq : T^2 ≤ t^2 := by nlinarith [hAway t ht,sq_abs t]
    have hExp : Real.exp (-(2*b)*t^2) ≤ Real.exp (-b*T^2)*Real.exp (-b*t^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hSq,hb]
    exact (mul_le_mul_of_nonneg_right hExp (sq_nonneg _)).trans_eq (by ring)
  have hLocal : (∫ t in E, Real.exp (-(2*b)*t^2)*‖F t‖^2) ≤
      ∫ t in E, Real.exp (-b*T^2)*(Real.exp (-b*t^2)*‖F t‖^2) := by
    apply integral_mono_ae hI2.integrableOn (hI.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem hE] with t ht
    exact hPoint t ht
  rw [integral_const_mul] at hLocal
  have hWhole : (∫ t in E, Real.exp (-b*t^2)*‖F t‖^2) ≤
      ∫ t : ℝ, Real.exp (-b*t^2)*‖F t‖^2 :=
    setIntegral_le_integral hI (Filter.Eventually.of_forall (fun t ↦ by positivity))
  calc
    _ ≤ Real.exp (-b*T^2)*(∫ t in E, Real.exp (-b*t^2)*‖F t‖^2) := hLocal
    _ ≤ Real.exp (-b*T^2)*(∫ t : ℝ, Real.exp (-b*t^2)*‖F t‖^2) :=
      mul_le_mul_of_nonneg_left hWhole (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_bound N hN S hS a ha b hb) (Real.exp_pos _).le

end PaperP1.GaussianDirichletTail
