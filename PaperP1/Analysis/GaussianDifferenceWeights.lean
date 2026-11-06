module

public import PaperP1.Analysis.DirichletPolynomialMeanValue


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianDifferenceWeights
open Finset MeasureTheory PaperP1 GaussianExponentialSums
open scoped Classical

def weight (b c t : ℝ) : ℝ := (Real.exp (-b*t^2)-Real.exp (-c*t^2))^2

theorem weight_nonneg (b c t : ℝ) : 0 ≤ weight b c t := sq_nonneg _

theorem weight_continuous (b c : ℝ) : Continuous (weight b c) := by unfold weight; fun_prop

theorem weight_le_one (b c t : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) : weight b c t ≤ 1 := by
  have hB : Real.exp (-b*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hC : Real.exp (-c*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  unfold weight
  nlinarith [Real.exp_pos (-b*t^2),Real.exp_pos (-c*t^2)]

theorem weight_gaussian (b c t : ℝ) (hbc : b ≤ c) : weight b c t ≤ Real.exp (-(2*b)*t^2) := by
  have hBC : Real.exp (-c*t^2) ≤ Real.exp (-b*t^2) := Real.exp_le_exp.mpr (by
    nlinarith [sq_nonneg t])
  have hSquare : (Real.exp (-b*t^2))^2=Real.exp (-(2*b)*t^2) := by
    rw [sq,← Real.exp_add]
    congr 1
    ring
  unfold weight
  rw [← hSquare]
  nlinarith [Real.exp_pos (-b*t^2),Real.exp_pos (-c*t^2)]

theorem weight_central (b c R t : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (_hR : 0 ≤ R)
    (ht : |t| ≤ R) : weight b c t ≤ (b+c)^2*R^4 := by
  have hB : Real.exp (-b*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hC : Real.exp (-c*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hBLo := Real.add_one_le_exp (-b*t^2)
  have hCLo := Real.add_one_le_exp (-c*t^2)
  have hBt : 0 ≤ b*t^2 := mul_nonneg hb (sq_nonneg t)
  have hCt : 0 ≤ c*t^2 := mul_nonneg hc (sq_nonneg t)
  have hAbs : |Real.exp (-b*t^2)-Real.exp (-c*t^2)| ≤ (b+c)*t^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hB,hC,hBLo,hCLo,hBt,hCt]
  have hSq : t^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hAbsR := hAbs.trans (mul_le_mul_of_nonneg_left hSq (add_nonneg hb hc))
  have hSquared := pow_le_pow_left₀ (abs_nonneg _) hAbsR 2
  rw [sq_abs] at hSquared
  unfold weight
  nlinarith only [hSquared]

theorem weighted_integrable (S : Finset ℕ) (a : ℕ → ℂ) (b c : ℝ)
    (hb : 0 < b) (hbc : b ≤ c) :
    Integrable (fun t ↦ weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2) := by
  have hI := gaussian_integrable S (fun n ↦ a n/(n : ℂ))
    (fun n ↦ -Real.log (n : ℝ)) (2*b) (by positivity)
  have hCont : Continuous (fun t ↦ weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2) :=
    (weight_continuous b c).mul ((polynomial_continuous _ _ _).norm.pow 2)
  apply hI.mono' hCont.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg b c t) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (weight_gaussian b c t hbc) (sq_nonneg _)

theorem value_unit (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖DirichletPolynomialMeanValue.value S a t‖ ≤ 1 := by
  have hNP : 0 < (N : ℝ) := by exact_mod_cast hN
  have hCard : S.card ≤ N := by
    have hh := card_le_card hS
    rw [Nat.card_Ico] at hh
    omega
  calc
    _ ≤ ∑ n ∈ S, ‖a n/(n : ℂ)‖ := polynomial_norm_bound _ _ _ _
    _ ≤ ∑ _n ∈ S, (1/(N : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hnN := (mem_Ico.mp (hS hn)).1
      rw [norm_div,Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (ha n hn) (Nat.cast_nonneg n)).trans
        (div_le_div_of_nonneg_left zero_le_one hNP (by exact_mod_cast hnN))
    _ = (S.card : ℝ)/(N : ℝ) := by rw [sum_const,nsmul_eq_mul]; ring
    _ ≤ 1 := (div_le_one hNP).mpr (by exact_mod_cast hCard)

theorem central_integral (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (b c R : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hR : 0 ≤ R) :
    (∫ t in Set.Ioc (-R) R, weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2) ≤
      2*(b+c)^2*R^5 := by
  have hCont : Continuous (fun t ↦ weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2) :=
    (weight_continuous b c).mul ((polynomial_continuous _ _ _).norm.pow 2)
  have hI : IntegrableOn (fun t ↦ weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2)
      (Set.Icc (-R) R) volume := hCont.integrableOn_Icc
  have hConst : IntegrableOn (fun _t : ℝ ↦ (b+c)^2*R^4) (Set.Ioc (-R) R) := by
    have hh : IntegrableOn (fun _t : ℝ ↦ (b+c)^2*R^4) (Set.Icc (-R) R) volume :=
      continuous_const.integrableOn_Icc
    exact hh.mono_set Set.Ioc_subset_Icc_self
  have hBound : (∫ t in Set.Ioc (-R) R,
      weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2) ≤
      ∫ _t in Set.Ioc (-R) R, (b+c)^2*R^4 := by
    apply integral_mono_ae (hI.mono_set Set.Ioc_subset_Icc_self) hConst
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hAbs : |t| ≤ R := abs_le.mpr ⟨(Set.mem_Ioc.mp ht).1.le,(Set.mem_Ioc.mp ht).2⟩
    have hv := value_unit N hN S hS a ha t
    have hv2 : ‖DirichletPolynomialMeanValue.value S a t‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (DirichletPolynomialMeanValue.value S a t)]
    exact (mul_le_mul_of_nonneg_left hv2 (weight_nonneg b c t)).trans
      (by simpa only [mul_one] using weight_central b c R t hb hc hR hAbs)
  have hEval : (∫ _t in Set.Ioc (-R) R, (b+c)^2*R^4)=2*(b+c)^2*R^5 := by
    rw [setIntegral_const]
    simp only [Real.volume_real_Ioc,smul_eq_mul]
    rw [max_eq_left (by linarith only [hR] : 0 ≤ R-(-R))]
    ring
  exact hBound.trans_eq hEval

end PaperP1.GaussianDifferenceWeights
