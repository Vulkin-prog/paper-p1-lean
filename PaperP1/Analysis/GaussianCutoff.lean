module

public import PaperP1.Analysis.GaussianLaplaceKernel

/-! # Actual Gaussian cutoff tails with separate finite-side normalization error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GaussianCutoff
open MeasureTheory PaperP1 GaussianLaplaceKernel
open scoped Classical

theorem prefactor_double_le (b : ℝ) (hb : 0 < b) : prefactor b ≤ 2*prefactor (2*b) := by
  have hs : Real.sqrt (Real.pi/b) ≤ 2*Real.sqrt (Real.pi/(2*b)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ Real.pi/b),mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ Real.pi/(2*b))]
    have he : (2 : ℝ)^2*(Real.pi/(2*b))=2*(Real.pi/b) := by ring
    rw [he]
    nlinarith [div_nonneg Real.pi_pos.le hb.le]
  calc
    _ ≤ (2*Real.sqrt (Real.pi/(2*b)))/(2*Real.pi) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = _ := by dsimp only [prefactor]; ring

theorem doubled_mass_bound (b c : ℝ) (hb : 0 < b) :
    prefactor b*(∫ u : ℝ, gaussian (2*b) c u) ≤ 2 := by
  calc
    _ ≤ (2*prefactor (2*b))*(∫ u : ℝ, gaussian (2*b) c u) :=
      mul_le_mul_of_nonneg_right (prefactor_double_le b hb)
        (integral_nonneg (fun u ↦ (Real.exp_pos _).le))
    _ = 2*(prefactor (2*b)*(∫ u : ℝ, gaussian (2*b) c u)) := by ring
    _ = _ := by rw [gaussian_normalized (2*b) c (by positivity)]; norm_num

theorem gaussian_tail_bound (b c d : ℝ) (hb : 0 < b) (hd : 0 ≤ d)
    (S : Set ℝ) (hS : MeasurableSet S) (hdist : ∀ u ∈ S, d ≤ |u-c|) :
    prefactor b*(∫ u in S, gaussian b c u) ≤ 2*Real.exp (-d^2/(8*b)) := by
  have hpoint (u : ℝ) (hu : u ∈ S) : gaussian b c u ≤ Real.exp (-d^2/(8*b))*gaussian (2*b) c u := by
    have hh := pow_le_pow_left₀ hd (hdist u hu) 2
    rw [sq_abs] at hh
    have hdiv := div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 8*b)
    rw [gaussian,gaussian,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : -(u-c)^2/(4*b)=-(u-c)^2/(8*b)-(u-c)^2/(8*b) := by ring
    have he2 : -(u-c)^2/(4*(2*b))=-(u-c)^2/(8*b) := by ring
    rw [he,he2]
    simp only [neg_div]
    linarith
  have hm : (∫ u in S, gaussian b c u) ≤ ∫ u in S, Real.exp (-d^2/(8*b))*gaussian (2*b) c u := by
    apply integral_mono_ae (gaussian_integrable b c hb).integrableOn
      ((gaussian_integrable (2*b) c (by positivity)).const_mul _).integrableOn
    filter_upwards [ae_restrict_mem hS] with u hu
    exact hpoint u hu
  rw [integral_const_mul] at hm
  have hall := setIntegral_le_integral (gaussian_integrable (2*b) c (by positivity))
    (Filter.Eventually.of_forall (fun u ↦ (Real.exp_pos _).le)) (s := S)
  calc
    _ ≤ prefactor b*(Real.exp (-d^2/(8*b))*(∫ u in S, gaussian (2*b) c u)) :=
      mul_le_mul_of_nonneg_left hm (prefactor_pos b hb).le
    _ ≤ prefactor b*(Real.exp (-d^2/(8*b))*(∫ u : ℝ, gaussian (2*b) c u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hall (Real.exp_pos _).le) (prefactor_pos b hb).le
    _ = Real.exp (-d^2/(8*b))*(prefactor b*(∫ u : ℝ, gaussian (2*b) c u)) := by ring
    _ ≤ Real.exp (-d^2/(8*b))*2 := mul_le_mul_of_nonneg_left (doubled_mass_bound b c hb) (Real.exp_pos _).le
    _ = _ := by ring

theorem kernel_negative_tail (b v : ℝ) (hb : 0 < b) (hv : v ≤ 0) :
    kernel b v ≤ 2*Real.exp b*Real.exp (-v^2/(8*b)) := by
  have ht := gaussian_tail_bound b (v-2*b) (-v) hb (by linarith) (Set.Ioi 0) measurableSet_Ioi (by
    intro u hu
    have hh := le_abs_self (u-(v-2*b))
    linarith [show 0 < u from hu])
  rw [neg_sq] at ht
  rw [kernel_completed_square b v hb]
  have hh := mul_le_mul_of_nonneg_left ht (Real.exp_pos b).le
  nlinarith

theorem gaussian_complement_mass (b c : ℝ) (hb : 0 < b) :
    prefactor b*(∫ u in Set.Ioi 0, gaussian b c u)+prefactor b*(∫ u in Set.Iic 0, gaussian b c u)=1 := by
  have hh := integral_add_compl (s := Set.Ioi 0) measurableSet_Ioi (gaussian_integrable b c hb)
  rw [Set.compl_Ioi] at hh
  rw [← mul_add,hh,gaussian_normalized b c hb]

theorem kernel_positive_error (b v : ℝ) (hb : 0 < b) (hv : 2*b ≤ v) :
    |kernel b v-1| ≤ Real.exp b-1+2*Real.exp b*Real.exp (-(v-2*b)^2/(8*b)) := by
  let m := prefactor b*(∫ u in Set.Iic 0, gaussian b (v-2*b) u)
  have hm0 : 0 ≤ m := mul_nonneg (prefactor_pos b hb).le
    (integral_nonneg (fun u ↦ (Real.exp_pos _).le))
  have hm := gaussian_tail_bound b (v-2*b) (v-2*b) hb (by linarith) (Set.Iic 0) measurableSet_Iic (by
    intro u hu
    have hh := neg_le_abs (u-(v-2*b))
    linarith [show u ≤ 0 from hu])
  have hcomp := gaussian_complement_mass b (v-2*b) hb
  have hk : kernel b v-1=(Real.exp b-1)-Real.exp b*m := by
    rw [kernel_completed_square b v hb]
    dsimp only [m]
    have hmul := congrArg (fun r : ℝ ↦ Real.exp b*r) hcomp
    nlinarith only [hmul]
  have heb : 0 ≤ Real.exp b-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hb.le)
  rw [hk]
  calc
    _ ≤ |Real.exp b-1|+|Real.exp b*m| := abs_sub _ _
    _ = (Real.exp b-1)+Real.exp b*m := by rw [abs_of_nonneg heb,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hm0)]
    _ ≤ (Real.exp b-1)+Real.exp b*(2*Real.exp (-(v-2*b)^2/(8*b))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
    _ = _ := by ring

theorem positive_far_error (b v : ℝ) (hb : 0 < b) (hv : 4*b ≤ v) :
    |kernel b v-1| ≤ Real.exp b-1+2*Real.exp b*Real.exp (-v^2/(32*b)) := by
  have hh := kernel_positive_error b v hb (by linarith)
  have hs : (v/2)^2 ≤ (v-2*b)^2 := by nlinarith
  have hd := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 8*b)
  have he : (v/2)^2/(8*b)=v^2/(32*b) := by ring
  rw [he] at hd
  have hExp : Real.exp (-(v-2*b)^2/(8*b)) ≤ Real.exp (-v^2/(32*b)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hd
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hExp (by positivity)))

theorem exp_half_le_two (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) : Real.exp (b/2) ≤ 2 := by
  have hh := Real.abs_exp_sub_one_le (show |b/2| ≤ 1 by rw [abs_of_pos (by positivity : 0 < b/2)]; linarith)
  rw [abs_of_pos (by positivity : 0 < b/2)] at hh
  linarith [le_abs_self (Real.exp (b/2)-1)]

def step (v : ℝ) : ℝ := if 0 ≤ v then 1 else 0

theorem step_error (b v : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    |kernel b v-step v| ≤ (if 0 ≤ v then Real.exp b-1 else 0)+
      2*Real.exp b*Real.exp (-v^2/(32*b)) := by
  have hK0 := kernel_nonneg b v
  have hK1 := kernel_le_exp b v hb
  have heb : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb.le
  by_cases hv : 0 ≤ v
  · rw [step,ite_eq_left hv,ite_eq_left hv]
    by_cases hfar : 4*b ≤ v
    · exact positive_far_error b v hb hfar
    · have habs : |kernel b v-1| ≤ Real.exp b := abs_le.mpr ⟨by linarith,by linarith⟩
      have hd : v^2/(32*b) ≤ b/2 := by
        apply (div_le_iff₀ (by positivity : 0 < 32*b)).mpr
        nlinarith
      have he : Real.exp (-b/2) ≤ Real.exp (-v^2/(32*b)) := by
        apply Real.exp_le_exp.mpr
        simpa only [neg_div] using neg_le_neg hd
      have hexp := exp_half_le_two b hb hb1
      have hi : 1 ≤ 2*Real.exp (-b/2) := by
        rw [show -b/2=-(b/2) by ring,Real.exp_neg]
        change 1 ≤ 2/Real.exp (b/2)
        exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [one_mul] using hexp)
      have hlow : Real.exp b ≤ 2*Real.exp b*Real.exp (-v^2/(32*b)) := by
        have hh := mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left he (by norm_num))) (Real.exp_pos b).le
        nlinarith
      exact habs.trans (by linarith)
  · rw [step,ite_eq_right hv,ite_eq_right hv,sub_zero,abs_of_nonneg hK0,zero_add]
    have hh := kernel_negative_tail b v hb (not_le.mp hv).le
    have hd : v^2/(32*b) ≤ v^2/(8*b) :=
      div_le_div_of_nonneg_left (sq_nonneg v) (by positivity) (by linarith)
    have he : Real.exp (-v^2/(8*b)) ≤ Real.exp (-v^2/(32*b)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hd
    exact hh.trans (mul_le_mul_of_nonneg_left he (by positivity))
end PaperP1.GaussianCutoff

