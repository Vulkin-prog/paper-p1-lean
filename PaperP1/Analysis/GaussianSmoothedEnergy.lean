module

public import PaperP1.Analysis.GaussianExponentialSums
public import PaperP1.Analysis.GaussianOverlap


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianSmoothedEnergy
open Finset MeasureTheory PaperP1 GaussianOverlap GaussianExponentialSums
open scoped Classical

def smoothed {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b x : ℝ) : ℝ :=
  ∑ i ∈ S, a i*heat b (x-w i)

theorem cross_expansion {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b c x : ℝ) :
    smoothed S a w b x*smoothed S a w c x =
      ∑ i ∈ S, ∑ j ∈ S, (a i*a j)*(heat b (x-w i)*heat c (x-w j)) := by
  unfold smoothed
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

theorem cross_integrable {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) :
    Integrable (fun x ↦ smoothed S a w b x*smoothed S a w c x) := by
  simp_rw [cross_expansion]
  exact integrable_finsetSum S (fun i hi ↦ integrable_finsetSum S (fun j hj ↦
    (product_integrable b c (w i) (w j) hb hc).const_mul (a i*a j)))

theorem cross_integral {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) :
    (∫ x : ℝ, smoothed S a w b x*smoothed S a w c x) =
      ∑ i ∈ S, ∑ j ∈ S, (a i*a j)*heat (b+c) (w i-w j) := by
  simp_rw [cross_expansion]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j hj
      rw [integral_const_mul,overlap b c (w i) (w j) hb hc]
    · intro j hj
      exact (product_integrable b c (w i) (w j) hb hc).const_mul (a i*a j)
  · intro i hi
    exact integrable_finsetSum S (fun j hj ↦
      (product_integrable b c (w i) (w j) hb hc).const_mul (a i*a j))

theorem heat_complex (b v : ℝ) :
    (heat b v : ℂ) = ((Real.sqrt (Real.pi/b)/(2*Real.pi) : ℝ) : ℂ)*
      Complex.exp (-((v^2/(4*b) : ℝ) : ℂ)) := by
  unfold heat GaussianLaplaceKernel.prefactor GaussianLaplaceKernel.gaussian
  rw [sub_zero,Complex.ofReal_mul,show -v^2/(4*b)=-(v^2/(4*b)) by ring,
    Complex.ofReal_exp,Complex.ofReal_neg]

theorem cross_parseval {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) :
    (∫ x : ℝ, smoothed S a w b x*smoothed S a w c x) =
      (∫ t : ℝ, Real.exp (-(b+c)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)/(2*Real.pi) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div,gaussian_gram S (fun i ↦ (a i : ℂ)) w (b+c) (by positivity),
    cross_integral S a w b c hb hc]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,heat_complex]
  rw [mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro j hj
  rw [Complex.ofReal_div]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hStar : star (a j : ℂ)=(a j : ℂ) := by
    exact Complex.conj_ofReal (a j)
  rw [hStar]
  ring

theorem difference_integrable {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) :
    Integrable (fun x ↦ (smoothed S a w b x-smoothed S a w c x)^2) := by
  have hI := ((cross_integrable S a w b b hb hb).sub
    ((cross_integrable S a w b c hb hc).const_mul 2)).add (cross_integrable S a w c c hc hc)
  exact hI.congr (Filter.Eventually.of_forall (fun x ↦ by
    dsimp only [Pi.add_apply,Pi.sub_apply]
    ring))

theorem difference_parseval {ι : Type*} (S : Finset ι) (a w : ι → ℝ) (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) :
    (∫ x : ℝ, (smoothed S a w b x-smoothed S a w c x)^2) =
      (∫ t : ℝ, (Real.exp (-b*t^2)-Real.exp (-c*t^2))^2*
        ‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)/(2*Real.pi) := by
  have hPhys : (∫ x : ℝ, (smoothed S a w b x-smoothed S a w c x)^2) =
      (∫ x : ℝ, smoothed S a w b x*smoothed S a w b x)-
      2*(∫ x : ℝ, smoothed S a w b x*smoothed S a w c x)+
      (∫ x : ℝ, smoothed S a w c x*smoothed S a w c x) := by
    simp_rw [show ∀ x, (smoothed S a w b x-smoothed S a w c x)^2 =
      smoothed S a w b x*smoothed S a w b x-2*(smoothed S a w b x*smoothed S a w c x)+
      smoothed S a w c x*smoothed S a w c x by intro x; ring]
    have hBC : Integrable (fun x ↦ 2*(smoothed S a w b x*smoothed S a w c x)) :=
      (cross_integrable S a w b c hb hc).const_mul 2
    have hSub : Integrable (fun x ↦ smoothed S a w b x*smoothed S a w b x-
        2*(smoothed S a w b x*smoothed S a w c x)) :=
      (cross_integrable S a w b b hb hb).sub hBC
    rw [integral_add hSub (cross_integrable S a w c c hc hc),
      integral_sub (cross_integrable S a w b b hb hb) hBC,integral_const_mul]
  have hFreq : (∫ t : ℝ, (Real.exp (-b*t^2)-Real.exp (-c*t^2))^2*
        ‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2) =
      (∫ t : ℝ, Real.exp (-(b+b)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)-
      2*(∫ t : ℝ, Real.exp (-(b+c)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)+
      (∫ t : ℝ, Real.exp (-(c+c)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2) := by
    have hPoint (t : ℝ) : (Real.exp (-b*t^2)-Real.exp (-c*t^2))^2*
        ‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2 =
      Real.exp (-(b+b)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2-
      2*(Real.exp (-(b+c)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)+
      Real.exp (-(c+c)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2 := by
      simp only [neg_add,add_mul,Real.exp_add]
      ring
    simp_rw [hPoint]
    have hBC : Integrable (fun t ↦ 2*(Real.exp (-(b+c)*t^2)*
        ‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)) :=
      (gaussian_integrable S (fun i ↦ (a i : ℂ)) w (b+c) (by positivity)).const_mul 2
    have hSub : Integrable (fun t ↦ Real.exp (-(b+b)*t^2)*
        ‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2-
        2*(Real.exp (-(b+c)*t^2)*‖polynomial S (fun i ↦ (a i : ℂ)) w t‖^2)) :=
      (gaussian_integrable S (fun i ↦ (a i : ℂ)) w (b+b) (by positivity)).sub hBC
    rw [integral_add hSub (gaussian_integrable S (fun i ↦ (a i : ℂ)) w (c+c) (by positivity)),
      integral_sub (gaussian_integrable S (fun i ↦ (a i : ℂ)) w (b+b) (by positivity)) hBC,
      integral_const_mul]
  rw [hPhys,hFreq,cross_parseval S a w b b hb hb,cross_parseval S a w b c hb hc,
    cross_parseval S a w c c hc hc]
  ring

end PaperP1.GaussianSmoothedEnergy
