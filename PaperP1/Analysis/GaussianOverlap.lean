module

public import PaperP1.Analysis.GaussianLaplaceKernel


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianOverlap
open MeasureTheory PaperP1 GaussianLaplaceKernel
open scoped Classical

def heat (b v : ℝ) : ℝ := prefactor b*gaussian b 0 v

theorem heat_nonneg (b v : ℝ) (hb : 0 < b) : 0 ≤ heat b v := by
  exact mul_nonneg (prefactor_pos b hb).le (Real.exp_pos _).le

theorem heat_integrable (b u : ℝ) (hb : 0 < b) : Integrable (fun x ↦ heat b (x-u)) := by
  simpa only [heat,gaussian,sub_zero] using (gaussian_integrable b u hb).const_mul (prefactor b)

theorem heat_mass (b u : ℝ) (hb : 0 < b) : (∫ x : ℝ, heat b (x-u))=1 := by
  simp only [heat,gaussian,sub_zero]
  rw [integral_const_mul]
  exact gaussian_normalized b u hb

theorem prefactor_square (b : ℝ) (hb : 0 < b) : (prefactor b)^2=1/(4*Real.pi*b) := by
  unfold prefactor
  rw [div_pow,Real.sq_sqrt (by positivity : 0 ≤ Real.pi/b)]
  field_simp
  ring

theorem prefactor_product (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    prefactor b*prefactor c = prefactor (b+c)*prefactor (b*c/(b+c)) := by
  apply (sq_eq_sq₀ (by positivity [prefactor_pos b hb,prefactor_pos c hc])
    (by positivity [prefactor_pos (b+c) (by positivity),
      prefactor_pos (b*c/(b+c)) (by positivity)])).mp
  rw [mul_pow,mul_pow,prefactor_square b hb,prefactor_square c hc,
    prefactor_square (b+c) (by positivity),prefactor_square (b*c/(b+c)) (by positivity)]
  field_simp

theorem product_identity (b c u v x : ℝ) (hb : 0 < b) (hc : 0 < c) :
    heat b (x-u)*heat c (x-v) =
      heat (b+c) (u-v)*heat (b*c/(b+c)) (x-(c*u+b*v)/(b+c)) := by
  have hExp : -(x-u)^2/(4*b)-(x-v)^2/(4*c) =
      -(u-v)^2/(4*(b+c))-(x-(c*u+b*v)/(b+c))^2/(4*(b*c/(b+c))) := by
    field_simp
    ring
  simp only [heat,gaussian,sub_zero]
  calc
    _ = (prefactor b*prefactor c)*Real.exp (-(x-u)^2/(4*b)-(x-v)^2/(4*c)) := by
      rw [show -(x-u)^2/(4*b)-(x-v)^2/(4*c) =
        -(x-u)^2/(4*b)+(-(x-v)^2/(4*c)) by ring,Real.exp_add]
      ring
    _ = (prefactor (b+c)*prefactor (b*c/(b+c)))*
        Real.exp (-(u-v)^2/(4*(b+c))-(x-(c*u+b*v)/(b+c))^2/(4*(b*c/(b+c)))) := by
      rw [prefactor_product b c hb hc,hExp]
    _ = _ := by
      rw [show -(u-v)^2/(4*(b+c))-(x-(c*u+b*v)/(b+c))^2/(4*(b*c/(b+c))) =
        -(u-v)^2/(4*(b+c))+(-(x-(c*u+b*v)/(b+c))^2/(4*(b*c/(b+c)))) by ring,
        Real.exp_add]
      ring

theorem product_integrable (b c u v : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Integrable (fun x ↦ heat b (x-u)*heat c (x-v)) := by
  simp_rw [product_identity b c u v _ hb hc]
  exact (heat_integrable (b*c/(b+c)) ((c*u+b*v)/(b+c)) (by positivity)).const_mul _

theorem overlap (b c u v : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (∫ x : ℝ, heat b (x-u)*heat c (x-v))=heat (b+c) (u-v) := by
  simp_rw [product_identity b c u v _ hb hc]
  rw [integral_const_mul,heat_mass _ _ (by positivity),mul_one]

end PaperP1.GaussianOverlap
