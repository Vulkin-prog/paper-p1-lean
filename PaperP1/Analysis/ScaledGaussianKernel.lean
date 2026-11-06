module

public import PaperP1.Analysis.GaussianOverlap


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ScaledGaussianKernel
open PaperP1 GaussianOverlap GaussianLaplaceKernel
open scoped Classical

theorem prefactor_scale (δ : ℝ) (hδ : 0 < δ) : prefactor (δ^2)=prefactor 1/δ := by
  unfold prefactor
  rw [Real.sqrt_div Real.pi_pos.le,Real.sqrt_sq hδ.le]
  norm_num only [div_one]
  ring

theorem heat_scaled (δ v : ℝ) (hδ : 0 < δ) :
    heat (δ^2) v=(prefactor 1/δ)*Real.exp (-v^2/(4*δ^2)) := by
  simp only [heat,prefactor_scale δ hδ,gaussian,sub_zero]

theorem heat_even (b v : ℝ) : heat b (-v)=heat b v := by
  simp only [heat,gaussian,sub_zero,neg_sq]

theorem heat_upper (δ v : ℝ) (hδ : 0 < δ) : heat (δ^2) v ≤ prefactor 1/δ := by
  rw [heat_scaled δ v hδ]
  have hExp : Real.exp (-v^2/(4*δ^2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) (by positivity))
  have hh := mul_le_mul_of_nonneg_left hExp (by positivity [prefactor_pos 1 (by norm_num)] : 0 ≤ prefactor 1/δ)
  simpa only [mul_one] using hh

theorem heat_lower (δ v : ℝ) (hδ : 0 < δ) (hv : |v| ≤ δ) :
    prefactor 1*Real.exp (-1)/δ ≤ heat (δ^2) v := by
  have hSq : v^2 ≤ δ^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg v) hv 2
  have hExp : -1 ≤ -v^2/(4*δ^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*δ^2)).mpr
    nlinarith only [hSq,sq_nonneg δ]
  calc
    _ = (prefactor 1/δ)*Real.exp (-1) := by ring
    _ ≤ (prefactor 1/δ)*Real.exp (-v^2/(4*δ^2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp)
        (by positivity [prefactor_pos 1 (by norm_num)])
    _ = _ := (heat_scaled δ v hδ).symm

theorem heat_tail (δ m v : ℝ) (hδ : 0 < δ) (hm : 0 ≤ m) (hv : m ≤ |v|) :
    heat (δ^2) v ≤ Real.exp (-m^2/(8*δ^2))*(prefactor 1/δ)*
      Real.exp (-v^2/(8*δ^2)) := by
  have hSq : m^2 ≤ v^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hm hv 2
  have hExp : Real.exp (-v^2/(4*δ^2)) ≤
      Real.exp (-m^2/(8*δ^2))*Real.exp (-v^2/(8*δ^2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right hSq (by positivity : 0 ≤ 8*δ^2)
    calc
      _ = -(v^2/(8*δ^2)) + -(v^2/(8*δ^2)) := by ring
      _ ≤ -(m^2/(8*δ^2)) + -(v^2/(8*δ^2)) := add_le_add (neg_le_neg hh) le_rfl
      _ = _ := by ring
  rw [heat_scaled δ v hδ]
  have hh := mul_le_mul_of_nonneg_left hExp (by positivity [prefactor_pos 1 (by norm_num)] : 0 ≤ prefactor 1/δ)
  nlinarith only [hh]

end PaperP1.ScaledGaussianKernel
