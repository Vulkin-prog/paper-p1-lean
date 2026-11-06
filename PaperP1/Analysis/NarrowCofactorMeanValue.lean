module

public import PaperP1.Analysis.SupportedCoefficientSquareBudget
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.NarrowCofactorRegime
public import PaperP1.Analysis.NarrowCofactorSparseMean

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowCofactorMeanValue
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem quantitative_bound (X H j : ℕ) (hX : 0 < X) (P Q : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ NarrowRamareRectangle.cofactorSet X H j, ‖f n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
      (NarrowRamareRectangle.coefficient P Q f) t‖^2) ≤
        SupportedCoefficientSquareBudget.constant*(T*NarrowPrimeBands.anchor H j/(X : ℝ)+1) := by
  let L := ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊
  have hLp : (0 : ℝ) < L := by
    have hh := (NarrowRamareRectangle.cofactor_endpoints X H j hX).1
    exact_mod_cast (show 0 < L by change 1 ≤ L at hh; omega)
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hu := NarrowPrimeBands.anchor_pos H j
  have hprod : (X : ℝ) ≤ (L : ℝ)*NarrowPrimeBands.anchor H j :=
    (div_le_iff₀ hu).mp (Nat.le_ceil ((X : ℝ)/NarrowPrimeBands.anchor H j))
  have hrec : 1/(L : ℝ) ≤ NarrowPrimeBands.anchor H j/(X : ℝ) :=
    (div_le_div_iff₀ hLp hXp).mpr (by nlinarith only [hprod])
  have hratio : T/(L : ℝ) ≤ T*NarrowPrimeBands.anchor H j/(X : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hrec hT.le
    convert hh using 1 <;> ring
  have hm := DirichletPolynomialMeanValue.bounded_dyadic_mean_square L (by exact_mod_cast hLp)
    (NarrowRamareRectangle.cofactorSet X H j) (NarrowCofactorRegime.cofactor_subset_dyadic X H j hX)
    (NarrowRamareRectangle.coefficient P Q f)
    (fun n hn ↦ NarrowCofactorSparseMean.coefficient_norm_bound P Q f n (hf n hn)) T hT
  have hx : 0 ≤ T*NarrowPrimeBands.anchor H j/(X : ℝ) := by positivity
  have hs : Real.sqrt Real.pi*(T/(L : ℝ))+4*Real.pi ≤
      (Real.sqrt Real.pi+4*Real.pi)*(T*NarrowPrimeBands.anchor H j/(X : ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left hratio (Real.sqrt_nonneg Real.pi)
    nlinarith only [hh,Real.sqrt_nonneg Real.pi,mul_nonneg Real.pi_pos.le hx]
  have hh := hm.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le)
  simpa only [SupportedCoefficientSquareBudget.constant,mul_assoc] using hh

theorem short_height_bound (X H j : ℕ) (hX : 0 < X) (P Q : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ NarrowRamareRectangle.cofactorSet X H j, ‖f n‖ ≤ 1)
    (T h : ℝ) (hT : 0 < T) (hh : 0 < h) (hTh : T ≤ (X : ℝ)/h)
    (hanchor : NarrowPrimeBands.anchor H j ≤ h) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
      (NarrowRamareRectangle.coefficient P Q f) t‖^2) ≤ 2*SupportedCoefficientSquareBudget.constant := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hprod : T*NarrowPrimeBands.anchor H j ≤ (X : ℝ) :=
    (mul_le_mul_of_nonneg_left hanchor hT.le).trans ((le_div_iff₀ hh).mp hTh)
  have hr : T*NarrowPrimeBands.anchor H j/(X : ℝ) ≤ 1 := (div_le_one hXp).mpr hprod
  have hs := mul_le_mul_of_nonneg_left (add_le_add hr (le_refl (1 : ℝ))) SupportedCoefficientSquareBudget.constant_pos.le
  have hb := quantitative_bound X H j hX P Q f hf T hT
  exact hb.trans (by nlinarith only [hs])
end PaperP1.NarrowCofactorMeanValue
