module

public import PaperP1.Algebra.BiquadraticSourceNorm
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.RingTheory.Norm.Transitivity

/-! # The literal biquadratic expression is the actual algebra norm of a quadratic tower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticNormModel

open QuadraticAlgebra

abbrev First (R : Type*) [CommRing R] (f : R) := QuadraticAlgebra R f 0

abbrev Second (R : Type*) [CommRing R] (f g : R) :=
  QuadraticAlgebra (First R f) (algebraMap R (First R f) g) 0

def auxiliary {R : Type*} [CommRing R] (f g a b c d : R) : Second R f g := ⟨⟨a, b⟩, ⟨c, d⟩⟩

theorem quadratic_norm {R : Type*} [CommRing R] (a b : R) (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = z.norm := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap R (QuadraticAlgebra R a b) z).det = z.norm
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

theorem inner_norm {R : Type*} [CommRing R] (f g a b c d : R) :
    (auxiliary f g a b c d).norm =
      (⟨BiquadraticNorm.upper f g a b c d, 2 * BiquadraticNorm.mixed g a b c d⟩ : First R f) := by
  apply QuadraticAlgebra.ext <;> simp [auxiliary, QuadraticAlgebra.norm_def, BiquadraticNorm.upper, BiquadraticNorm.mixed] <;> ring

theorem norm_formula {R : Type*} [CommRing R] (f g a b c d : R) :
    Algebra.norm R (auxiliary f g a b c d) = BiquadraticNorm.norm f g a b c d := by
  rw [← Algebra.norm_norm (R := R) (S := First R f),
    quadratic_norm (algebraMap R (First R f) g) 0 (auxiliary f g a b c d), inner_norm, quadratic_norm]
  simp only [QuadraticAlgebra.norm_def, BiquadraticNorm.norm]
  ring

theorem source_norm_formula {K : Type*} [Field K] (f₁ f₂ f₃ h G a b c d : K)
    (hG : G ≠ 0) (h₃ : f₃ * G ^ 2 = f₁ * f₂) (hh : h * G = f₂) :
    Algebra.norm K (auxiliary f₁ f₂ a b c (d / G)) =
      BiquadraticSourceNorm.sourceNorm f₁ f₂ f₃ h a b c d := by
  rw [norm_formula]
  exact (BiquadraticSourceNorm.sourceNorm_normalized f₁ f₂ f₃ h G a b c d hG h₃ hh).symm

theorem nonsquare_condition {R : Type*} [CommRing R] (f : R) (hf : ¬ IsSquare f) :
    ∀ r : R, r ^ 2 ≠ f + 0 * r := by
  intro r hr
  apply hf
  refine ⟨r, ?_⟩
  simpa only [zero_mul, add_zero, pow_two] using hr.symm

theorem second_nonsquare {K : Type*} [Field K] [CharZero K] (f g : K)
    (hg : ¬ IsSquare g) (hfg : ¬ IsSquare (f * g)) :
    ¬ IsSquare (algebraMap K (First K f) g) := by
  rintro ⟨z, hz⟩
  have hr := congrArg QuadraticAlgebra.re hz.symm
  have hi := congrArg QuadraticAlgebra.im hz.symm
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, zero_mul, add_zero] at hr hi
  have ht : (2 : K) ≠ 0 := by norm_num
  have hp : z.re * z.im = 0 := by
    apply mul_left_cancel₀ ht
    linear_combination hi
  rcases mul_eq_zero.mp hp with ha | hb
  · apply hfg
    refine ⟨f * z.im, ?_⟩
    simp only [ha, zero_mul, zero_add] at hr
    rw [← hr]
    ring
  · apply hg
    refine ⟨z.re, ?_⟩
    simpa only [hb, mul_zero, add_zero] using hr.symm

theorem tower_isField {K : Type*} [Field K] [CharZero K] (f g : K)
    (hf : ¬ IsSquare f) (hg : ¬ IsSquare g) (hfg : ¬ IsSquare (f * g)) : IsField (Second K f g) := by
  let : Fact (∀ r : K, r ^ 2 ≠ f + 0 * r) := ⟨nonsquare_condition f hf⟩
  let : Fact (∀ r : First K f, r ^ 2 ≠ algebraMap K (First K f) g + 0 * r) :=
    ⟨nonsquare_condition _ (second_nonsquare f g hg hfg)⟩
  exact Field.toIsField (Second K f g)

theorem tower_finrank {K : Type*} [Field K] [CharZero K] (f g : K)
    (hf : ¬ IsSquare f) : Module.finrank K (Second K f g) = 4 := by
  let : Fact (∀ r : K, r ^ 2 ≠ f + 0 * r) := ⟨nonsquare_condition f hf⟩
  have h₁ := QuadraticAlgebra.finrank_eq_two (R := K) (a := f) (b := 0)
  have h₂ := QuadraticAlgebra.finrank_eq_two (R := First K f) (a := algebraMap K (First K f) g) (b := 0)
  have hm := Module.finrank_mul_finrank K (First K f) (Second K f g)
  rw [h₁, h₂] at hm
  exact hm.symm

end PaperP1.BiquadraticNormModel
