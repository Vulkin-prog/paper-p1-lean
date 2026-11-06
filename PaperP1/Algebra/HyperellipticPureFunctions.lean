module

public import PaperP1.Algebra.HyperellipticMonomialIndex
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Actual pure quadratic polynomial functions admit a separating leading coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticPureFunctions

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree HyperellipticWeightedMonomials
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

def Pure (f : F[X]) (z : CurveRing f) : Prop := z.re = 0 ∨ z.im = 0

def realCoefficient (f : F[X]) (n : ℕ) : CurveRing f →ₗ[F] F where
  toFun z := z.re.coeff n
  map_add' z w := by simp
  map_smul' c z := by simp

def imaginaryCoefficient (f : F[X]) (n : ℕ) : CurveRing f →ₗ[F] F where
  toFun z := z.im.coeff n
  map_add' z w := by simp
  map_smul' c z := by simp

theorem pure_one (f : F[X]) : Pure f 1 := Or.inr rfl

theorem pure_mul (f : F[X]) (z w : CurveRing f) (hz : Pure f z) (hw : Pure f w) : Pure f (z * w) := by
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · right
    simp only [QuadraticAlgebra.im_mul, hz, hw, zero_mul, mul_zero, add_zero]
  · left
    simp only [QuadraticAlgebra.re_mul, hz, hw, zero_mul, mul_zero, zero_add]
  · left
    simp only [QuadraticAlgebra.re_mul, hz, hw, zero_mul, mul_zero, zero_add]
  · right
    simp only [QuadraticAlgebra.im_mul, hz, hw, zero_mul, mul_zero, add_zero]

theorem pure_pow (f : F[X]) (z : CurveRing f) (hz : Pure f z) (n : ℕ) : Pure f (z ^ n) := by
  induction n with
  | zero => exact pure_one f
  | succ n ih => rw [pow_succ]; exact pure_mul f _ _ ih hz

theorem vector_pure (f : F[X]) (i : ℕ ⊕ ℕ) : Pure f (vector f i) := by
  rcases i with i | i
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem real_degree (f : F[X]) (z : CurveRing f) (him : z.im = 0) :
    poleDegree f z = 2 * z.re.natDegree := by
  rw [poleDegree, norm_formula, him, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, natDegree_pow]

theorem imaginary_degree (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f)
    (hre : z.re = 0) (him : z.im ≠ 0) : poleDegree f z = f.natDegree + 2 * z.im.natDegree := by
  rw [poleDegree, norm_formula, hre, zero_pow (by decide : 2 ≠ 0), zero_sub, natDegree_neg,
    natDegree_mul (PaperP1.HyperellipticOddDegreeNorm.polynomial_ne_zero f hodd) (pow_ne_zero 2 him), natDegree_pow]

theorem lower_real_coefficient (f : F[X]) (z w : CurveRing f) (hz : z.im = 0) (hw : Pure f w)
    (hlt : poleDegree f w < poleDegree f z) : w.re.coeff z.re.natDegree = 0 := by
  rcases hw with hw | hw
  · rw [hw, coeff_zero]
  · rw [real_degree f w hw, real_degree f z hz] at hlt
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem lower_imaginary_coefficient (f : F[X]) (hodd : Odd f.natDegree) (z w : CurveRing f)
    (hz : z.re = 0) (hzn : z ≠ 0) (hw : Pure f w)
    (hlt : poleDegree f w < poleDegree f z) : w.im.coeff z.im.natDegree = 0 := by
  have hzIm : z.im ≠ 0 := fun h ↦ hzn ((zero_iff f z).mpr ⟨hz, h⟩)
  rcases hw with hw | hw
  · by_cases hwi : w.im = 0
    · rw [hwi, coeff_zero]
    · rw [imaginary_degree f hodd w hw hwi, imaginary_degree f hodd z hz hzIm] at hlt
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [hw, coeff_zero]

theorem leading_functional (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f)
    (hz : z ≠ 0) (hpure : Pure f z) :
    ∃ ℓ : CurveRing f →ₗ[F] F, ℓ z ≠ 0 ∧
      ∀ w : CurveRing f, Pure f w → poleDegree f w < poleDegree f z → ℓ w = 0 := by
  rcases hpure with hre | him
  · have hIm : z.im ≠ 0 := fun h ↦ hz ((zero_iff f z).mpr ⟨hre, h⟩)
    refine ⟨imaginaryCoefficient f z.im.natDegree, ?_, ?_⟩
    · change z.im.coeff z.im.natDegree ≠ 0
      rw [coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hIm
    · intro w hw hlt
      exact lower_imaginary_coefficient f hodd z w hre hz hw hlt
  · have hRe : z.re ≠ 0 := fun h ↦ hz ((zero_iff f z).mpr ⟨h, him⟩)
    refine ⟨realCoefficient f z.re.natDegree, ?_, ?_⟩
    · change z.re.coeff z.re.natDegree ≠ 0
      rw [coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hRe
    · intro w hw hlt
      exact lower_real_coefficient f z w him hw hlt


end PaperP1.HyperellipticPureFunctions
