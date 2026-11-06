module

public import PaperP1.Algebra.HyperellipticPolynomialAlgebra
public import Mathlib.RingTheory.Derivation.Basic

/-! # The actual tangent derivation on the quadratic polynomial algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticTangentDerivation

open Polynomial HyperellipticPolynomialAlgebra
open scoped QuadraticAlgebra

variable {F : Type*} [Field F]

def tangent (f : F[X]) : Derivation F (CurveRing f) (CurveRing f) where
  toLinearMap :=
    { toFun := fun z ↦ ⟨f.derivative * z.im + 2 * f * z.im.derivative, 2 * z.re.derivative⟩
      map_add' := by
        intro z w
        apply QuadraticAlgebra.ext <;> simp [Polynomial.derivative_add] <;> ring
      map_smul' := by
        intro c z
        apply QuadraticAlgebra.ext <;> simp [smul_eq_C_mul] <;> ring }
  map_one_eq_zero' := by apply QuadraticAlgebra.ext <;> simp
  leibniz' := by
    intro z w
    apply QuadraticAlgebra.ext <;> simp [smul_eq_mul, Polynomial.derivative_add, Polynomial.derivative_mul] <;> ring

@[simp]
theorem tangent_re (f : F[X]) (z : CurveRing f) :
    (tangent f z).re = f.derivative * z.im + 2 * f * z.im.derivative := rfl

@[simp]
theorem tangent_im (f : F[X]) (z : CurveRing f) : (tangent f z).im = 2 * z.re.derivative := rfl

theorem evaluation_tangent_base (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) (P : F[X]) :
    evaluation f x y hy (tangent f (algebraMap F[X] (CurveRing f) P)) =
      2 * y * P.derivative.eval x := by
  simp only [evaluation_apply, tangent_re, tangent_im, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, derivative_zero, mul_zero, add_zero, zero_add,
    eval_zero, eval_mul, eval_ofNat]
  ring

theorem tangent_root (f : F[X]) : tangent f QuadraticAlgebra.omega =
    algebraMap F[X] (CurveRing f) f.derivative := by
  apply QuadraticAlgebra.ext <;> simp [tangent]

end PaperP1.HyperellipticTangentDerivation
