module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Exact coefficient projections for polynomial scalar descent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialScalarProjection

open Polynomial

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Module R A] [Module R B]

def project (ell : A →ₗ[R] B) (P : A[X]) : B[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (P.coeff.mapRange ell ell.map_zero))

theorem project_coefficient (ell : A →ₗ[R] B) (P : A[X]) (n : ℕ) :
    (project ell P).coeff n = ell (P.coeff n) := rfl

theorem project_add (ell : A →ₗ[R] B) (P Q : A[X]) :
    project ell (P + Q) = project ell P + project ell Q := by
  ext n
  simp only [project_coefficient, coeff_add, map_add]

theorem project_smul (ell : A →ₗ[R] B) (r : R) (P : A[X]) :
    project ell (r • P) = r • project ell P := by
  ext n
  simp only [project_coefficient, coeff_smul, map_smul]

theorem project_degree_le (ell : A →ₗ[R] B) (P : A[X]) :
    (project ell P).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [project_coefficient, coeff_eq_zero_of_natDegree_lt hn, map_zero]

def linearMap (ell : A →ₗ[R] B) : A[X] →ₗ[R] B[X] where
  toFun := project ell
  map_add' := project_add ell
  map_smul' := project_smul ell

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def component (ell : L →ₗ[K] K) : L[X][X] →ₗ[K] K[X][X] :=
  linearMap (linearMap ell)

def extend (P : K[X][X]) : L[X][X] :=
  P.map (Polynomial.mapRingHom (algebraMap K L))

theorem extend_coefficient (P : K[X][X]) (i j : ℕ) :
    (((extend P : L[X][X]).coeff i).coeff j) = algebraMap K L ((P.coeff i).coeff j) := by
  simp only [extend, Polynomial.coeff_map, Polynomial.coe_mapRingHom]

theorem component_coefficient (ell : L →ₗ[K] K) (P : L[X][X]) (i j : ℕ) :
    ((component ell P).coeff i).coeff j = ell ((P.coeff i).coeff j) := rfl

theorem component_constant_mul (ell : L →ₗ[K] K) (c : L) (P : K[X][X]) :
    component ell (C (C c) * extend P) = C (C (ell c)) * P := by
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  rw [component_coefficient, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul]
  rw [extend_coefficient]
  have h := ell.map_smul ((P.coeff i).coeff j) c
  simpa [Algebra.smul_def, mul_comm] using h

end PaperP1.PolynomialScalarProjection
