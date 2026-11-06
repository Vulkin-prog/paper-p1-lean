module

public import PaperP1.Geometry.P3FactorMultiplicationMap
public import PaperP1.Algebra.P3FactorSegreDegreeZero
public import PaperP1.Geometry.IntegerProjectiveProper

/-! # The actual universal projective factor-multiplication image is closed over the integers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorMultiplicationProper

open AlgebraicGeometry CategoryTheory MvPolynomial P3HomogeneousCoefficientFamily
open P3FactorSegreGrading P3FactorMultiplicationMap

attribute [local instance] MvPolynomial.gradedAlgebra P3FactorSegreGrading.grading

theorem source_proper (e f : ℕ) : IsProper (IntegerProjectiveProper.structureMap (piece e f)) := by
  let : Module.Finite ℤ (piece e f 0) := P3FactorSegreDegreeZero.zero_module_finite e f
  let : Algebra.FiniteType (piece e f 0) (Quotient e f) := P3FactorSegreDegreeZero.over_zero_finite_type e f
  exact IntegerProjectiveProper.proper (piece e f)

theorem coefficient_zero_finite (d : ℕ) :
    Module.Finite ℤ (homogeneousSubmodule (Index d) ℤ 0) := by
  apply Module.Finite.of_surjective (Algebra.linearMap ℤ (homogeneousSubmodule (Index d) ℤ 0))
  intro x
  refine ⟨x.val.coeff 0, Subtype.ext ?_⟩
  change C (x.val.coeff 0) = x.val
  exact (HomogeneousPolynomialEvaluation.homogeneous_zero_eq_C x.val x.property).symm

theorem coefficient_proper (d : ℕ) :
    IsProper (IntegerProjectiveProper.structureMap (homogeneousSubmodule (Index d) ℤ)) := by
  let G := homogeneousSubmodule (Index d) ℤ
  let A := MvPolynomial (Index d) ℤ
  let : Module.Finite ℤ (G 0) := coefficient_zero_finite d
  let : IsScalarTower ℤ (G 0) A := by
    constructor
    intro n r x
    change (n • r.val) * x = n • (r.val * x)
    exact smul_mul_assoc n r.val x
  let : Algebra.FiniteType (G 0) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (G 0) A
  exact IntegerProjectiveProper.proper G

theorem multiplication_proper (e f : ℕ) : IsProper (multiplication e f) := by
  let g : coefficientScheme (e + f) ⟶ Spec (CommRingCat.of ℤ) :=
    IntegerProjectiveProper.structureMap (homogeneousSubmodule (Index (e + f)) ℤ)
  let h := IntegerProjectiveProper.structureMap (piece e f)
  let : IsProper g := coefficient_proper (e + f)
  let : IsSeparated g := (coefficient_proper (e + f)).toIsSeparated
  have he : multiplication e f ≫ g = h := specZIsTerminal.hom_ext _ _
  let : IsProper (multiplication e f ≫ g) := by
    rw [he]
    exact source_proper e f
  exact IsProper.of_comp (multiplication e f) g

theorem image_closed (e f : ℕ) : IsClosed (Set.range (multiplication e f)) := by
  let : IsProper (multiplication e f) := multiplication_proper e f
  exact (multiplication e f).isClosedMap.isClosed_range

end PaperP1.P3FactorMultiplicationProper
