module

public import PaperP1.Algebra.LocalizedAffineQuadraticSource
public import PaperP1.Algebra.FullDegreePrimitiveAlgebra
public import PaperP1.Algebra.FractionFieldFromGenericGenerator
public import Mathlib.FieldTheory.SeparableClosure

/-! # A literal full-degree irreducible source relation gives the actual primitive fraction field

The source and its generic tower are the actual quadratic algebras over the
ordered power parameters. Domain, field and primitive-generation properties
are conclusions. Separability follows when the same polynomial is separable.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullDegreeAffineSourceField
open Polynomial PaperP1.LocalizedAffineQuadraticSource PaperP1.AffinePowerParameterFractionField
variable (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) (s : List (Base F))

theorem generic_isField (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) : IsField (Generic F s) := by
  let := genericAlgebra F D hD s
  let : Nontrivial (Generic F s) := generic_nontrivial F s
  let : Module.Finite (ParameterField F) (Generic F s) := generic_finite F D hD s
  exact PaperP1.FullDegreePrimitiveAlgebra.isField P hmonic hP (injection F s y) hy
    ((generic_dimension F D hD s).trans hd)

theorem primitive (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) :
    letI := genericAlgebra F D hD s
    Algebra.adjoin (ParameterField F) ({injection F s y} : Set (Generic F s)) = ⊤ := by
  let := genericAlgebra F D hD s
  let : Nontrivial (Generic F s) := generic_nontrivial F s
  let : Module.Finite (ParameterField F) (Generic F s) := generic_finite F D hD s
  exact PaperP1.FullDegreePrimitiveAlgebra.adjoin_eq_top P hmonic hP (injection F s y) hy
    ((generic_dimension F D hD s).trans hd)

theorem source_isDomain (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) : IsDomain (Source F s) := by
  let : IsDomain (Generic F s) := (generic_isField F D hD s P hmonic hP y hy hd).isDomain
  exact (injection_injective F s).isDomain (injection F s)

theorem fraction_ring (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) :
    letI := genericAlgebra F D hD s
    letI := (generic_isField F D hD s P hmonic hP y hy hd).toField
    letI := (injection F s).toAlgebra
    IsFractionRing (Source F s) (Generic F s) := by
  let := sourceAlgebra F D s
  let := genericAlgebra F D hD s
  let := (generic_isField F D hD s P hmonic hP y hy hd).toField
  exact PaperP1.FractionFieldFromGenericGenerator.isFractionRing
    (R := Parameters F) (K := ParameterField F) (injection F s) (injection_injective F s)
    (parameter_compatibility F D hD s) y (primitive F D hD s P hmonic hP y hy hd)

theorem dimension_eq (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) :
    letI := genericAlgebra F D hD s
    Module.finrank (ParameterField F) (Generic F s) = P.natDegree := by
  let := genericAlgebra F D hD s
  let : Nontrivial (Generic F s) := generic_nontrivial F s
  let : Module.Finite (ParameterField F) (Generic F s) := generic_finite F D hD s
  exact PaperP1.FullDegreePrimitiveAlgebra.finrank_eq P hmonic hP (injection F s y) hy
    ((generic_dimension F D hD s).trans hd)

theorem minimal_polynomial (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0) :
    letI := genericAlgebra F D hD s
    minpoly (ParameterField F) (injection F s y) = P := by
  let := genericAlgebra F D hD s
  let : Nontrivial (Generic F s) := generic_nontrivial F s
  exact (minpoly.eq_of_irreducible_of_monic hP hy hmonic).symm

theorem primitive_intermediate (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) :
    letI := genericAlgebra F D hD s
    letI := (generic_isField F D hD s P hmonic hP y hy hd).toField
    IntermediateField.adjoin (ParameterField F) ({injection F s y} : Set (Generic F s)) = ⊤ := by
  let := genericAlgebra F D hD s
  let := (generic_isField F D hD s P hmonic hP y hy hd).toField
  exact IntermediateField.adjoin_eq_top_of_algebra (ParameterField F) _
    (primitive F D hD s P hmonic hP y hy hd)

theorem separable (P : (ParameterField F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hsep : P.Separable) (y : Source F s)
    (hy : letI := genericAlgebra F D hD s; Polynomial.aeval (injection F s y) P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) :
    letI := genericAlgebra F D hD s
    letI := (generic_isField F D hD s P hmonic hP y hy hd).toField
    Algebra.IsSeparable (ParameterField F) (Generic F s) := by
  let := genericAlgebra F D hD s
  let := (generic_isField F D hD s P hmonic hP y hy hd).toField
  have htop := primitive_intermediate F D hD s P hmonic hP y hy hd
  rw [← IntermediateField.isSeparable_top, ← htop,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  intro z hz
  rw [Set.mem_singleton_iff.mp hz]
  change (minpoly (ParameterField F) (injection F s y)).Separable
  rw [minimal_polynomial F D hD s P hmonic hP y hy]
  exact hsep

end PaperP1.FullDegreeAffineSourceField
