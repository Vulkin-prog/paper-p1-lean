module

public import PaperP1.Algebra.P3FactorSegrePrimeLocus
public import PaperP1.Algebra.GradedPolynomialGenerators
public import Mathlib.RingTheory.FiniteType

/-! # The actual graded Segre coefficient quotient and multiplication map over the integers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorSegreGrading

open MvPolynomial P3HomogeneousCoefficientFamily P3CoefficientMultiplication P3FactorSegreRelations
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Quotient (e f : ℕ) := Ring e f ⧸ ideal e f

def piece (e f n : ℕ) : Submodule ℤ (Quotient e f) :=
  HomogeneousQuotientGrading.piece (homogeneousSubmodule (Coords e f) ℤ) (ideal e f) n

@[instance_reducible]
def grading (e f : ℕ) : GradedAlgebra (piece e f) :=
  HomogeneousQuotientGrading.grading (homogeneousSubmodule (Coords e f) ℤ) (ideal e f)
    (ideal_homogeneous e f)

attribute [local instance] grading

def coordinate (e f : ℕ) (ij : Coords e f) : Quotient e f :=
  Ideal.Quotient.mk (ideal e f) (X ij)

def coefficient (e f : ℕ) (m : Index (e + f)) : Quotient e f :=
  Ideal.Quotient.mk (ideal e f) (coefficientForm e f m)

theorem coordinate_mem (e f : ℕ) (ij : Coords e f) : coordinate e f ij ∈ piece e f 1 :=
  Submodule.mem_map.mpr ⟨X ij, isHomogeneous_X ℤ ij, rfl⟩

theorem coefficient_mem (e f : ℕ) (m : Index (e + f)) : coefficient e f m ∈ piece e f 1 :=
  Submodule.mem_map.mpr ⟨coefficientForm e f m, form_homogeneous e f m, rfl⟩

def gradedMap (e f : ℕ) : homogeneousSubmodule (Index (e + f)) ℤ →+*ᵍ piece e f :=
  GradedPolynomialGenerators.gradedEval (piece e f) (coefficient e f) (coefficient_mem e f)

theorem gradedMap_X (e f : ℕ) (m : Index (e + f)) : gradedMap e f (X m) = coefficient e f m :=
  GradedPolynomialGenerators.gradedEval_X _ _ _ m

theorem generators_adjoin (e f : ℕ) : Algebra.adjoin ℤ (Set.range (coordinate e f)) = ⊤ := by
  let q := Ideal.Quotient.mkₐ ℤ (ideal e f)
  have he : aeval (R := ℤ) (coordinate e f) = q := by
    apply MvPolynomial.algHom_ext
    intro ij
    exact aeval_X (coordinate e f) ij
  rw [← MvPolynomial.aeval_range, he]
  exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective ℤ (ideal e f))

theorem finite_type (e f : ℕ) : Algebra.FiniteType ℤ (Quotient e f) := inferInstance

def coefficientIdeal (e f : ℕ) : Ideal (Quotient e f) := Ideal.span (Set.range (coefficient e f))

theorem product_map_le (e f : ℕ) :
    (P3FactorSegrePrimeLocus.productIdeal e f).map (Ideal.Quotient.mk (ideal e f)) ≤ coefficientIdeal e f := by
  rw [P3FactorSegrePrimeLocus.productIdeal, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨P, ⟨m, rfl⟩, rfl⟩
  exact Ideal.subset_span ⟨m, rfl⟩

theorem coordinate_in_radical (e f : ℕ) (ij : Coords e f) :
    coordinate e f ij ∈ (coefficientIdeal e f).radical := by
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (ideal e f))
    (P3FactorSegrePrimeLocus.coordinate_mem_radical e f ij)
  have hh : coordinate e f ij ∈
      ((P3FactorSegrePrimeLocus.productIdeal e f).map (Ideal.Quotient.mk (ideal e f))).radical :=
    (Ideal.map_radical_le (Ideal.Quotient.mk (ideal e f))) hm
  exact Ideal.radical_mono (product_map_le e f) hh

theorem irrelevant_le_radical (e f : ℕ) :
    (HomogeneousIdeal.irrelevant (piece e f)).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (homogeneousSubmodule (Index (e + f)) ℤ)).toIdeal.map
        (gradedMap e f).toRingHom).radical := by
  have hcoefficient : coefficientIdeal e f ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Index (e + f)) ℤ)).toIdeal.map
        (gradedMap e f).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨m, rfl⟩
    have hx := HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousSubmodule (Index (e + f)) ℤ)
      (by decide : 0 < 1) (isHomogeneous_X ℤ m)
    have hh := Ideal.mem_map_of_mem (gradedMap e f).toRingHom hx
    change gradedMap e f (X m) ∈
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Index (e + f)) ℤ)).toIdeal.map
        (gradedMap e f).toRingHom at hh
    rw [gradedMap_X] at hh
    exact hh
  apply IrrelevantGenerated.irrelevant_le_radical (piece e f) (Set.range (coordinate e f))
    (by rintro _ ⟨ij, rfl⟩; exact coordinate_mem e f ij) (generators_adjoin e f)
  rintro _ ⟨ij, rfl⟩
  exact Ideal.radical_mono hcoefficient (coordinate_in_radical e f ij)

end PaperP1.P3FactorSegreGrading
