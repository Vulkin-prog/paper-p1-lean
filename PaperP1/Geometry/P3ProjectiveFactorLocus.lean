module

public import PaperP1.Geometry.IntegerProjectiveEquationEvaluation
public import PaperP1.Geometry.P3FactorSegreFieldPoint

/-! # The finite closed union of actual positive-degree projective factor images -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3ProjectiveFactorLocus

open AlgebraicGeometry CategoryTheory MvPolynomial P3HomogeneousCoefficientFamily
open P3FactorMultiplicationMap
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Partition (d : ℕ) := {e : Fin (d + 1) // 0 < e.val ∧ e.val < d}

def degreeMap {n d : ℕ} (h : n = d) : coefficientScheme n ⟶ coefficientScheme d :=
  (eqToIso (congrArg coefficientScheme h)).hom

def degreeVector {F : Type} {n d : ℕ} (h : n = d) (a : Index n → F) : Index d → F := h ▸ a

theorem degreeVector_ne_zero {F : Type} [Zero F] {n d : ℕ}
    (h : n = d) (a : Index n → F) (ha : a ≠ 0) : degreeVector h a ≠ 0 := by
  subst d
  exact ha

theorem degreeMap_point {F : Type} [Field F] {n d : ℕ}
    (h : n = d) (a : Index n → F) (ha : a ≠ 0) :
    degreeMap h (IntegerCoefficientProjectivePoint.point a ha) =
      IntegerCoefficientProjectivePoint.point (degreeVector h a) (degreeVector_ne_zero h a ha) := by
  subst d
  rfl

theorem partition_degree (d : ℕ) (e : Partition d) : e.val.val + (d - e.val.val) = d := by
  have := e.property.2
  omega

def partitionMap (d : ℕ) (e : Partition d) :
    sourceScheme e.val.val (d - e.val.val) ⟶ coefficientScheme d :=
  multiplication e.val.val (d - e.val.val) ≫ degreeMap (partition_degree d e)

def locus (d : ℕ) : Set (coefficientScheme d) := ⋃ e : Partition d, Set.range (partitionMap d e)

theorem partition_proper (d : ℕ) (e : Partition d) : IsProper (partitionMap d e) := by
  let : IsProper (multiplication e.val.val (d - e.val.val)) :=
    P3FactorMultiplicationProper.multiplication_proper _ _
  unfold partitionMap degreeMap
  infer_instance

theorem locus_closed (d : ℕ) : IsClosed (locus d) := by
  apply isClosed_iUnion_of_finite
  intro e
  let : IsProper (partitionMap d e) := partition_proper d e
  exact (partitionMap d e).isClosedMap.isClosed_range

theorem product_point_mem_locus {F : Type} [Field F] (d : ℕ) (e : Partition d)
    (a : Index e.val.val → F) (b : Index (d - e.val.val) → F) (ha : a ≠ 0) (hb : b ≠ 0) :
    IntegerCoefficientProjectivePoint.point
      (degreeVector (partition_degree d e) (P3FactorSegreFieldPoint.productVector _ _ a b))
      (degreeVector_ne_zero _ _ (P3FactorSegreFieldPoint.productVector_ne_zero _ _ a b ha hb)) ∈
        locus d := by
  apply Set.mem_iUnion.mpr
  refine ⟨e, P3FactorSegreFieldPoint.point _ _ a b ha hb, ?_⟩
  change degreeMap (partition_degree d e)
    (multiplication _ _ (P3FactorSegreFieldPoint.point _ _ a b ha hb)) = _
  rw [P3FactorSegreFieldPoint.multiplication_point, degreeMap_point]

theorem finite_positive_equations (d : ℕ) :
    ∃ forms : Finset (MvPolynomial (Index d) ℤ),
      (∀ P ∈ forms, ∃ n : ℕ, 0 < n ∧ P.IsHomogeneous n) ∧
      (∀ (F : Type) [Field F] (a : Index d → F) (ha : a ≠ 0),
        IntegerCoefficientProjectivePoint.point a ha ∈ locus d ↔
          ∀ P ∈ forms, eval a (map (Int.castRingHom F) P) = 0) ∧
      ∀ (F : Type) [CommRing F], ∀ P ∈ forms,
        eval (0 : Index d → F) (map (Int.castRingHom F) P) = 0 :=
  IntegerProjectiveEquationEvaluation.closed_field_equations (locus d) (locus_closed d)

end PaperP1.P3ProjectiveFactorLocus
