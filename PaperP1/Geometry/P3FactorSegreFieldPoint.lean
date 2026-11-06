module

public import PaperP1.Geometry.IntegerCoefficientProjectivePoint
public import PaperP1.Geometry.P3FactorMultiplicationMap

/-! # Actual field-valued factor pairs give points in the universal projective factor image -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorSegreFieldPoint

open MvPolynomial P3HomogeneousCoefficientFamily P3CoefficientMultiplication
  P3FactorSegreRelations P3FactorSegreGrading
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra P3FactorSegreGrading.grading

variable {F : Type} [Field F] (e f : ℕ) (a : Index e → F) (b : Index f → F)

def tensorVector : Coords e f → F := fun ij ↦ a ij.1 * b ij.2

theorem tensor_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : tensorVector e f a b ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
  intro hz
  exact mul_ne_zero hi hj (congr_fun hz (i, j))

theorem relations_le_ray_kernel :
    P3FactorSegreRelations.ideal e f ≤
      RingHom.ker (IntegerCoefficientProjectivePoint.rayMap (tensorVector e f a b)) := by
  apply Ideal.span_le.mpr
  intro P hP
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hP
  change IntegerCoefficientProjectivePoint.rayMap (tensorVector e f a b) _ = 0
  rw [IntegerCoefficientProjectivePoint.ray_homogeneous_value _ _
    (relation_homogeneous e f t.1.1 t.1.2 t.2.1 t.2.2)]
  rw [show eval (tensorVector e f a b)
      (map (Int.castRingHom F) (relation e f t.1.1 t.1.2 t.2.1 t.2.2)) = 0 from
    pure_tensor_vanishes e f a b t.1.1 t.1.2 t.2.1 t.2.2, map_zero, zero_mul]

def quotientRay : Quotient e f →+* MvPolynomial Unit F :=
  Ideal.Quotient.lift (P3FactorSegreRelations.ideal e f)
    (IntegerCoefficientProjectivePoint.rayMap (tensorVector e f a b))
    (fun _ h ↦ relations_le_ray_kernel e f a b h)

theorem quotientRay_mk (P : Ring e f) :
    quotientRay e f a b (Ideal.Quotient.mk (P3FactorSegreRelations.ideal e f) P) =
      IntegerCoefficientProjectivePoint.rayMap (tensorVector e f a b) P := rfl

def quotientGradedMap : piece e f →+*ᵍ homogeneousSubmodule Unit F where
  __ := quotientRay e f a b
  map_mem h := by
    obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp h
    exact IntegerCoefficientProjectivePoint.ray_homogeneous _ P hP

def point (ha : a ≠ 0) (hb : b ≠ 0) : ProjectiveSpectrum (piece e f) where
  asHomogeneousIdeal := (⊥ : HomogeneousIdeal (homogeneousSubmodule Unit F)).comap
    (quotientGradedMap e f a b)
  isPrime := RingHom.ker_isPrime (quotientRay e f a b)
  not_irrelevant_le h := by
    obtain ⟨ij, hij⟩ := Function.ne_iff.mp (tensor_ne_zero e f a b ha hb)
    have hx := HomogeneousIdeal.mem_irrelevant_of_mem (piece e f)
      (by decide : 0 < 1) (coordinate_mem e f ij)
    have hh := h hx
    change quotientRay e f a b (coordinate e f ij) = 0 at hh
    rw [coordinate, quotientRay_mk, IntegerCoefficientProjectivePoint.rayMap_X] at hh
    exact mul_ne_zero (C_ne_zero.mpr hij) (X_ne_zero ()) hh

def productVector : Index (e + f) → F := fun m ↦
  eval (tensorVector e f a b) (map (Int.castRingHom F) (coefficientForm e f m))

theorem productVector_coefficient (m : Index (e + f)) :
    productVector e f a b m = (polynomial e a * polynomial f b).coeff m.val := by
  rw [productVector, evaluate_form, ← pure_tensor_product e f a b, tensor_coefficient]
  rfl

theorem productVector_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : productVector e f a b ≠ 0 := by
  intro hz
  apply pure_tensor_nonzero e f a b ha hb
  change tensorPolynomial e f (tensorVector e f a b) = 0
  rw [← reconstruct_tensor e f (tensorVector e f a b)]
  change polynomial (e + f) (productVector e f a b) = 0
  rw [hz]
  simp [polynomial]

theorem ray_composition :
    (quotientRay e f a b).comp (gradedMap e f).toRingHom =
      IntegerCoefficientProjectivePoint.rayMap (productVector e f a b) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro m
    change quotientRay e f a b (gradedMap e f (X m)) = _
    rw [gradedMap_X, coefficient, quotientRay_mk,
      IntegerCoefficientProjectivePoint.ray_homogeneous_value _ _ (form_homogeneous e f m),
      pow_one, IntegerCoefficientProjectivePoint.rayMap_X]
    rfl

theorem multiplication_point (ha : a ≠ 0) (hb : b ≠ 0) :
    P3FactorMultiplicationMap.multiplication e f (point e f a b ha hb) =
      IntegerCoefficientProjectivePoint.point (productVector e f a b)
        (productVector_ne_zero e f a b ha hb) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  apply Ideal.ext
  intro P
  change quotientRay e f a b (gradedMap e f P) = 0 ↔
    IntegerCoefficientProjectivePoint.rayMap (productVector e f a b) P = 0
  change ((quotientRay e f a b).comp (gradedMap e f).toRingHom) P = 0 ↔ _
  rw [ray_composition]

theorem product_point_mem_image (ha : a ≠ 0) (hb : b ≠ 0) :
    IntegerCoefficientProjectivePoint.point (productVector e f a b)
      (productVector_ne_zero e f a b ha hb) ∈
      Set.range (P3FactorMultiplicationMap.multiplication e f) :=
  ⟨point e f a b ha hb, multiplication_point e f a b ha hb⟩

end PaperP1.P3FactorSegreFieldPoint
