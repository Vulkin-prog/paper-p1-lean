module

public import PaperP1.Algebra.AffinePowerProjectionImage
public import PaperP1.Algebra.GeneratedThreeCoordinatePoints
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The literal affine projected image has exactly its monic irreducible hypersurface equation and all its field points

The polynomial kernel, quotient equivalence and exhaustive point correspondence
are proved from the actual source relation. No hypersurface-kernel identity or
point-lifting property is assumed.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.AffineProjectionHypersurfacePoints
open Polynomial PaperP1.LocalizedAffineQuadraticSource PaperP1.AffinePowerParameterFractionField
open PaperP1.AffinePowerProjectionImage
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarTower
variable (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) (s : List (Base F))

include hD in
theorem relation_iff_dvd (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (Q : (Parameters F)[X]) :
    (letI := sourceAlgebra F D s; Polynomial.aeval y Q = 0) ↔ P ∣ Q := by
  let := sourceAlgebra F D s
  let := genericAlgebra F D hD s
  let : Nontrivial (Generic F s) := generic_nontrivial F s
  have hPi := PaperP1.FullDegreeSourceDerivativeConductor.fraction_irreducible F P hmonic hP
  have hPy := PaperP1.FullDegreeSourceDerivativeConductor.generic_relation F D hD s P y hy
  have hmin := minpoly.eq_of_irreducible_of_monic hPi hPy (hmonic.map _)
  constructor
  · intro hQ
    have hh := minpoly.dvd (ParameterField F) (injection F s y)
      (PaperP1.FullDegreeSourceDerivativeConductor.generic_relation F D hD s Q y hQ)
    rw [← hmin] at hh
    exact (hmonic.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map (ParameterField F)).mpr hh
  · intro hQ
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hQ hy

include hD in
theorem source_kernel (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    letI := sourceAlgebra F D s
    RingHom.ker (Polynomial.aeval y).toRingHom = Ideal.span ({P} : Set (Parameters F)[X]) := by
  let := sourceAlgebra F D s
  ext Q
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact relation_iff_dvd F D hD s P hmonic hP y hy Q

def polynomialMap (y : Source F s) : (Parameters F)[X] →ₐ[F] image F D s y where
  toRingHom := Polynomial.eval₂RingHom (MvPolynomial.aeval (v F D s y)).toRingHom (z F D s y)
  commutes' r := by
    change (C (MvPolynomial.C r)).eval₂ (MvPolynomial.aeval (v F D s y)).toRingHom (z F D s y) = _
    rw [eval₂_C]
    exact (MvPolynomial.aeval (v F D s y)).commutes r

theorem polynomialMap_surjective (y : Source F s) : Function.Surjective (polynomialMap F D s y) := by
  apply (AlgHom.range_eq_top (polynomialMap F D s y)).mp
  have hh : Algebra.adjoin F (Set.range (Fin.cons (z F D s y) (v F D s y))) ≤
      (polynomialMap F D s y).range := by
    apply Algebra.adjoin_le
    rintro a ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change z F D s y ∈ (polynomialMap F D s y).range
      refine ⟨X, ?_⟩
      exact Polynomial.eval₂_X _ _
    · change v F D s y j ∈ (polynomialMap F D s y).range
      refine ⟨C (MvPolynomial.X j), ?_⟩
      change (C (MvPolynomial.X j)).eval₂ (MvPolynomial.aeval (v F D s y)).toRingHom (z F D s y) = _
      rw [eval₂_C]
      exact MvPolynomial.aeval_X _ j
  rw [image_generated] at hh
  exact top_unique hh

include hD in
theorem image_kernel (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    RingHom.ker (polynomialMap F D s y).toRingHom = Ideal.span ({P} : Set (Parameters F)[X]) := by
  ext Q
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change polynomial F D s y Q = 0 ↔ P ∣ Q
  have hv : polynomial F D s y Q = 0 ↔ (polynomial F D s y Q : Source F s) = 0 := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  rw [hv, polynomial_value]
  exact relation_iff_dvd F D hD s P hmonic hP y hy Q

include hD in
def quotientEquiv (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    AdjoinRoot P ≃ₐ[F] image F D s y :=
  (Ideal.quotientEquivAlgOfEq F (image_kernel F D hD s P hmonic hP y hy).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (polynomialMap_surjective F D s y))

theorem quotientEquiv_mk (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (Q : (Parameters F)[X]) :
    quotientEquiv F D hD s P hmonic hP y hy (AdjoinRoot.mk P Q) = polynomial F D s y Q := by
  rfl

theorem quotientEquiv_root (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    quotientEquiv F D hD s P hmonic hP y hy (AdjoinRoot.root P) = z F D s y := by
  change quotientEquiv F D hD s P hmonic hP y hy (AdjoinRoot.mk P X) = _
  rw [quotientEquiv_mk]
  exact Polynomial.eval₂_X _ _

theorem quotientEquiv_coefficient (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (Q : Parameters F) :
    quotientEquiv F D hD s P hmonic hP y hy (AdjoinRoot.of P Q) = MvPolynomial.aeval (v F D s y) Q := by
  change quotientEquiv F D hD s P hmonic hP y hy (AdjoinRoot.mk P (C Q)) = _
  rw [quotientEquiv_mk]
  exact Polynomial.eval₂_C _ _

include hD in
theorem point_lift (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (t : Fin 2 → F) (w : F) (hw : P.eval₂ (MvPolynomial.eval t) w = 0) :
    ∃ φ : image F D s y →ₐ[F] F, φ (z F D s y) = w ∧ ∀ i, φ (v F D s y i) = t i := by
  have hw' : P.eval₂ (MvPolynomial.aeval t).toRingHom w = 0 := hw
  let e := quotientEquiv F D hD s P hmonic hP y hy
  let f := AdjoinRoot.liftAlgHom P (MvPolynomial.aeval t) w hw'
  let φ : image F D s y →ₐ[F] F := f.comp e.symm.toAlgHom
  refine ⟨φ, ?_, ?_⟩
  · rw [← quotientEquiv_root F D hD s P hmonic hP y hy]
    change f (e.symm (e (AdjoinRoot.root P))) = w
    rw [e.symm_apply_apply]
    exact AdjoinRoot.liftAlgHom_root P (MvPolynomial.aeval t) w hw'
  · intro i
    have he : e (AdjoinRoot.of P (MvPolynomial.X i)) = v F D s y i := by
      rw [quotientEquiv_coefficient]
      exact MvPolynomial.aeval_X _ i
    rw [← he]
    change f (e.symm (e (AdjoinRoot.of P (MvPolynomial.X i)))) = t i
    rw [e.symm_apply_apply]
    change AdjoinRoot.liftAlgHom P (MvPolynomial.aeval t) w hw' (AdjoinRoot.of P (MvPolynomial.X i)) = _
    exact (AdjoinRoot.liftAlgHom_of P (MvPolynomial.aeval t) w hw' (MvPolynomial.X i)).trans
      (MvPolynomial.aeval_X _ i)

abbrev Solution (P : (Parameters F)[X]) :=
  {tw : (Fin 2 → F) × F // P.eval₂ (MvPolynomial.eval tw.1) tw.2 = 0}

def pointValues (P : (Parameters F)[X]) (y : Source F s)
    (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (φ : image F D s y →ₐ[F] F) : Solution F P := by
  refine ⟨PaperP1.GeneratedThreeCoordinatePoints.values (v F D s y) (z F D s y) φ, ?_⟩
  have hh := PaperP1.GeneratedThreeCoordinatePoints.mixed_evaluation (v F D s y) (z F D s y) φ P
  have he := equation F D s y P hy
  change P.eval₂ (MvPolynomial.aeval (v F D s y)).toRingHom (z F D s y) = 0 at he
  rw [he, map_zero] at hh
  exact hh.symm

include hD in
def pointsEquiv (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    (image F D s y →ₐ[F] F) ≃ Solution F P := by
  apply Equiv.ofBijective (pointValues F D s P y hy)
  constructor
  · intro φ ψ he
    exact PaperP1.GeneratedThreeCoordinatePoints.values_injective
      (v F D s y) (z F D s y) (image_generated F D s y) (congrArg Subtype.val he)
  · intro tw
    obtain ⟨φ, hz, hv⟩ := point_lift F D hD s P hmonic hP y hy tw.val.1 tw.val.2 tw.property
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    exact Prod.ext (funext hv) hz

include hD in
theorem point_cardinality (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    Nat.card (image F D s y →ₐ[F] F) = Nat.card (Solution F P) :=
  Nat.card_congr (pointsEquiv F D hD s P hmonic hP y hy)

end PaperP1.AffineProjectionHypersurfacePoints
