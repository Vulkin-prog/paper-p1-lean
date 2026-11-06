module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Scalar extension of an actual polynomial coordinate quotient is the coefficient-extended quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialQuotientScalarExtension

open scoped TensorProduct
open MvPolynomial

variable {F E σ : Type*} [CommRing F] [CommRing E] [Algebra F E]

theorem polynomial_map (P : MvPolynomial σ F) :
    MvPolynomial.algebraTensorAlgEquiv F E ((1 : E) ⊗ₜ[F] P) = map (algebraMap F E) P := by
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

theorem ideal_map (I : Ideal (MvPolynomial σ F)) :
    (I.map (Algebra.TensorProduct.includeRight (A := E) (R := F)).toRingHom).map
      (MvPolynomial.algebraTensorAlgEquiv F E).toRingHom = I.map (map (algebraMap F E)) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro P
  exact polynomial_map P

def equiv (I : Ideal (MvPolynomial σ F)) :
    E ⊗[F] (MvPolynomial σ F ⧸ I) ≃ₐ[E]
      MvPolynomial σ E ⧸ I.map (map (algebraMap F E)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv E (MvPolynomial σ F) E I).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv F E) (ideal_map I).symm)

theorem equiv_tmul_mk (I : Ideal (MvPolynomial σ F)) (a : E) (P : MvPolynomial σ F) :
    equiv (E := E) I (a ⊗ₜ[F] Ideal.Quotient.mk I P) =
      Ideal.Quotient.mk (I.map (map (algebraMap F E))) (a • map (algebraMap F E) P) := by
  change Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv F E) (ideal_map I).symm
    (Algebra.TensorProduct.tensorQuotientEquiv E (MvPolynomial σ F) E I
      (a ⊗ₜ[F] Ideal.Quotient.mk I P)) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.Quotient.mk _ (MvPolynomial.algebraTensorAlgEquiv F E (a ⊗ₜ[F] P)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]

end PaperP1.PolynomialQuotientScalarExtension
