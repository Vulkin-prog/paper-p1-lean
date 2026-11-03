module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Explicit bases after quotienting the coefficient ring and transporting scalars -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuotientFreeBasis

open Module

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (e : Basis ι A B) (I : Ideal A)

def basis : Basis ι (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  (e.baseChange (A ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

theorem basis_apply (i : ι) : basis e I i = Ideal.Quotient.mk _ (e i) := by
  rw [basis, Basis.map_apply, Basis.baseChange_apply]
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
  change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm (1 ⊗ₜ[A] e i)) = _
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]

variable {S T : Type*} [CommRing S] [CommRing T]
  (eA : A ⧸ I ≃+* S) (eB : B ⧸ I.map (algebraMap A B) ≃+* T) (f : S →+* T)
  (hcomm : ∀ a : A, eB (Ideal.Quotient.mk _ (algebraMap A B a)) =
    f (eA (Ideal.Quotient.mk I a)))

def transported :
    letI : Algebra S T := f.toAlgebra
    Basis ι S T := by
  let : Algebra S T := f.toAlgebra
  let : Algebra (A ⧸ I) T := (f.comp eA.toRingHom).toAlgebra
  let eAlg : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] T :=
    { eB with
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact hcomm a }
  exact ((basis e I).map eAlg.toLinearEquiv).mapCoeffs eA (fun _ _ ↦ rfl)

set_option backward.isDefEq.respectTransparency false in
theorem transported_apply (i : ι) :
    letI : Algebra S T := f.toAlgebra
    transported e I eA eB f hcomm i = eB (Ideal.Quotient.mk _ (e i)) := by
  let : Algebra S T := f.toAlgebra
  let : Algebra (A ⧸ I) T := (f.comp eA.toRingHom).toAlgebra
  rw [transported, Basis.mapCoeffs_apply, Basis.map_apply, basis_apply]
  rfl

end PaperP1.QuotientFreeBasis
