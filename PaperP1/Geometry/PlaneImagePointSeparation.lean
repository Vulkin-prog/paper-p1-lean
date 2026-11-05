module

public import PaperP1.Geometry.LinearPlaneImageFiber

/-! # Agreement of the three actual projected coordinates determines every good source point evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneImagePointSeparation

open MvPolynomial LinearPlaneImage

theorem evaluations_equal_of_coordinates {F A K L Ω : Type*} [Field F] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Field Ω] [Algebra F A] [Algebra F Ω]
    [Algebra (MvPolynomial (Fin 2) F) A] [IsScalarTower F (MvPolynomial (Fin 2) F) A]
    [Algebra (MvPolynomial (Fin 2) F) K] [Algebra K L] [Algebra A L] [Algebra (MvPolynomial (Fin 2) F) L]
    [IsScalarTower (MvPolynomial (Fin 2) F) K L] [IsScalarTower (MvPolynomial (Fin 2) F) A L]
    [IsFractionRing (MvPolynomial (Fin 2) F) K] [IsFractionRing A L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (g : Fin 2 → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤)
    (φ ψ : A →ₐ[F] Ω) (hcoords : ∀ i : Fin 3, φ (coordinates g y i) = ψ (coordinates g y i))
    (hδ : φ (LinearPlaneImageFiber.denominator (F := F) y) ≠ 0) : φ = ψ := by
  have hcomp : φ.comp (toSource (F := F) g y) = ψ.comp (toSource (F := F) g y) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change φ (toSource g y (Ideal.Quotient.mk (ideal g y) (X i))) =
      ψ (toSource g y (Ideal.Quotient.mk (ideal g y) (X i)))
    rw [toSource_mk, aeval_X]
    exact hcoords i
  apply LinearPlaneImageFiber.evaluations_equal g y hsource hfinite hprimitive φ ψ _ hδ
  intro b
  exact DFunLike.congr_fun hcomp b

end PaperP1.PlaneImagePointSeparation
