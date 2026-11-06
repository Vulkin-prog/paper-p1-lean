module

public import PaperP1.Geometry.LinearHypersurfaceImageFiber

/-! # Agreement of the actual projected hypersurface coordinates determines every good source point evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HypersurfaceImagePointSeparation

open MvPolynomial LinearHypersurfaceImage

theorem evaluations_equal_of_conductor {m : ℕ} {F A Ω : Type*} [Field F] [CommRing A]
    [Field Ω] [Algebra F A] [Algebra F Ω] (g : Fin m → A) (y δ : A)
    (hconductor : ∀ a : A, δ * a ∈ (toSource (F := F) g y).range)
    (φ ψ : A →ₐ[F] Ω) (hcoords : ∀ i, φ (coordinates g y i) = ψ (coordinates g y i))
    (hδ : φ δ ≠ 0) : φ = ψ := by
  have hcomp : φ.comp (toSource (F := F) g y) = ψ.comp (toSource (F := F) g y) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change φ (toSource g y (Ideal.Quotient.mk (ideal g y) (X i))) =
      ψ (toSource g y (Ideal.Quotient.mk (ideal g y) (X i)))
    rw [toSource_mk, aeval_X]
    exact hcoords i
  apply ConductorFiberInjectivity.evaluations_equal (toSource (F := F) g y).range δ
    hconductor φ ψ _ hδ
  intro a ha
  obtain ⟨b, rfl⟩ := ha
  exact DFunLike.congr_fun hcomp b

theorem evaluations_equal_of_coordinates {m : ℕ} {F A K L Ω : Type*} [Field F] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Field Ω] [Algebra F A] [Algebra F Ω]
    [Algebra (MvPolynomial (Fin m) F) A] [IsScalarTower F (MvPolynomial (Fin m) F) A]
    [Algebra (MvPolynomial (Fin m) F) K] [Algebra K L] [Algebra A L] [Algebra (MvPolynomial (Fin m) F) L]
    [IsScalarTower (MvPolynomial (Fin m) F) K L] [IsScalarTower (MvPolynomial (Fin m) F) A L]
    [IsFractionRing (MvPolynomial (Fin m) F) K] [IsFractionRing A L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤)
    (φ ψ : A →ₐ[F] Ω) (hcoords : ∀ i : Fin (m + 1), φ (coordinates g y i) = ψ (coordinates g y i))
    (hδ : φ (LinearHypersurfaceImageFiber.denominator (m := m) (F := F) y) ≠ 0) : φ = ψ := by
  exact evaluations_equal_of_conductor g y (LinearHypersurfaceImageFiber.denominator (m := m) (F := F) y)
    (LinearHypersurfaceImageFiber.conductor g y hsource hfinite hprimitive) φ ψ hcoords hδ

end PaperP1.HypersurfaceImagePointSeparation
