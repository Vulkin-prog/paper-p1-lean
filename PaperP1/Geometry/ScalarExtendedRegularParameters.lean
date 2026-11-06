module

public import PaperP1.Geometry.BoundedRegularSectionAvoidance
public import PaperP1.Algebra.ScalarExtendedGradedCoordinates

/-! # Bounded original integer parameter coefficients selected in the actual regular scalar extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarExtendedRegularParameters

open MvPolynomial
open scoped TensorProduct

theorem exists_coefficients_powers {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero E] [IsAlgClosed E] [CommRing A] [Algebra F A] [IsDomain A] (n : ℕ)
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : Fin n → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀)) (z : Fin n) (hz : x z ≠ 0) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * d + 1) ^ (n - 1)) ∧
      ∃ N : ℕ, 0 < N ∧ ∀ i : Fin n, (X i) ^ N ∈
        GradedPolynomialPresentation.kernel (F := E) (ScalarExtendedGradedCoordinates.coordinates (F := F) E x) ⊔
          Ideal.span {X z, CommonLinearNormalization.form (fun i ↦ (u i : E))} := by
  let G : ℕ → Submodule E (E ⊗[F] A) := fun r ↦ (H r).baseChange E
  let : GradedAlgebra G := inferInstance
  let y := ScalarExtendedGradedCoordinates.coordinates (F := F) E x
  have hy : ∀ i, y i ∈ G 1 := ScalarExtendedGradedCoordinates.mem_piece H x hx
  have hgen' : Algebra.adjoin E (Set.range y) = ⊤ := ScalarExtendedGradedCoordinates.generates x hgen
  have hp' : GradedHilbertPolynomial.IsHilbertPolynomial G
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀) :=
    ScalarExtendedGradedHilbert.hilbertPolynomial H _ hp
  have hregular : Function.Injective (fun a : E ⊗[F] A ↦ a * aeval (R := E) y (X z)) := by
    rw [aeval_X]
    exact ScalarExtendedGradedHilbert.nonzero_domain_section_regular (x z) hz
  obtain ⟨u, hu, N, hN, hpow⟩ := BoundedRegularSectionAvoidance.exists_coefficients_powers
    n G y hy hgen' d hd b₀ hp' (X z) (isHomogeneous_X E z) hregular
  exact ⟨u, by simpa only [one_mul] using hu, N, hN, hpow⟩

end PaperP1.ScalarExtendedRegularParameters
