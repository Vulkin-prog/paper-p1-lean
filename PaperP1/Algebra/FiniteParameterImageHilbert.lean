module

public import PaperP1.Algebra.FiniteCurveParameterRank
public import PaperP1.Algebra.TwoVariableGradedHilbert

/-! # Actual finite independent linear parameters of rank d give the exact linear Hilbert degree d -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteParameterImageHilbert

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

local instance fieldCommSemiring (F : Type*) [Field F] : CommSemiring F :=
  (inferInstance : Field F).toCommRing.toCommSemiring
local instance polynomialRing (F σ : Type*) [Field F] : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (F σ : Type*) [Field F] : Semiring (MvPolynomial σ F) :=
  (polynomialRing F σ).toSemiring

theorem exists_linear_hilbert {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsDomain A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 2 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hinj : Function.Injective (aeval (R := F) g)) (d : ℕ)
    (hrank : letI : Algebra (MvPolynomial (Fin 2) F) A := (aeval (R := F) g).toRingHom.toAlgebra;
      Module.finrank (MvPolynomial (Fin 2) F) A = d) :
    ∃ b : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b) := by
  let : Algebra (MvPolynomial (Fin 2) F) A := (aeval (R := F) g).toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin 2) F) A := hfinite
  let f := GradedPolynomialGenerators.gradedEval H g hg
  obtain ⟨ι, hι, v, w, hv, hspan⟩ := FiniteHomogeneousModuleGenerators.exists_generators
    (A := MvPolynomial (Fin 2) F) H
  let : Fintype ι := hι
  have hs := FiniteGradedLinearGrowth.hasSlope f
    (fun r ↦ (aeval (R := F) g).commutes r) v w hv hinj hspan
    (fun n ↦ MvPolynomialHilbert.piece_finite F (Fin 2) n) 1 1 (FiniteCurveParameterRank.base_hilbert F)
  have hcoherent : (letI : Algebra (MvPolynomial (Fin 2) F) A := f.toRingHom.toAlgebra;
      Module.finrank (MvPolynomial (Fin 2) F) A) = Module.finrank (MvPolynomial (Fin 2) F) A :=
    @Algebra.finrank_eq_of_equiv_equiv
      (MvPolynomial (Fin 2) F) A _ _ (f.toRingHom.toAlgebra)
      (MvPolynomial (Fin 2) F) A _ _ ((aeval (R := F) g).toRingHom.toAlgebra)
      (RingEquiv.refl _) (RingEquiv.refl _) (by ext p <;> rfl)
  have he : (letI : Algebra (MvPolynomial (Fin 2) F) A := f.toRingHom.toAlgebra;
      (Module.finrank (MvPolynomial (Fin 2) F) A : ℚ) * 1) = (d : ℚ) := by
    rw [mul_one, hcoherent, hrank]
  have hsD : LinearHilbertGrowth.HasSlope (LinearHilbertGrowth.function H) (d : ℚ) := he ▸ hs
  obtain ⟨p, hp⟩ := TwoVariableGradedHilbert.exists_polynomial_of_finite H g hg hfinite
  obtain ⟨b, hb⟩ := LinearHilbertGrowth.hilbert_polynomial_affine hsD hp
  exact ⟨b, hb ▸ hp⟩

end PaperP1.FiniteParameterImageHilbert
