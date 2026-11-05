module

public import PaperP1.Algebra.FiniteCurveParameterIndependence
public import PaperP1.Algebra.FiniteGradedLinearGrowth
public import PaperP1.Algebra.MvPolynomialHilbert

/-! # The actual finite linear parameter rank equals the original positive Hilbert slope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCurveParameterRank

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

local instance fieldCommSemiring (F : Type*) [Field F] : CommSemiring F :=
  (inferInstance : Field F).toCommRing.toCommSemiring
local instance polynomialRing (F σ : Type*) [Field F] : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (F σ : Type*) [Field F] : Semiring (MvPolynomial σ F) :=
  (polynomialRing F σ).toSemiring

theorem base_hilbert (F : Type*) [Field F] :
    GradedHilbertPolynomial.IsHilbertPolynomial (homogeneousSubmodule (Fin 2) F)
      (Polynomial.C 1 * Polynomial.X + Polynomial.C 1) := by
  refine ⟨0, fun n _hn ↦ ?_⟩
  rw [MvPolynomialHilbert.piece_finrank]
  simp only [Nat.card_fin, show 2 + n - 1 = n + 1 by omega, Nat.choose_succ_self_right]
  simp

theorem rank_eq_slope {F A : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A] [IsDomain A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 2 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (a b : ℚ) (ha : 0 < a)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H (Polynomial.C a * Polynomial.X + Polynomial.C b)) :
    letI : Algebra (MvPolynomial (Fin 2) F) A := (aeval (R := F) g).toRingHom.toAlgebra
    (Module.finrank (MvPolynomial (Fin 2) F) A : ℚ) = a := by
  let : Algebra (MvPolynomial (Fin 2) F) A := (aeval (R := F) g).toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin 2) F) A := hfinite
  let f := GradedPolynomialGenerators.gradedEval H g hg
  obtain ⟨ι, hι, v, w, hv, hspan⟩ := FiniteHomogeneousModuleGenerators.exists_generators
    (A := MvPolynomial (Fin 2) F) H
  let : Fintype ι := hι
  have hinj : Function.Injective f := FiniteCurveParameterIndependence.injective H g hg hfinite a b ha hp
  have hc := FiniteGradedLinearGrowth.coefficient_eq f
    (fun r ↦ (aeval (R := F) g).commutes r) v w hv hinj hspan
    (fun n ↦ MvPolynomialHilbert.piece_finite F (Fin 2) n) 1 1 (base_hilbert F)
    (Polynomial.C a * Polynomial.X + Polynomial.C b) hp
  convert hc.symm using 1
  · rw [mul_one]
    apply congrArg (fun r : ℕ ↦ (r : ℚ))
    exact @Algebra.finrank_eq_of_equiv_equiv
      (MvPolynomial (Fin 2) F) A _ _ ((aeval (R := F) g).toRingHom.toAlgebra)
      (MvPolynomial (Fin 2) F) A _ _ (f.toRingHom.toAlgebra)
      (RingEquiv.refl _) (RingEquiv.refl _) (by ext p <;> rfl)
  · simp

end PaperP1.FiniteCurveParameterRank
