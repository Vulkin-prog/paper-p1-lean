module

public import PaperP1.Geometry.ScalarExtendedRegularParameters
public import PaperP1.Algebra.ScalarExtendedParameterFiber
public import PaperP1.Algebra.FiniteLinearGradedParameters
public import PaperP1.Algebra.CoordinateFractionFieldGenerators
public import PaperP1.Algebra.MvPolynomialHilbert
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual bounded finite chart normalization over the original coefficient field, without geometric integrality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalFieldFiniteCurveParameters

open MvPolynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_parameters {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (hnot : X z ∉ I) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * d + 1) ^ (n - 1)) ∧
      (aeval (R := F) ![Ideal.Quotient.mk I (X z),
        Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))]).Finite := by
  classical
  let : I.IsPrime := hprime
  let A := MvPolynomial (Fin n) F ⧸ I
  let H := HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I
  let : GradedAlgebra H := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin n) F) I hI
  let : ∀ r, Module.Finite F (H r) := fun r ↦ by
    let : Module.Finite F (homogeneousSubmodule (Fin n) F r) := MvPolynomialHilbert.piece_finite F (Fin n) r
    exact HomogeneousQuotientGrading.piece_finite _ I r
  let x : Fin n → A := fun i ↦ Ideal.Quotient.mk I (X i)
  have hx : ∀ i, x i ∈ H 1 := fun i ↦
    Submodule.mem_map.mpr ⟨X i, isHomogeneous_X F i, rfl⟩
  have hgen : Algebra.adjoin F (Set.range x) = ⊤ := CoordinateFractionFieldGenerators.quotient_variables_generate I
  let E := AlgebraicClosure F
  have hx0 : x z ≠ 0 := fun hh ↦ hnot (Ideal.Quotient.eq_zero_iff_mem.mp hh)
  obtain ⟨u, hu, N, hN, hpow⟩ := ScalarExtendedRegularParameters.exists_coefficients_powers
    (E := E) n H x hx hgen d hd b₀ hp z hx0
  let g : Fin 2 → A := ![Ideal.Quotient.mk I (X z),
    Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))]
  have heval : aeval (R := F) x = Ideal.Quotient.mkₐ F I := by
    apply MvPolynomial.algHom_ext
    intro i
    exact aeval_X _ i
  have hzeroFiber := ScalarExtendedParameterFiber.finite_fiber (E := E) x hgen z u N hN hpow
  rw [heval] at hzeroFiber
  let : Module.Finite F (A ⧸ Ideal.span (Set.range g)) := hzeroFiber
  have hg : ∀ i, g i ∈ H 1 := by
    intro i
    fin_cases i
    · exact hx z
    · exact Submodule.mem_map.mpr ⟨_, CommonLinearNormalization.form_homogeneous _, rfl⟩
  refine ⟨u, hu, ?_⟩
  exact FiniteLinearGradedParameters.finite_evaluation_of_adjoin g
    (FiniteLinearGradedParameters.finite_adjoin_of_finite_quotient H g hg)

end PaperP1.OriginalFieldFiniteCurveParameters
