module

public import PaperP1.Algebra.ProjectiveHypersurfaceHilbert
public import PaperP1.Algebra.FiniteSurfaceParameterInjectivity
public import PaperP1.Algebra.HomogeneousLinearNormalization

/-! # Actual integral projective surface hypersurfaces construct three finite independent linear parameters -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveHypersurfaceFiniteParameters

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_parameters (F : Type*) [Field F] [Infinite F]
    (I : Ideal (MvPolynomial (Fin 4) F)) (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    [I.IsPrime] (d : ℕ) (hd : 0 < d) (q : MvPolynomial (Fin 4) F) (hspan : I = Ideal.span {q})
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) :
    letI := HomogeneousQuotientGrading.grading (MvPolynomial.homogeneousSubmodule (Fin 4) F) I hI;
    ∃ g : Fin 3 → (MvPolynomial (Fin 4) F ⧸ I),
      (∀ i, g i ∈ HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule (Fin 4) F) I 1) ∧
      (MvPolynomial.aeval (R := F) g).Finite ∧ Function.Injective (MvPolynomial.aeval (R := F) g) := by
  let := HomogeneousQuotientGrading.grading (MvPolynomial.homogeneousSubmodule (Fin 4) F) I hI
  let H := HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule (Fin 4) F) I
  let (n : ℕ) : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 4) F n) :=
    MvPolynomialHilbert.piece_finite F (Fin 4) n
  let (n : ℕ) : Module.Finite F (H n) :=
    HomogeneousQuotientGrading.piece_finite (MvPolynomial.homogeneousSubmodule (Fin 4) F) I n
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial H (ProjectiveHypersurfaceHilbert.polynomial d) := by
    dsimp [H]
    rw [hspan]
    exact ProjectiveHypersurfaceHilbert.isHilbertPolynomial F d q hq hq0
  have hmem : q ∈ I := by rw [hspan]; exact Ideal.mem_span_singleton_self q
  obtain ⟨g, hg, hgfinite⟩ := HomogeneousLinearNormalization.exists_parameters I q hq hq0 hmem
  refine ⟨g, hg, hgfinite, ?_⟩
  apply FiniteSurfaceParameterInjectivity.injective H (ProjectiveHypersurfaceHilbert.polynomial d) hp _ g hg hgfinite
  rw [ProjectiveHypersurfaceHilbert.coeff_two]
  exact div_ne_zero (by exact_mod_cast Nat.ne_of_gt hd) (by norm_num)

end PaperP1.ProjectiveHypersurfaceFiniteParameters
