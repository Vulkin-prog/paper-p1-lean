module

public import PaperP1.Geometry.BoundedFiniteCurveParameters
public import PaperP1.Algebra.FiniteCurveParameterRank

/-! # Genuine bounded linear Noether normalization of the actual curve coordinate ring -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedCurveNoetherNormalization

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_normalization {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous 1) (hnot : f ∉ I) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * d + 1) ^ (n - 1)) ∧
      let φ := aeval (R := F) ![Ideal.Quotient.mk I f,
        Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))];
      φ.Finite ∧ Function.Injective φ ∧
        (letI : Algebra (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) := φ.toRingHom.toAlgebra;
          Module.finrank (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) = d) := by
  obtain ⟨u, hu, hfinite⟩ := BoundedFiniteCurveParameters.exists_bounded_finite_parameters
    n I hI hprime d hd b₀ hp f hf hnot
  let : I.IsPrime := hprime
  let H := HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I
  let : GradedAlgebra H := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin n) F) I hI
  let : ∀ r, Module.Finite F (H r) := fun r ↦ by
    let : Module.Finite F (homogeneousSubmodule (Fin n) F r) := MvPolynomialHilbert.piece_finite F (Fin n) r
    exact HomogeneousQuotientGrading.piece_finite _ I r
  let g : Fin 2 → (MvPolynomial (Fin n) F ⧸ I) := ![Ideal.Quotient.mk I f,
    Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))]
  have hg : ∀ i, g i ∈ H 1 := by
    intro i
    fin_cases i
    · exact Submodule.mem_map.mpr ⟨f, hf, rfl⟩
    · exact Submodule.mem_map.mpr ⟨_, CommonLinearNormalization.form_homogeneous _, rfl⟩
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hinj := FiniteCurveParameterIndependence.injective H g hg hfinite (d : ℚ) b₀ hdQ hp
  refine ⟨u, hu, hfinite, hinj, ?_⟩
  let : Algebra (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) :=
    (aeval (R := F) g).toRingHom.toAlgebra
  have hr := FiniteCurveParameterRank.rank_eq_slope H g hg hfinite (d : ℚ) b₀ hdQ hp
  exact_mod_cast hr

end PaperP1.BoundedCurveNoetherNormalization
