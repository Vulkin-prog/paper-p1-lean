module

public import PaperP1.Algebra.ProjectiveAvoidanceRadical
public import PaperP1.Geometry.BoundedProjectiveSectionAvoidance
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Actual section-avoiding linear parameters have a finite-dimensional zero fibre -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteLinearZeroFiber

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finite_of_variable_powers {F σ : Type*} [Field F] [Finite σ]
    (J : Ideal (MvPolynomial σ F)) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ i : σ, (X i) ^ N ∈ J) : Module.Finite F (MvPolynomial σ F ⧸ J) := by
  let q := Ideal.Quotient.mkₐ F J
  let g : σ → (MvPolynomial σ F ⧸ J) := fun i ↦ q (X i)
  have hint (i : σ) : IsIntegral F (g i) := by
    apply IsIntegral.of_pow hN
    have hz : g i ^ N = 0 := by
      change q (X i) ^ N = 0
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpow i)
    rw [hz]
    exact isIntegral_zero
  have he : aeval (R := F) g = q := by
    apply MvPolynomial.algHom_ext
    intro i
    exact aeval_X g i
  have hgen : Algebra.adjoin F (Set.range g) = ⊤ := by
    rw [← MvPolynomial.aeval_range, he]
    exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective F J)
  let : Module.Finite F (Algebra.adjoin F (Set.range g)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range g) (by
      rintro _ ⟨i, rfl⟩
      exact hint i)
  exact Module.Finite.of_surjective (Algebra.adjoin F (Set.range g)).val.toLinearMap (by
    intro b
    exact ⟨⟨b, by rw [hgen]; trivial⟩, rfl⟩)

theorem finite_of_avoidance {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (havoid : ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f, eval p.rep ℓ ≠ 0) :
    Module.Finite F (MvPolynomial σ F ⧸ (I ⊔ Ideal.span {f, ℓ})) := by
  obtain ⟨N, hN, hpow⟩ := ProjectiveAvoidanceRadical.exists_uniform_power I hI f hf ℓ hℓ havoid
  exact finite_of_variable_powers _ N hN hpow

theorem bounded_linear_zero_fiber {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous 1) (hnot : f ∉ I) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * d + 1) ^ (n - 1)) ∧
      Module.Finite F (MvPolynomial (Fin n) F ⧸
        (I ⊔ Ideal.span {f, CommonLinearNormalization.form (fun i ↦ (u i : F))})) := by
  obtain ⟨u, hu, havoid⟩ := BoundedProjectiveSectionAvoidance.exists_coefficients n I hI hprime d hd b₀ hp f hf hnot
  refine ⟨u, by simpa only [one_mul] using hu, ?_⟩
  exact finite_of_avoidance I hI f hf _ (CommonLinearNormalization.form_homogeneous _) havoid

end PaperP1.FiniteLinearZeroFiber
