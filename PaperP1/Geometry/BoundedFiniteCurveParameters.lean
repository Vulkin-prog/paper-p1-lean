module

public import PaperP1.Algebra.FiniteLinearGradedParameters
public import PaperP1.Algebra.FiniteLinearZeroFiber
public import PaperP1.Algebra.MvPolynomialHilbert
public import Mathlib.Tactic.FinCases

/-! # Actual finite degree-one curve parameters with bounded integer coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedFiniteCurveParameters

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finite_of_avoidance {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (f : MvPolynomial σ F) (hf : f.IsHomogeneous 1)
    (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (havoid : ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f, eval p.rep ℓ ≠ 0) :
    (aeval (R := F) ![Ideal.Quotient.mk I f, Ideal.Quotient.mk I ℓ]).Finite := by
  classical
  let q := Ideal.Quotient.mkₐ F I
  let H := HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I
  let : GradedAlgebra H := HomogeneousQuotientGrading.grading (homogeneousSubmodule σ F) I hI
  let : ∀ n, Module.Finite F (H n) := fun n ↦ by
    let : Module.Finite F (homogeneousSubmodule σ F n) := MvPolynomialHilbert.piece_finite F σ n
    exact HomogeneousQuotientGrading.piece_finite _ I n
  let g : Fin 2 → (MvPolynomial σ F ⧸ I) := ![q f, q ℓ]
  let J := I ⊔ Ideal.span {f, ℓ}
  let K := Ideal.span (Set.range g)
  have hJ : J.IsHomogeneous (homogeneousSubmodule σ F) := hI.sup
    (Ideal.homogeneous_span _ _ (by
      intro P hP
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with rfl | rfl
      · exact ⟨1, hf⟩
      · exact ⟨1, hℓ⟩))
  let : Module.Finite F (MvPolynomial σ F ⧸ J) :=
    FiniteLinearZeroFiber.finite_of_avoidance I hI f hf ℓ hℓ havoid
  obtain ⟨N, hN, hcut⟩ := FiniteGradedSupport.eventually_le_ideal (homogeneousSubmodule σ F) J hJ
  have hle : J ≤ Ideal.comap q.toRingHom K := by
    apply sup_le
    · intro P hP
      change q P ∈ K
      have hz : q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hP
      rw [hz]
      exact K.zero_mem
    · apply Ideal.span_le.mpr
      intro P hP
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with rfl | rfl
      · exact Ideal.subset_span ⟨(0 : Fin 2), rfl⟩
      · exact Ideal.subset_span ⟨(1 : Fin 2), rfl⟩
  have hg : ∀ i, g i ∈ H 1 := by
    intro i
    fin_cases i
    · exact Submodule.mem_map.mpr ⟨f, hf, rfl⟩
    · exact Submodule.mem_map.mpr ⟨ℓ, hℓ, rfl⟩
  apply FiniteLinearGradedParameters.finite_evaluation_of_eventual_span H g hg N hN
  intro n hn x hx
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hx
  exact hle (hcut n hn hP)

theorem exists_bounded_finite_parameters {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous 1) (hnot : f ∉ I) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * d + 1) ^ (n - 1)) ∧
      (aeval (R := F) ![Ideal.Quotient.mk I f,
        Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))]).Finite := by
  obtain ⟨u, hu, havoid⟩ := BoundedProjectiveSectionAvoidance.exists_coefficients n I hI hprime d hd b₀ hp f hf hnot
  refine ⟨u, by simpa only [one_mul] using hu, ?_⟩
  exact finite_of_avoidance I hI f hf _ (CommonLinearNormalization.form_homogeneous _) havoid

end PaperP1.BoundedFiniteCurveParameters
