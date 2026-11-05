module

public import PaperP1.Geometry.ProjectiveSectionFiniteSet
public import PaperP1.Algebra.BoundedMomentLinearForm
public import PaperP1.Arithmetic.IntegerLinearFormHeight
public import Mathlib.Algebra.CharZero.Infinite

/-! # Bounded integer linear forms avoiding an entire actual projective section -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedProjectiveSectionAvoidance

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_coefficients {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous e) (hnot : f ∉ I) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * (e * d) + 1) ^ (n - 1)) ∧
      ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f,
        eval p.rep (CommonLinearNormalization.form (fun i ↦ (u i : F))) ≠ 0 := by
  classical
  obtain ⟨E, hE, hcard⟩ := ProjectiveSectionFiniteSet.exists_finset I hI hprime d hd b₀ hp f hf hnot
  let S := E.image (fun p ↦ p.rep)
  have hS : S.card ≤ e * d := by
    change (E.image (fun p ↦ p.rep)).card ≤ _
    rw [Finset.card_image_of_injective _ ProjectiveSectionFiniteSet.rep_injective]
    exact hcard
  obtain ⟨u, hu, hnonzero⟩ := BoundedMomentLinearForm.exists_coefficients n S (by
    intro w hw
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hw
    exact p.rep_ne_zero)
  refine ⟨u, ?_, ?_⟩
  · intro i
    apply (hu i).trans
    apply Nat.pow_le_pow_left
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (n - 1) hS) 1
  · intro p hpsection
    exact hnonzero p.rep (Finset.mem_image.mpr ⟨p, (hE p).mpr hpsection, rfl⟩)

theorem exists_coefficients_and_height {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous e) (hnot : f ∉ I) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * (e * d) + 1) ^ (n - 1)) ∧
      (∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f,
        eval p.rep (CommonLinearNormalization.form (fun i ↦ (u i : F))) ≠ 0) ∧
      ∀ (H : ℕ) (v : Fin n → ℤ), (∀ i, (v i).natAbs ≤ H) →
        |eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤
          ((n * (((n - 1) * (e * d) + 1) ^ (n - 1)) * H : ℕ) : ℤ) := by
  obtain ⟨u, hu, hnonzero⟩ := exists_coefficients n I hI hprime d hd b₀ hp f hf hnot
  exact ⟨u, hu, hnonzero, fun H v hv ↦ IntegerLinearFormHeight.evaluation_bound n _ H u hu v hv⟩

theorem rational_curve {n : ℕ} (Γ : ProjectiveCurveData.Curve (Fin n)) {e : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal) :
    ∃ u : Fin n → ℕ,
      (∀ i, u i ≤ ((n - 1) * (e * ProjectiveCurveHilbertDegree.natDegree Γ) + 1) ^ (n - 1)) ∧
      (∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus Γ.ideal f,
        eval p.rep (CommonLinearNormalization.form (fun i ↦ (u i : ℚ))) ≠ 0) ∧
      ∀ (H : ℕ) (v : Fin n → ℤ), (∀ i, (v i).natAbs ≤ H) →
        |eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤
          ((n * (((n - 1) * (e * ProjectiveCurveHilbertDegree.natDegree Γ) + 1) ^ (n - 1)) * H : ℕ) : ℤ) := by
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial (ProjectiveCurveData.piece Γ.ideal)
      (Polynomial.C (ProjectiveCurveHilbertDegree.natDegree Γ : ℚ) * Polynomial.X + Polynomial.C Γ.constant) := by
    rw [ProjectiveCurveHilbertDegree.natDegree_cast Γ]
    exact Γ.hilbert
  exact exists_coefficients_and_height n Γ.ideal Γ.homogeneous Γ.prime _
    (ProjectiveCurveHilbertDegree.natDegree_pos Γ) Γ.constant hp f hf hnot

end PaperP1.BoundedProjectiveSectionAvoidance
