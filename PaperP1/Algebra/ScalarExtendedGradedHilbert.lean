module

public import PaperP1.Algebra.RegularGradedHilbertSection
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Scalar extension preserves actual homogeneous dimensions and regular section multiplication -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarExtendedGradedHilbert

open scoped TensorProduct

theorem piece_finrank {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (H : ℕ → Submodule F A) (n : ℕ) :
    Module.finrank E ((H n).baseChange E) = Module.finrank F (H n) := by
  calc
    _ = Module.finrank E (E ⊗[F] H n) := (Submodule.toBaseChange.toLinearEquiv E (H n)).finrank_eq.symm
    _ = _ := Module.finrank_baseChange

theorem piece_finite {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (H : ℕ → Submodule F A) (n : ℕ) [Module.Finite F (H n)] :
    Module.Finite E ((H n).baseChange E) := by
  let : Module.Finite E (E ⊗[F] H n) := inferInstance
  exact Module.Finite.equiv (Submodule.toBaseChange.toLinearEquiv E (H n))

theorem hilbertPolynomial {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (H : ℕ → Submodule F A) [GradedAlgebra H]
    (P : Polynomial ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H P) :
    GradedHilbertPolynomial.IsHilbertPolynomial (fun n ↦ (H n).baseChange E) P := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [piece_finrank]
  exact hN n hn

theorem lTensor_mulRight {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (f : A) (t : E ⊗[F] A) :
    (LinearMap.mulRight F f).lTensor E t = t * ((1 : E) ⊗ₜ[F] f) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [LinearMap.mulRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add, ha, hb, add_mul]

theorem regular_multiplication {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (f : A) (hregular : Function.Injective (fun a : A ↦ a * f)) :
    Function.Injective (fun t : E ⊗[F] A ↦ t * ((1 : E) ⊗ₜ[F] f)) := by
  have hmap : Function.Injective ((LinearMap.mulRight F f).lTensor E) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := E) _ hregular
  intro a b he
  apply hmap
  rw [lTensor_mulRight, lTensor_mulRight]
  exact he

theorem nonzero_domain_section_regular {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] [IsDomain A] (f : A) (hf : f ≠ 0) :
    Function.Injective (fun t : E ⊗[F] A ↦ t * ((1 : E) ⊗ₜ[F] f)) :=
  regular_multiplication f (fun _ _ he ↦ mul_right_cancel₀ hf he)

theorem section_dimension {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] [IsDomain A] (H : ℕ → Submodule F A) [GradedAlgebra H]
    (d : ℕ) (hd : 0 < d) (b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b))
    {e : ℕ} {f : A} (hf : f ∈ H e) (hf0 : f ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, Module.finrank E
      (HomogeneousPrincipalQuotient.piece (fun r ↦ (H r).baseChange E) ((1 : E) ⊗ₜ[F] f) (n + e)) = e * d := by
  exact RegularGradedHilbertSection.eventual_dimension (fun r ↦ (H r).baseChange E) d hd b
    (hilbertPolynomial H _ hp) (Submodule.tmul_mem_baseChange_of_mem 1 hf)
    (nonzero_domain_section_regular f hf0)

end PaperP1.ScalarExtendedGradedHilbert
