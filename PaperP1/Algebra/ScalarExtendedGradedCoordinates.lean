module

public import PaperP1.Algebra.ScalarExtendedGradedHilbert
public import PaperP1.Algebra.CommonLinearNormalization

/-! # Original homogeneous generators and actual bounded integer forms after scalar extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarExtendedGradedCoordinates

open scoped TensorProduct

def coordinates {F A σ : Type*} [Field F] [CommRing A] [Algebra F A]
    (E : Type*) [Field E] [Algebra F E] (x : σ → A) : σ → E ⊗[F] A :=
  fun i ↦ (1 : E) ⊗ₜ[F] x i

theorem mem_piece {F E A σ : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (H : ℕ → Submodule F A) (x : σ → A)
    (hx : ∀ i, x i ∈ H 1) : ∀ i, coordinates (F := F) E x i ∈ (H 1).baseChange E := by
  intro i
  exact Submodule.tmul_mem_baseChange_of_mem 1 (hx i)

theorem generates {F E A σ : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (x : σ → A) (hgen : Algebra.adjoin F (Set.range x) = ⊤) :
    Algebra.adjoin E (Set.range (coordinates (F := F) E x)) = ⊤ := by
  have hh := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
    (R := F) (A := E) (B := A) (Set.range x) hgen
  have he : ((fun a : A ↦ (1 : E) ⊗ₜ[F] a) '' Set.range x) =
      Set.range (coordinates (F := F) E x) := by
    ext t
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  rwa [he] at hh

theorem linear_form {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] {n : ℕ} (x : Fin n → A) (u : Fin n → ℕ) :
    MvPolynomial.aeval (R := E) (coordinates (F := F) E x)
      (CommonLinearNormalization.form (fun i ↦ (u i : E))) =
      (1 : E) ⊗ₜ[F] (MvPolynomial.aeval (R := F) x
        (CommonLinearNormalization.form (fun i ↦ (u i : F)))) := by
  let ι : A →ₐ[F] E ⊗[F] A := Algebra.TensorProduct.includeRight
  change MvPolynomial.aeval (R := E) (coordinates (F := F) E x)
      (CommonLinearNormalization.form (fun i ↦ (u i : E))) =
      ι (MvPolynomial.aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F))))
  simp only [CommonLinearNormalization.form, map_sum, map_mul,
    MvPolynomial.aeval_X, map_natCast]
  rfl

end PaperP1.ScalarExtendedGradedCoordinates
