module

public import PaperP1.Arithmetic.IntegerLinearFormHeight
public import PaperP1.Geometry.QuotientPointEvaluation
public import Mathlib.Data.Int.Cast.Field

/-! # Literal integer linear coordinates, their coefficient-field evaluations and their heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerLinearPlaneProjection

open MvPolynomial

def coordinate {n : ℕ} (u : Fin n → ℕ) (w : Fin n → ℤ) : ℤ := ∑ i, (u i : ℤ) * w i

def projection {n : ℕ} (u v : Fin n → ℕ) (w : Fin n → ℤ) : ℤ × ℤ :=
  (coordinate u w, coordinate v w)

theorem coordinate_eq_evaluation {n : ℕ} (u : Fin n → ℕ) (w : Fin n → ℤ) :
    coordinate u w = eval w (CommonLinearNormalization.form (fun i ↦ (u i : ℤ))) :=
  (CommonLinearNormalization.evaluation _ _).symm

theorem coordinate_cast {F : Type*} [Field F] {n : ℕ} (u : Fin n → ℕ) (w : Fin n → ℤ) :
    (coordinate u w : F) =
      eval (fun i ↦ (w i : F)) (CommonLinearNormalization.form (fun i ↦ (u i : F))) := by
  rw [CommonLinearNormalization.evaluation]
  simp only [coordinate, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

theorem quotient_evaluation {F : Type*} [Field F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → ℕ) (w : Fin n → ℤ)
    (hw : ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0) :
    QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) hw
      (Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))) =
      (coordinate u w : F) := by
  rw [QuotientPointEvaluation.evaluation_mk, coordinate_cast]

theorem coordinate_height {n B H : ℕ} (u : Fin n → ℕ) (hu : ∀ i, u i ≤ B)
    (w : Fin n → ℤ) (hw : ∀ i, (w i).natAbs ≤ H) :
    (coordinate u w).natAbs ≤ n * B * H := by
  have hh := IntegerLinearFormHeight.evaluation_bound n B H u hu w hw
  rw [← coordinate_eq_evaluation, Int.abs_eq_natAbs] at hh
  exact_mod_cast hh

theorem projection_height {n B H : ℕ} (u v : Fin n → ℕ)
    (hu : ∀ i, u i ≤ B) (hv : ∀ i, v i ≤ B)
    (w : Fin n → ℤ) (hw : ∀ i, (w i).natAbs ≤ H) :
    (projection u v w).1.natAbs ≤ n * B * H ∧ (projection u v w).2.natAbs ≤ n * B * H :=
  ⟨coordinate_height u hu w hw, coordinate_height v hv w hw⟩

end PaperP1.IntegerLinearPlaneProjection
