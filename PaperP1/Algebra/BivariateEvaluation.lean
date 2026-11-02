module

public import PaperP1.Algebra.BivariateReciprocalProduct

/-! # Actual nested-polynomial evaluation and the finite reciprocal scaling identity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateEvaluation

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BiquadraticCoefficientPolynomials

def evaluate {R : Type*} [CommRing R] (x y : R) : ℤ[X][X] →+* R :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) x) y

theorem rectangle_evaluation {R : Type*} [CommRing R] (x y : R) (a b : ℕ)
    (w : Fin (a + 1) × Fin (b + 1) → ℤ) :
    evaluate x y (rectangle a b w) =
      ∑ i : Fin (a + 1) × Fin (b + 1), (w i : R) * x ^ i.1.val * y ^ i.2.val := by
  unfold evaluate rectangle row
  simp only [map_sum, coe_eval₂RingHom, eval₂_monomial, Int.coe_castRingHom, Fintype.sum_prod_type]
  exact sum_comm

theorem integer_evaluation {R : Type*} [CommRing R] (P : ℤ[X][X]) (x y : ℤ) :
    evaluate (x : R) (y : R) P = ((P.evalEval x y : ℤ) : R) := by
  have he : evaluate (x : R) (y : R) = (Int.castRingHom R).comp (Polynomial.evalEvalRingHom x y) := by
    ext <;> simp [evaluate]
  exact congrArg (fun φ : ℤ[X][X] →+* R ↦ φ P) he

theorem reciprocal_sum_scaled {R : Type*} [Field R] (P : ℤ[X][X]) (a b : ℕ)
    (hxP : degreeX P ≤ a) (hyP : degreeY P ≤ b) (x y : R) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ a * y ^ b * (∑ i : Fin (a + 1) × Fin (b + 1),
      ((P.coeff i.2.val).coeff i.1.val : R) * (1 / x) ^ (a - i.1.val) * (1 / y) ^ (b - i.2.val)) =
        evaluate x y P := by
  have heval : evaluate x y P = ∑ i : Fin (a + 1) × Fin (b + 1),
      ((P.coeff i.2.val).coeff i.1.val : R) * x ^ i.1.val * y ^ i.2.val := by
    conv_lhs => rw [← BivariateReciprocalProduct.rectangle_reconstruction P a b hxP hyP]
    exact rectangle_evaluation x y a b _
  rw [heval, mul_sum]
  apply sum_congr rfl
  intro i _
  have hxi := BivariateReciprocalProduct.reverse_power x hx a (a - i.1.val) (Nat.sub_le _ _)
  have hyi := BivariateReciprocalProduct.reverse_power y hy b (b - i.2.val) (Nat.sub_le _ _)
  have heX : a - (a - i.1.val) = i.1.val := by omega
  have heY : b - (b - i.2.val) = i.2.val := by omega
  rw [heX] at hxi
  rw [heY] at hyi
  calc
    _ = (x ^ a * (x⁻¹) ^ (a - i.1.val)) * (y ^ b * (y⁻¹) ^ (b - i.2.val)) *
        ((P.coeff i.2.val).coeff i.1.val : R) := by simp only [one_div]; ring
    _ = _ := by rw [hxi, hyi]; ring

end PaperP1.BivariateEvaluation
