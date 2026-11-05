module

public import PaperP1.Arithmetic.NonGeometricPlanePointBound

/-! # Coefficient-uniform integer-grid bounds for linear plane equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearPlaneGridBound

open Polynomial Finset PaperP1.CurveIntegerFibres PaperP1.BivariateCurveDegreeTransport

variable {K : Type*} [Field K] [CharZero K]

theorem offsetBox_card (B : ℕ) : (offsetBox B).card = 2 * B + 1 := by
  rw [offsetBox, Int.card_Icc]
  omega

theorem grid_card_of_outer_positive (P : K[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (B : ℕ) :
    (PlaneCurvePointCount.grid P B).card ≤ (offsetBox B).card * P.natDegree := by
  classical
  have hf (x : ℤ) :
      ((offsetBox B).filter (fun y : ℤ ↦ P.evalEval (x : K) (y : K) = 0)).card ≤ P.natDegree := by
    let T := (offsetBox B).filter (fun y : ℤ ↦ P.evalEval (x : K) (y : K) = 0)
    have he : (T.image (fun y : ℤ ↦ (y : K))).card = T.card :=
      Finset.card_image_of_injective T Int.cast_injective
    have hroot : ∀ y ∈ T.image (fun y : ℤ ↦ (y : K)), P.evalEval (x : K) y = 0 := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hz).2
    have hb := RationalCurveCriticalPoints.fibre_card P hP hdeg (x : K)
      (T.image (fun y : ℤ ↦ (y : K))) hroot
    rwa [he] at hb
  calc
    (PlaneCurvePointCount.grid P B).card =
        ∑ x ∈ offsetBox B, ((offsetBox B).filter
          (fun y : ℤ ↦ P.evalEval (x : K) (y : K) = 0)).card := by
      simp only [PlaneCurvePointCount.grid, card_eq_sum_ones, sum_filter, Finset.sum_product]
    _ ≤ ∑ _x ∈ offsetBox B, P.natDegree := sum_le_sum (fun x _hx ↦ hf x)
    _ = _ := by simp

omit [CharZero K] in
theorem grid_card_swap (P : K[X][X]) (B : ℕ) :
    (PlaneCurvePointCount.grid (Bivariate.swap P) B).card =
      (PlaneCurvePointCount.grid P B).card := by
  classical
  simp only [PlaneCurvePointCount.grid, card_eq_sum_ones, sum_filter,
    Finset.sum_product, swap_evaluation]
  exact Finset.sum_comm

theorem linear_grid_card (P : K[X][X]) (hP : Irreducible P)
    (hdegree : PlaneCurvePointCount.degree P = 1) (B : ℕ) :
    (PlaneCurvePointCount.grid P B).card ≤ 2 * B + 1 := by
  have hb (Q : K[X][X]) (hQ : Irreducible Q) (hd : PlaneCurvePointCount.degree Q = 1)
      (ho : 0 < Q.natDegree) : (PlaneCurvePointCount.grid Q B).card ≤ 2 * B + 1 := by
    have hout : Q.natDegree ≤ 1 := (BivariateResultantDegree.outer_degree_le Q).trans hd.le
    calc
      _ ≤ (offsetBox B).card * Q.natDegree := grid_card_of_outer_positive Q hQ ho B
      _ ≤ (offsetBox B).card * 1 := Nat.mul_le_mul_left _ hout
      _ = _ := by rw [mul_one, offsetBox_card]
  by_cases ho : 0 < P.natDegree
  · exact hb P hP hdegree ho
  · have hp := degree_le_partial_sum P
    have hswap : 0 < (Bivariate.swap P).natDegree := by omega
    rw [← grid_card_swap]
    exact hb (Bivariate.swap P) ((MulEquiv.irreducible_iff Bivariate.swap).mpr hP)
      ((degree_swap P).trans hdegree) hswap

theorem linear_real_grid_card (P : K[X][X]) (hP : Irreducible P)
    (hdegree : PlaneCurvePointCount.degree P = 1) (H : ℝ) (hH : 2 < H) :
    ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ 3 * H := by
  have hb := linear_grid_card P hP hdegree ⌊H⌋₊
  have hbr : ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ 2 * (⌊H⌋₊ : ℝ) + 1 := by
    exact_mod_cast hb
  have hf : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith)
  linarith

end PaperP1.LinearPlaneGridBound
