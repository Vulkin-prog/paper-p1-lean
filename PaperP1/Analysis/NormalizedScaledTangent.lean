module

public import PaperP1.Analysis.ScaledPolynomialTangentTrajectory
public import PaperP1.Analysis.BothGraphDerivativeFormulas
public import PaperP1.Analysis.GraphTangentSmooth

/-! # Actual normalized graph trajectories as nonzero smooth tangent rescalings -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedScaledTangent

open MvPolynomial Set PlaneCoordinateSwap
open scoped ContDiff

def firstScale (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (t : ℝ) : ℝ :=
  (eval (fun j ↦ φ j t) (pderiv 1 P))⁻¹

def secondScale (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (t : ℝ) : ℝ :=
  -(eval (fun j ↦ φ j t) (pderiv 0 P))⁻¹

theorem first_trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hφ : GraphTangentEvaluation.Trajectory P φ s) :
    ScaledPolynomialTangentTrajectory.Trajectory P (firstScale P φ) φ s := by
  intro t ht i
  apply (hφ.2 t ht i).congr_deriv
  fin_cases i
  · change (1 : ℝ) = (eval (fun j ↦ φ j t) (pderiv 1 P))⁻¹ * eval (fun j ↦ φ j t) (pderiv 1 P)
    exact (inv_mul_cancel₀ (hφ.1 t ht)).symm
  · change -eval (fun j ↦ φ j t) (pderiv 0 P) / eval (fun j ↦ φ j t) (pderiv 1 P) =
      (eval (fun j ↦ φ j t) (pderiv 1 P))⁻¹ * (-eval (fun j ↦ φ j t) (pderiv 0 P))
    rw [div_eq_mul_inv, mul_comm]

theorem second_trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) :
    ScaledPolynomialTangentTrajectory.Trajectory P (secondScale P φ) φ s := by
  intro t ht i
  apply (hφ.2 t ht i).congr_deriv
  fin_cases i
  · change -eval (fun j ↦ φ j t) (pderiv 1 P) / eval (fun j ↦ φ j t) (pderiv 0 P) =
      (-(eval (fun j ↦ φ j t) (pderiv 0 P))⁻¹) * eval (fun j ↦ φ j t) (pderiv 1 P)
    rw [div_eq_mul_inv]
    ring
  · change (1 : ℝ) = (-(eval (fun j ↦ φ j t) (pderiv 0 P))⁻¹) *
      (-eval (fun j ↦ φ j t) (pderiv 0 P))
    rw [neg_mul_neg]
    exact (inv_mul_cancel₀ (hφ.1 t ht)).symm

theorem second_smooth (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) :
    ∀ i, ContDiffOn ℝ ∞ (φ i) s := by
  have hnew := BothGraphDerivativeFormulas.transpose_trajectory P φ s hφ
  have hsm := GraphTangentSmooth.contDiffOn_trajectory (polynomial P) (fun i t ↦ φ (index i) t) s hs hnew
  intro i
  simpa only [index_twice] using hsm (index i)

theorem firstScale_smooth (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hφ : GraphTangentEvaluation.Trajectory P φ s) :
    ContDiffOn ℝ ∞ (firstScale P φ) s := by
  have hsm := GraphTangentSmooth.contDiffOn_trajectory P φ s hs hφ
  change ContDiffOn ℝ ∞ (fun t ↦ (eval (fun j ↦ φ j t) (pderiv 1 P))⁻¹) s
  exact (PolynomialEvaluationDerivative.contDiffOn_eval (pderiv 1 P) ∞ s φ hsm).fun_inv hφ.1

theorem secondScale_smooth (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) :
    ContDiffOn ℝ ∞ (secondScale P φ) s := by
  have hsm := second_smooth P φ s hs hφ
  change ContDiffOn ℝ ∞ (fun t ↦ -(eval (fun j ↦ φ j t) (pderiv 0 P))⁻¹) s
  exact ((PolynomialEvaluationDerivative.contDiffOn_eval (pderiv 0 P) ∞ s φ hsm).fun_inv hφ.1).neg

theorem firstScale_ne_zero (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hφ : GraphTangentEvaluation.Trajectory P φ s) (t : ℝ) (ht : t ∈ s) : firstScale P φ t ≠ 0 :=
  inv_ne_zero (hφ.1 t ht)

theorem secondScale_ne_zero (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) (t : ℝ) (ht : t ∈ s) : secondScale P φ t ≠ 0 :=
  neg_ne_zero.mpr (inv_ne_zero (hφ.1 t ht))

theorem first_wronskian_ne_zero (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : GraphTangentEvaluation.Trajectory P φ s)
    (n : ℕ) (f : Fin n → MvPolynomial (Fin 2) ℝ) (t : ℝ) (ht : t ∈ s)
    (hW : eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) ≠ 0) :
    AnalyticWronskianProduct.wronskian n (fun i u ↦ eval (fun j ↦ φ j u) (f i)) t ≠ 0 :=
  ScaledPolynomialTangentTrajectory.wronskian_ne_zero P (firstScale P φ) φ s hs
    (firstScale_smooth P φ s hs hφ) (first_trajectory P φ s hφ) n f t ht
    (firstScale_ne_zero P φ s hφ t ht) hW

theorem second_wronskian_ne_zero (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s)
    (n : ℕ) (f : Fin n → MvPolynomial (Fin 2) ℝ) (t : ℝ) (ht : t ∈ s)
    (hW : eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) ≠ 0) :
    AnalyticWronskianProduct.wronskian n (fun i u ↦ eval (fun j ↦ φ j u) (f i)) t ≠ 0 :=
  ScaledPolynomialTangentTrajectory.wronskian_ne_zero P (secondScale P φ) φ s hs
    (secondScale_smooth P φ s hs hφ) (second_trajectory P φ s hφ) n f t ht
    (secondScale_ne_zero P φ s hφ t ht) hW

end PaperP1.NormalizedScaledTangent
