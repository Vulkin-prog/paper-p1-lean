module

public import PaperP1.Analysis.PolynomialEvaluationDerivative
public import PaperP1.Algebra.RationalTangentNumerator
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual evaluation derivatives in a normalized polynomial graph chart

The first coordinate has derivative one; the second follows the curve slope.
Every denominator is required to be nonzero on the actual open parameter set.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphTangentEvaluation

open MvPolynomial Set PolynomialTangentDegree PolynomialEvaluationDerivative

def velocity (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 1 else -eval z (pderiv 0 P) / eval z (pderiv 1 P)

def Trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, eval (fun j ↦ φ j t) (pderiv 1 P) ≠ 0) ∧
    ∀ t ∈ s, ∀ i, HasDerivAt (φ i) (velocity P (fun j ↦ φ j t) i) t

theorem directional_normalized (P Q : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hA : eval z (pderiv 1 P) ≠ 0) :
    directional z (velocity P z) Q = eval z (tangent P Q) / eval z (pderiv 1 P) := by
  simp only [directional, Fin.sum_univ_two, velocity, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, tangent, map_sub, map_mul]
  field_simp [hA]
  ring

theorem hasDerivAt_evaluation (P Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : Trajectory P φ s) (t : ℝ) (ht : t ∈ s) :
    HasDerivAt (fun u ↦ eval (fun j ↦ φ j u) Q)
      (eval (fun j ↦ φ j t) (tangent P Q) / eval (fun j ↦ φ j t) (pderiv 1 P)) t :=
  (PolynomialEvaluationDerivative.hasDerivAt_eval Q φ (velocity P (fun j ↦ φ j t)) t (hφ.2 t ht)).congr_deriv
    (directional_normalized P Q _ (hφ.1 t ht))

theorem deriv_evaluation (P Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : Trajectory P φ s) (t : ℝ) (ht : t ∈ s) :
    deriv (fun u ↦ eval (fun j ↦ φ j u) Q) t =
      eval (fun j ↦ φ j t) (tangent P Q) / eval (fun j ↦ φ j t) (pderiv 1 P) :=
  (hasDerivAt_evaluation P Q φ s hφ t ht).deriv

theorem equation_constant (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : Trajectory P φ (Ioo a b))
    (t u : ℝ) (ht : t ∈ Ioo a b) (hu : u ∈ Ioo a b) :
    eval (fun j ↦ φ j t) P = eval (fun j ↦ φ j u) P := by
  have hd : DifferentiableOn ℝ (fun v ↦ eval (fun j ↦ φ j v) P) (Ioo a b) :=
    fun v hv ↦ (hasDerivAt_evaluation P P φ (Ioo a b) hφ v hv).differentiableAt.differentiableWithinAt
  have hz : EqOn (deriv (fun v ↦ eval (fun j ↦ φ j v) P)) 0 (Ioo a b) := by
    intro v hv
    rw [deriv_evaluation P P φ (Ioo a b) hφ v hv, tangent_self, map_zero, zero_div]
    rfl
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hd hz ht hu

end PaperP1.GraphTangentEvaluation
