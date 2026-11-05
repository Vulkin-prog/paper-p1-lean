module

public import PaperP1.Analysis.GraphTangentEvaluation
public import PaperP1.Analysis.PolynomialVelocitySmooth
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth normalized graph fields and actual trajectories

Denominator nonvanishing is used locally and on the actual parameter domain.
The smoothness of the trajectory is a consequence of its differential equation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphTangentSmooth

open MvPolynomial Set GraphTangentEvaluation PolynomialVelocitySmooth
open scoped ContDiff

theorem contDiffAt_velocity (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hA : eval z (pderiv 1 P) ≠ 0) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (velocity P) z := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · simpa [velocity] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : Fin 2 → ℝ ↦ (1 : ℝ)) z)
  · simpa [velocity] using
      ((contDiff_eval (pderiv 0 P) n).contDiffAt.neg.fun_div
        (contDiff_eval (pderiv 1 P) n).contDiffAt hA)

theorem velocity_contDiffOn (P : MvPolynomial (Fin 2) ℝ) (n : WithTop ℕ∞)
    (s : Set ℝ) (φ : Fin 2 → ℝ → ℝ)
    (hφ : ∀ i, ContDiffOn ℝ n (φ i) s)
    (hA : ∀ t ∈ s, eval (fun j ↦ φ j t) (pderiv 1 P) ≠ 0) :
    ∀ i, ContDiffOn ℝ n (fun t ↦ velocity P (fun j ↦ φ j t) i) s := by
  intro i
  fin_cases i
  · simpa [velocity] using
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ ↦ (1 : ℝ)) s)
  · simpa [velocity] using
      (PolynomialEvaluationDerivative.contDiffOn_eval (pderiv 0 P) n s φ hφ).neg.fun_div
        (PolynomialEvaluationDerivative.contDiffOn_eval (pderiv 1 P) n s φ hφ) hA

theorem contDiffOn_trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s) :
    ∀ i, ContDiffOn ℝ ∞ (φ i) s := by
  have hfinite : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (φ i) s := by
    intro n
    induction n with
    | zero =>
      intro i
      exact contDiffOn_zero.mpr (HasDerivAt.continuousOn (fun t ht ↦ hφ.2 t ht i))
    | succ n ih =>
      intro i
      have hd : DifferentiableOn ℝ (φ i) s := fun t ht ↦
        (hφ.2 t ht i).differentiableAt.differentiableWithinAt
      have hv := velocity_contDiffOn P n s φ ih hφ.1 i
      have hder : ContDiffOn ℝ n (deriv (φ i)) s := hv.congr (fun t ht ↦ (hφ.2 t ht i).deriv)
      have hh := (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : ℕ∞ω)) hs).mpr ⟨hd, by simp, hder⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hh
  intro i
  exact contDiffOn_infty.mpr (fun n ↦ hfinite n i)

end PaperP1.GraphTangentSmooth
