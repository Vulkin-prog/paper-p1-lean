module

public import PaperP1.Analysis.PolynomialEvaluationDerivative
public import PaperP1.Analysis.AnalyticWronskianProduct
public import PaperP1.Algebra.PolynomialTangentWronskian
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic.FinCases

/-! # Actual tangent trajectories and their polynomial Wronskians

The differential equation implies smoothness; it is not an additional premise.
Iterated real derivatives agree with evaluated formal tangent derivatives.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialTangentTrajectory

open MvPolynomial Finset Set PolynomialTangentDegree PolynomialEvaluationDerivative
open scoped ContDiff

def velocity (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then eval z (pderiv 1 P) else -eval z (pderiv 0 P)

def Trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ i, HasDerivAt (φ i) (velocity P (fun j ↦ φ j t) i) t

theorem directional_tangent (P Q : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    directional z (velocity P z) Q = eval z (tangent P Q) := by
  simp only [directional, Fin.sum_univ_two, velocity, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, tangent, map_sub, map_mul]
  ring

theorem hasDerivAt_evaluation (P Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : Trajectory P φ s) (t : ℝ) (ht : t ∈ s) :
    HasDerivAt (fun u ↦ eval (fun j ↦ φ j u) Q)
      (eval (fun j ↦ φ j t) (tangent P Q)) t := by
  simpa only [directional_tangent] using
    PolynomialEvaluationDerivative.hasDerivAt_eval Q φ (velocity P (fun j ↦ φ j t)) t (hφ t ht)

theorem deriv_evaluation (P Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : Trajectory P φ s) (t : ℝ) (ht : t ∈ s) :
    deriv (fun u ↦ eval (fun j ↦ φ j u) Q) t = eval (fun j ↦ φ j t) (tangent P Q) :=
  (hasDerivAt_evaluation P Q φ s hφ t ht).deriv

theorem iterated_evaluation (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s) (n : ℕ)
    (Q : MvPolynomial (Fin 2) ℝ) :
    EqOn (iteratedDeriv n (fun u ↦ eval (fun j ↦ φ j u) Q))
      (fun t ↦ eval (fun j ↦ φ j t) ((tangent P)^[n] Q)) s := by
  induction n generalizing Q with
  | zero => intro t _ht; rfl
  | succ n ih =>
    have he := (ih Q).deriv hs
    intro t ht
    calc
      _ = deriv (iteratedDeriv n (fun u ↦ eval (fun j ↦ φ j u) Q)) t := by rw [iteratedDeriv_succ]
      _ = deriv (fun u ↦ eval (fun j ↦ φ j u) ((tangent P)^[n] Q)) t := he ht
      _ = eval (fun j ↦ φ j t) (tangent P ((tangent P)^[n] Q)) :=
        deriv_evaluation P _ φ s hφ t ht
      _ = _ := by rw [Function.iterate_succ_apply']

theorem wronskian_evaluation (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s) (n : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (t : ℝ) (ht : t ∈ s) :
    AnalyticWronskianProduct.wronskian n (fun i u ↦ eval (fun j ↦ φ j u) (f i)) t =
      eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) := by
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) ℝ) :=
    fun i j ↦ (tangent P)^[i.val] (f j)
  change (AnalyticWronskianProduct.jetMatrix n (fun i u ↦ eval (fun j ↦ φ j u) (f i)) t).det =
    eval (fun j ↦ φ j t) A.det
  rw [(eval (fun j ↦ φ j t)).map_det A]
  congr 1
  ext i j
  exact iterated_evaluation P φ s hs hφ i.val (f j) ht

theorem velocity_contDiffOn (P : MvPolynomial (Fin 2) ℝ) (n : WithTop ℕ∞)
    (s : Set ℝ) (φ : Fin 2 → ℝ → ℝ) (hφ : ∀ i, ContDiffOn ℝ n (φ i) s) :
    ∀ i, ContDiffOn ℝ n (fun t ↦ velocity P (fun j ↦ φ j t) i) s := by
  intro i
  fin_cases i
  · simpa [velocity] using contDiffOn_eval (pderiv 1 P) n s φ hφ
  · simpa [velocity] using
      (contDiffOn_eval (pderiv 0 P) n s φ hφ).neg

theorem contDiffOn_trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s) :
    ∀ i, ContDiffOn ℝ ∞ (φ i) s := by
  have hfinite : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (φ i) s := by
    intro n
    induction n with
    | zero =>
      intro i
      exact contDiffOn_zero.mpr (HasDerivAt.continuousOn (fun t ht ↦ hφ t ht i))
    | succ n ih =>
      intro i
      have hd : DifferentiableOn ℝ (φ i) s := fun t ht ↦ (hφ t ht i).differentiableAt.differentiableWithinAt
      have hv := velocity_contDiffOn P n s φ ih i
      have hder : ContDiffOn ℝ n (deriv (φ i)) s := hv.congr (fun t ht ↦ (hφ t ht i).deriv)
      have hh := (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : ℕ∞ω)) hs).mpr ⟨hd, by simp, hder⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hh
  intro i
  exact contDiffOn_infty.mpr (fun n ↦ hfinite n i)

end PaperP1.PolynomialTangentTrajectory
