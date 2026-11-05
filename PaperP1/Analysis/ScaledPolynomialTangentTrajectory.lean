module

public import PaperP1.Analysis.PolynomialTangentTrajectory
public import PaperP1.Analysis.ScaledWronskianTransformation
public import PaperP1.Analysis.LocalAffineDerivativeFormula

/-! # Actual smoothly scaled polynomial tangent trajectories

Their actual Wronskians are the evaluated formal tangent Wronskians multiplied
by the exact nonzero scale power. Affine reparametrization is also explicit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledPolynomialTangentTrajectory

open MvPolynomial Set PolynomialTangentDegree PolynomialEvaluationDerivative
open scoped ContDiff

def Trajectory (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ i, HasDerivAt (φ i)
    (a t * PolynomialTangentTrajectory.velocity P (fun j ↦ φ j t) i) t

theorem directional_scaled (P Q : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) (a : ℝ) :
    directional z (fun i ↦ a * PolynomialTangentTrajectory.velocity P z i) Q =
      a * eval z (tangent P Q) := by
  simp only [directional, Fin.sum_univ_two, PolynomialTangentTrajectory.velocity, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, tangent, map_sub, map_mul]
  ring

theorem hasDerivAt_evaluation (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hφ : Trajectory P a φ s) (t : ℝ) (ht : t ∈ s) :
    HasDerivAt (fun u ↦ eval (fun j ↦ φ j u) Q)
      (a t * eval (fun j ↦ φ j t) (tangent P Q)) t :=
  (PolynomialEvaluationDerivative.hasDerivAt_eval Q φ
    (fun i ↦ a t * PolynomialTangentTrajectory.velocity P (fun j ↦ φ j t) i) t (hφ t ht)).congr_deriv
      (directional_scaled P Q _ (a t))

theorem deriv_evaluation (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hφ : Trajectory P a φ s) (t : ℝ) (ht : t ∈ s) :
    deriv (fun u ↦ eval (fun j ↦ φ j u) Q) t =
      a t * eval (fun j ↦ φ j t) (tangent P Q) :=
  (hasDerivAt_evaluation P a Q φ s hφ t ht).deriv

theorem wronskian_evaluation (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s)
    (hφ : Trajectory P a φ s) (n : ℕ) (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (t : ℝ) (ht : t ∈ s) :
    AnalyticWronskianProduct.wronskian n (fun i u ↦ eval (fun j ↦ φ j u) (f i)) t =
      (a t) ^ (∑ i : Fin n, i.val) *
        eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) := by
  let F : Fin n → ℕ → ℝ → ℝ :=
    fun j k u ↦ eval (fun i ↦ φ i u) ((tangent P)^[k] (f j))
  have hF : ∀ j k, ∀ u ∈ s, HasDerivAt (F j k) (a u * F j (k + 1) u) u := by
    intro j k u hu
    simpa only [F, Function.iterate_succ_apply'] using
      hasDerivAt_evaluation P a ((tangent P)^[k] (f j)) φ s hφ u hu
  have hw := ScaledWronskianTransformation.wronskian_factor n a F s hs ha hF t ht
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) ℝ) :=
    fun i j ↦ (tangent P)^[i.val] (f j)
  have hdet : (ScaledWronskianTransformation.chainMatrix n F t).det =
      eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) := by
    change (ScaledWronskianTransformation.chainMatrix n F t).det = eval (fun j ↦ φ j t) A.det
    rw [(eval (fun j ↦ φ j t)).map_det A]
    rfl
  rw [hdet] at hw
  simpa only [F, Function.iterate_zero_apply] using hw

theorem wronskian_ne_zero (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s)
    (hφ : Trajectory P a φ s) (n : ℕ) (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (t : ℝ) (ht : t ∈ s) (hscale : a t ≠ 0)
    (hW : eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) ≠ 0) :
    AnalyticWronskianProduct.wronskian n (fun i u ↦ eval (fun j ↦ φ j u) (f i)) t ≠ 0 := by
  rw [wronskian_evaluation P a φ s hs ha hφ n f t ht]
  exact mul_ne_zero (pow_ne_zero _ hscale) hW

theorem velocity_contDiffOn (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ) (n : WithTop ℕ∞)
    (s : Set ℝ) (φ : Fin 2 → ℝ → ℝ) (ha : ContDiffOn ℝ n a s)
    (hφ : ∀ i, ContDiffOn ℝ n (φ i) s) :
    ∀ i, ContDiffOn ℝ n (fun t ↦ a t * PolynomialTangentTrajectory.velocity P (fun j ↦ φ j t) i) s :=
  fun i ↦ ha.mul (PolynomialTangentTrajectory.velocity_contDiffOn P n s φ hφ i)

theorem contDiffOn_trajectory (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s)
    (hφ : Trajectory P a φ s) : ∀ i, ContDiffOn ℝ ∞ (φ i) s := by
  have hfinite : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (φ i) s := by
    intro n
    induction n with
    | zero =>
      intro i
      exact contDiffOn_zero.mpr (HasDerivAt.continuousOn (fun t ht ↦ hφ t ht i))
    | succ n ih =>
      intro i
      have hd : DifferentiableOn ℝ (φ i) s := fun t ht ↦
        (hφ t ht i).differentiableAt.differentiableWithinAt
      have han : ContDiffOn ℝ n a s := ha.of_le (by simp)
      have hv := velocity_contDiffOn P a n s φ han ih i
      have hder : ContDiffOn ℝ n (deriv (φ i)) s := hv.congr (fun t ht ↦ (hφ t ht i).deriv)
      have hh := (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : ℕ∞ω)) hs).mpr ⟨hd, by simp, hder⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hh
  intro i
  exact contDiffOn_infty.mpr (fun n ↦ hfinite n i)

theorem affine_trajectory (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hφ : Trajectory P a φ s)
    (u c : ℝ) (v : Set ℝ) (hmap : MapsTo (LocalAffineDerivativeFormula.parameter u c) v s) :
    Trajectory P (fun t ↦ c * a (LocalAffineDerivativeFormula.parameter u c t))
      (fun i t ↦ φ i (LocalAffineDerivativeFormula.parameter u c t)) v := by
  intro t ht i
  have hh := (hφ _ (hmap ht) i).comp t (LocalAffineDerivativeFormula.hasDerivAt_parameter u c t)
  apply hh.congr_deriv
  ring

end PaperP1.ScaledPolynomialTangentTrajectory
