module

public import PaperP1.Analysis.GraphTangentSmooth
public import PaperP1.Analysis.IteratedGraphDerivative
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Constructed local normalized graph pieces

At every actual curve point with nonzero second partial, the ODE constructs
an open graph chart whose parameter is exactly its first coordinate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalNormalizedGraphPiece

open Set Filter MvPolynomial GraphTangentEvaluation GraphTangentSmooth PolynomialVelocitySmooth
open scoped Topology ContDiff

structure Piece (P : MvPolynomial (Fin 2) ℝ) where
  left : ℝ
  right : ℝ
  ordered : left < right
  path : Fin 2 → ℝ → ℝ
  trajectory : Trajectory P path (Ioo left right)
  equation : ∀ t ∈ Ioo left right, eval (fun i ↦ path i t) P = 0
  first_coordinate : ∀ t ∈ Ioo left right, path 0 t = t

theorem exists_trajectory (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hA : eval z (pderiv 1 P) ≠ 0) (t₀ : ℝ) :
    ∃ φ : Fin 2 → ℝ → ℝ, (fun i ↦ φ i t₀) = z ∧
      ∃ a b : ℝ, t₀ ∈ Ioo a b ∧ Trajectory P φ (Ioo a b) := by
  obtain ⟨α, hα, ε, hε, hder⟩ := (contDiffAt_velocity P z hA 1)
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hc : ContinuousAt α t₀ := (hder t₀ ht₀).continuousAt
  have hAcont : ContinuousAt (fun t ↦ eval (α t) (pderiv 1 P)) t₀ :=
    (contDiff_eval (pderiv 1 P) 1).continuous.continuousAt.comp hc
  have hA₀ : eval (α t₀) (pderiv 1 P) ≠ 0 := by rw [hα]; exact hA
  have hn : {t : ℝ | t ∈ Ioo (t₀ - ε) (t₀ + ε) ∧ eval (α t) (pderiv 1 P) ≠ 0} ∈ 𝓝 t₀ :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds ht₀) (hAcont.eventually_ne hA₀)
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  refine ⟨(fun i t ↦ α t i), hα, a, b, hab, ?_, ?_⟩
  · exact fun t ht ↦ (hsub ht).2
  · intro t ht i
    exact (hasDerivAt_pi.mp (hder t (hsub ht).1)) i

theorem first_coordinate_identity (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : Trajectory P φ (Ioo a b)) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (hinit : φ 0 t₀ = t₀) : ∀ t ∈ Ioo a b, φ 0 t = t := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (φ 0) 1 t := by
    simpa [velocity] using hφ.2 t ht 0
  have hz (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun u ↦ φ 0 u - u) 0 t := by
    have hid : HasDerivAt (fun u : ℝ ↦ u) (1 : ℝ) t := hasDerivAt_id' t
    have hsub : HasDerivAt (fun u ↦ φ 0 u - u) (1 - 1) t :=
      HasDerivAt.fun_sub (hd t ht) hid
    simpa only [sub_self] using hsub
  have hdiff : DifferentiableOn ℝ (fun u ↦ φ 0 u - u) (Ioo a b) :=
    fun t ht ↦ (hz t ht).differentiableAt.differentiableWithinAt
  have hzero : EqOn (deriv (fun u ↦ φ 0 u - u)) 0 (Ioo a b) :=
    fun t ht ↦ (hz t ht).deriv
  intro t ht
  have hh := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero ht ht₀
  change φ 0 t - t = φ 0 t₀ - t₀ at hh
  rw [hinit] at hh
  linarith

theorem exists_piece (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hA : eval z (pderiv 1 P) ≠ 0) :
    ∃ r : Piece P, z 0 ∈ Ioo r.left r.right ∧ (fun i ↦ r.path i (z 0)) = z := by
  obtain ⟨φ, hpoint, a, b, ht₀, hφ⟩ := exists_trajectory P z hA (z 0)
  have hinit : φ 0 (z 0) = z 0 := congrFun hpoint 0
  have heq : ∀ t ∈ Ioo a b, eval (fun i ↦ φ i t) P = 0 := by
    intro t ht
    rw [equation_constant P φ a b hφ t (z 0) ht ht₀, hpoint]
    exact hzero
  exact ⟨⟨a, b, ht₀.1.trans ht₀.2, φ, hφ, heq,
    first_coordinate_identity P φ a b hφ (z 0) ht₀ hinit⟩, ht₀, hpoint⟩

theorem exists_smooth_piece_with_derivatives (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hA : eval z (pderiv 1 P) ≠ 0) :
    ∃ r : Piece P, z 0 ∈ Ioo r.left r.right ∧ (fun i ↦ r.path i (z 0)) = z ∧
      (∀ i, ContDiffOn ℝ ∞ (r.path i) (Ioo r.left r.right)) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, ∀ j : ℕ, 1 ≤ j →
        ∃ N : MvPolynomial (Fin 2) ℝ,
          N.totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * j ∧
          EqOn (iteratedDeriv j (fun t ↦ eval (fun i ↦ r.path i t) Q))
            (fun t ↦ eval (fun i ↦ r.path i t) N /
              (eval (fun i ↦ r.path i t) (pderiv 1 P)) ^ (2 * j - 1))
            (Ioo r.left r.right) := by
  obtain ⟨r, hmem, hpoint⟩ := exists_piece P z hzero hA
  refine ⟨r, hmem, hpoint, contDiffOn_trajectory P r.path _ isOpen_Ioo r.trajectory, ?_⟩
  intro Q j hj
  exact IteratedGraphDerivative.positive_order P Q r.path _ isOpen_Ioo r.trajectory j hj

end PaperP1.LocalNormalizedGraphPiece
