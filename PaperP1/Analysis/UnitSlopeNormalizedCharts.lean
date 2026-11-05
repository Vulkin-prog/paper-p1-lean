module

public import PaperP1.Analysis.ControlledNormalizedCharts
public import PaperP1.Analysis.GraphSlopeControl

/-! # Constructed local controlled graphs with unit slope and unit distance bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitSlopeNormalizedCharts

open MvPolynomial Set PlaneCoordinateSwap
open scoped ContDiff

structure Piece (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) where
  independent : Fin 2
  left : ℝ
  right : ℝ
  ordered : left < right
  path : Fin 2 → ℝ → ℝ
  normalized_coordinate : ∀ t ∈ Ioo left right, path independent t = t
  trajectory : if independent = 0 then GraphTangentEvaluation.Trajectory P path (Ioo left right)
    else TransposedNormalizedGraphPiece.Trajectory P path (Ioo left right)
  smooth : ∀ i, ContDiffOn ℝ ∞ (path i) (Ioo left right)
  equation : ∀ t ∈ Ioo left right, eval (fun j ↦ path j t) P = 0
  avoids : ∀ t ∈ Ioo left right, (fun j ↦ path j t) ∉ GraphControlExceptions.points P r
  derivative_signs : ∀ n ≤ r, ∀ t ∈ Ioo left right, ∀ u ∈ Ioo left right,
    SignType.sign (iteratedDeriv n (path (index independent)) t) =
      SignType.sign (iteratedDeriv n (path (index independent)) u)
  slope : ∀ t ∈ Ioo left right, |deriv (path (index independent)) t| ≤ 1
  distance : ∀ t ∈ Ioo left right, ∀ u ∈ Ioo left right,
    |path (index independent) t - path (index independent) u| ≤ |t - u|

def of_first (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : LocalNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo q.left q.right)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (q.path i) (Ioo q.left q.right))
    (havoid : ∀ t ∈ Ioo q.left q.right, (fun j ↦ q.path j t) ∉ GraphControlExceptions.points P r)
    (hinit : |eval (fun j ↦ q.path j t₀) (pderiv 0 P)| ≤
      |eval (fun j ↦ q.path j t₀) (pderiv 1 P)|) : Piece P r where
  independent := 0
  left := q.left
  right := q.right
  ordered := q.ordered
  path := q.path
  normalized_coordinate := q.first_coordinate
  trajectory := by simpa only [ite_true] using q.trajectory
  smooth := hsmooth
  equation := q.equation
  avoids := havoid
  derivative_signs := by
    intro n hn t ht u hu
    simpa only [index_zero] using GraphControlledDerivatives.first_all_orders_sign P r q.path
      (Ioo q.left q.right) isOpen_Ioo isPreconnected_Ioo q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, havoid v hv⟩) n hn t u ht hu
  slope := by
    intro t ht
    simpa only [index_zero] using GraphSlopeControl.first_abs_deriv P r q.path
      (Ioo q.left q.right) isPreconnected_Ioo q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, havoid v hv⟩) t₀ ht₀ hinit t ht
  distance := by
    intro t ht u hu
    simpa only [index_zero] using GraphSlopeControl.first_distance P r q.path q.left q.right q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, havoid v hv⟩) t₀ ht₀ hinit t u ht hu

def of_second (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo q.left q.right)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (q.path i) (Ioo q.left q.right))
    (havoid : ∀ t ∈ Ioo q.left q.right, (fun j ↦ q.path j t) ∉ GraphControlExceptions.points P r)
    (hinit : |eval (fun j ↦ q.path j t₀) (pderiv 1 P)| ≤
      |eval (fun j ↦ q.path j t₀) (pderiv 0 P)|) : Piece P r where
  independent := 1
  left := q.left
  right := q.right
  ordered := q.ordered
  path := q.path
  normalized_coordinate := q.second_coordinate
  trajectory := by simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using q.trajectory
  smooth := hsmooth
  equation := q.equation
  avoids := havoid
  derivative_signs := by
    intro n hn t ht u hu
    simpa only [index_one] using GraphControlledDerivatives.second_all_orders_sign P r q.path
      (Ioo q.left q.right) isOpen_Ioo isPreconnected_Ioo q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, havoid v hv⟩) n hn t u ht hu
  slope := by
    intro t ht
    simpa only [index_one] using GraphSlopeControl.second_abs_deriv P r q.path
      (Ioo q.left q.right) isPreconnected_Ioo q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, havoid v hv⟩) t₀ ht₀ hinit t ht
  distance := by
    intro t ht u hu
    simpa only [index_one] using GraphSlopeControl.second_distance P r q.path q.left q.right q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, havoid v hv⟩) t₀ ht₀ hinit t u ht hu

theorem exists_at_nonexceptional (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hnot : z ∉ GraphControlExceptions.points P r) :
    ∃ q : Piece P r, z q.independent ∈ Ioo q.left q.right ∧
      (fun j ↦ q.path j (z q.independent)) = z := by
  classical
  obtain ⟨E, hE, _hcard⟩ := GraphControlExceptions.exists_finset P hP hD r
  have hnotE : z ∉ E := fun hz ↦ hnot ((hE z).mp hz)
  have hgradient := GraphControlExceptions.gradient_nonzero P hD r z hzero hnot
  by_cases hcmp : |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|
  · have hA : eval z (pderiv 1 P) ≠ 0 := by
      intro hz
      have ha : eval z (pderiv 0 P) = 0 := abs_eq_zero.mp
        (le_antisymm (by simpa only [hz, abs_zero] using hcmp) (abs_nonneg _))
      obtain ⟨i, hi⟩ := hgradient
      fin_cases i
      · exact hi ha
      · exact hi hz
    obtain ⟨q, hmem, hpoint, hsmooth, havoid⟩ :=
      NormalizedGraphFiniteAvoidance.exists_first P z hzero hA E hnotE
    have hnon : ∀ t ∈ Ioo q.left q.right, (fun j ↦ q.path j t) ∉ GraphControlExceptions.points P r :=
      fun t ht hz ↦ havoid t ht ((hE _).mpr hz)
    have hinit : |eval (fun j ↦ q.path j (z 0)) (pderiv 0 P)| ≤
        |eval (fun j ↦ q.path j (z 0)) (pderiv 1 P)| := by rw [hpoint]; exact hcmp
    exact ⟨of_first P r q (z 0) hmem hsmooth hnon hinit, hmem, hpoint⟩
  · have hA : eval z (pderiv 0 P) ≠ 0 := by
      intro hz
      apply hcmp
      rw [hz, abs_zero]
      exact abs_nonneg _
    obtain ⟨q, hmem, hpoint, hsmooth, havoid⟩ :=
      NormalizedGraphFiniteAvoidance.exists_second P z hzero hA E hnotE
    have hnon : ∀ t ∈ Ioo q.left q.right, (fun j ↦ q.path j t) ∉ GraphControlExceptions.points P r :=
      fun t ht hz ↦ havoid t ht ((hE _).mpr hz)
    have hinit : |eval (fun j ↦ q.path j (z 1)) (pderiv 1 P)| ≤
        |eval (fun j ↦ q.path j (z 1)) (pderiv 0 P)| := by
      rw [hpoint]
      exact le_of_lt (lt_of_not_ge hcmp)
    exact ⟨of_second P r q (z 1) hmem hsmooth hnon hinit, hmem, hpoint⟩

theorem exists_control_set_and_unit_slope_charts (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ GraphControlExceptions.points P r) ∧
      E.card ≤ 30 * P.totalDegree ^ 2 * (r + 1) ^ 2 ∧
      ∀ z : Fin 2 → ℝ, eval z P = 0 → z ∉ E →
        ∃ q : Piece P r, z q.independent ∈ Ioo q.left q.right ∧
          (fun j ↦ q.path j (z q.independent)) = z := by
  classical
  obtain ⟨E, hE, hcard⟩ := GraphControlExceptions.exists_finset P hP hD r
  refine ⟨E, hE, hcard, ?_⟩
  intro z hzero hnot
  exact exists_at_nonexceptional P hP hD r z hzero (fun hz ↦ hnot ((hE z).mpr hz))

end PaperP1.UnitSlopeNormalizedCharts
