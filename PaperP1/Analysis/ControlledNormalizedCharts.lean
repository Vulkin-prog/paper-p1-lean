module

public import PaperP1.Analysis.NormalizedGraphFiniteAvoidance
public import PaperP1.Analysis.GraphControlledDerivatives

/-! # Constructed smooth normalized charts with simultaneous derivative signs

Every nonexceptional actual curve point has such a chart. The theorem is local;
it supplies no upper bound for the total number of charts covering the curve.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ControlledNormalizedCharts

open MvPolynomial Set PlaneCoordinateSwap
open scoped ContDiff

def HasControlledChart (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (z : Fin 2 → ℝ) : Prop :=
  ∃ i : Fin 2, ∃ a b : ℝ, ∃ φ : Fin 2 → ℝ → ℝ,
    z i ∈ Ioo a b ∧ (fun j ↦ φ j (z i)) = z ∧
    (∀ t ∈ Ioo a b, φ i t = t) ∧
    (if i = 0 then GraphTangentEvaluation.Trajectory P φ (Ioo a b)
      else TransposedNormalizedGraphPiece.Trajectory P φ (Ioo a b)) ∧
    (∀ j, ContDiffOn ℝ ∞ (φ j) (Ioo a b)) ∧
    (∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) P = 0) ∧
    (∀ t ∈ Ioo a b, (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r) ∧
    ∀ n ≤ r, ∀ t ∈ Ioo a b, ∀ u ∈ Ioo a b,
      SignType.sign (iteratedDeriv n (φ (index i)) t) =
        SignType.sign (iteratedDeriv n (φ (index i)) u)

theorem exists_first (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hA : eval z (pderiv 1 P) ≠ 0) (hnot : z ∉ GraphControlExceptions.points P r) :
    HasControlledChart P r z := by
  classical
  obtain ⟨E, hE, _hcard⟩ := GraphControlExceptions.exists_finset P hP hD r
  have hn : z ∉ E := fun hz ↦ hnot ((hE z).mp hz)
  obtain ⟨q, hmem, hpoint, hsmooth, havoid⟩ :=
    NormalizedGraphFiniteAvoidance.exists_first P z hzero hA E hn
  have hnon : ∀ t ∈ Ioo q.left q.right, (fun j ↦ q.path j t) ∉ GraphControlExceptions.points P r :=
    fun t ht hz ↦ havoid t ht ((hE _).mpr hz)
  refine ⟨0, q.left, q.right, q.path, hmem, hpoint, q.first_coordinate, ?_, hsmooth, q.equation, hnon, ?_⟩
  · simpa only [ite_true] using q.trajectory
  · intro n hn t ht u hu
    simpa only [index_zero] using GraphControlledDerivatives.first_all_orders_sign P r q.path
      (Ioo q.left q.right) isOpen_Ioo isPreconnected_Ioo q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, hnon v hv⟩) n hn t u ht hu

theorem exists_second (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hA : eval z (pderiv 0 P) ≠ 0) (hnot : z ∉ GraphControlExceptions.points P r) :
    HasControlledChart P r z := by
  classical
  obtain ⟨E, hE, _hcard⟩ := GraphControlExceptions.exists_finset P hP hD r
  have hn : z ∉ E := fun hz ↦ hnot ((hE z).mp hz)
  obtain ⟨q, hmem, hpoint, hsmooth, havoid⟩ :=
    NormalizedGraphFiniteAvoidance.exists_second P z hzero hA E hn
  have hnon : ∀ t ∈ Ioo q.left q.right, (fun j ↦ q.path j t) ∉ GraphControlExceptions.points P r :=
    fun t ht hz ↦ havoid t ht ((hE _).mpr hz)
  refine ⟨1, q.left, q.right, q.path, hmem, hpoint, q.second_coordinate, ?_, hsmooth, q.equation, hnon, ?_⟩
  · simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using q.trajectory
  · intro n hn t ht u hu
    simpa only [index_one] using GraphControlledDerivatives.second_all_orders_sign P r q.path
      (Ioo q.left q.right) isOpen_Ioo isPreconnected_Ioo q.trajectory
      (fun v hv ↦ ⟨q.equation v hv, hnon v hv⟩) n hn t u ht hu

theorem exists_at_nonexceptional (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hnot : z ∉ GraphControlExceptions.points P r) : HasControlledChart P r z := by
  obtain ⟨i, hi⟩ := GraphControlExceptions.gradient_nonzero P hD r z hzero hnot
  fin_cases i
  · exact exists_second P hP hD r z hzero hi hnot
  · exact exists_first P hP hD r z hzero hi hnot

theorem exists_control_set_and_charts (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ GraphControlExceptions.points P r) ∧
      E.card ≤ 30 * P.totalDegree ^ 2 * (r + 1) ^ 2 ∧
      ∀ z : Fin 2 → ℝ, eval z P = 0 → z ∉ E → HasControlledChart P r z := by
  classical
  obtain ⟨E, hE, hcard⟩ := GraphControlExceptions.exists_finset P hP hD r
  refine ⟨E, hE, hcard, ?_⟩
  intro z hzero hnot
  exact exists_at_nonexceptional P hP hD r z hzero (fun hz ↦ hnot ((hE z).mpr hz))

end PaperP1.ControlledNormalizedCharts
