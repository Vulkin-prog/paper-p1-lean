module

public import PaperP1.Analysis.ScaledMonomialPieceCount
public import PaperP1.Analysis.AffineUnitGraphParametrization

/-! # All-polynomial point counts on the actual affine unit-graph maps -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitGraphMonomialPieceCount

open MvPolynomial Set UnitSlopeNormalizedCharts LocalAffineDerivativeFormula
  MonomialWronskianExceptions TotalDegreeMonomials
open scoped ContDiff

theorem exists_scale (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P r) :
    ∃ a : ℝ → ℝ, ContDiffOn ℝ ∞ a (Ioo q.left q.right) ∧
      (∀ t ∈ Ioo q.left q.right, a t ≠ 0) ∧
      ScaledPolynomialTangentTrajectory.Trajectory P a q.path (Ioo q.left q.right) := by
  by_cases hi : q.independent = 0
  · have hφ : GraphTangentEvaluation.Trajectory P q.path (Ioo q.left q.right) := by
      simpa only [hi, ite_true] using q.trajectory
    exact ⟨NormalizedScaledTangent.firstScale P q.path,
      NormalizedScaledTangent.firstScale_smooth P q.path _ isOpen_Ioo hφ,
      NormalizedScaledTangent.firstScale_ne_zero P q.path _ hφ,
      NormalizedScaledTangent.first_trajectory P q.path _ hφ⟩
  · have hφ : TransposedNormalizedGraphPiece.Trajectory P q.path (Ioo q.left q.right) := by
      simpa only [hi, ite_false] using q.trajectory
    exact ⟨NormalizedScaledTangent.secondScale P q.path,
      NormalizedScaledTangent.secondScale_smooth P q.path _ isOpen_Ioo hφ,
      NormalizedScaledTangent.secondScale_ne_zero P q.path _ hφ,
      NormalizedScaledTangent.second_trajectory P q.path _ hφ⟩

theorem exists_affine_scale (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P (r + 1))
    (u c : ℝ) (hc : 0 < c) (hmap : MapsTo (parameter u c) (Ioo (0 : ℝ) 1) (Ioo q.left q.right)) :
    ∃ a : ℝ → ℝ, ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, a t ≠ 0) ∧
      ScaledPolynomialTangentTrajectory.Trajectory P a
        (AffineUnitGraphParametrization.path q u c) (Ioo (0 : ℝ) 1) := by
  obtain ⟨a, ha, hne, htraj⟩ := exists_scale P (r + 1) q
  refine ⟨(fun t ↦ c * a (parameter u c t)), ?_, ?_, ?_⟩
  · exact contDiffOn_const.mul (smooth_composition a q.left q.right ha u c (Ioo (0 : ℝ) 1) hmap)
  · exact fun t ht ↦ mul_ne_zero hc.ne' (hne _ (hmap ht))
  · exact ScaledPolynomialTangentTrajectory.affine_trajectory P a q.path _ htraj u c _ hmap

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) (q : Piece P (r + 1))
    (u c : ℝ) (hc : 0 < c) (hmap : MapsTo (parameter u c) (Ioo (0 : ℝ) 1) (Ioo q.left q.right))
    (hnon : ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ exceptionalPoints P k)
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) (hdegree : Q.totalDegree ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1,
      (fun i ↦ AffineUnitGraphParametrization.path q u c i t) = z) ∧ eval z Q = 0) :
    S.card < Fintype.card (Index k) := by
  obtain ⟨a, ha, hne, htraj⟩ := exists_affine_scale P r q u c hc hmap
  exact ScaledMonomialPieceCount.point_count P k a (AffineUnitGraphParametrization.path q u c) 0 1 ha hne htraj
    (fun t ht ↦ q.equation _ (hmap ht)) (fun t ht ↦ hnon _ (hmap ht)) Q hQ hdegree S hS

end PaperP1.UnitGraphMonomialPieceCount
