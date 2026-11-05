module

public import PaperP1.Analysis.FiniteSetAvoidingInterval
public import PaperP1.Analysis.BothGraphDerivativeFormulas

/-! # Constructed normalized graphs avoiding any prescribed finite point set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedGraphFiniteAvoidance

open MvPolynomial Set BothGraphDerivativeFormulas
open scoped ContDiff

theorem exists_first (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hA : eval z (pderiv 1 P) ≠ 0)
    (E : Finset (Fin 2 → ℝ)) (hnot : z ∉ E) :
    ∃ q : LocalNormalizedGraphPiece.Piece P,
      z 0 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (z 0)) = z ∧
      (∀ i, ContDiffOn ℝ ∞ (q.path i) (Ioo q.left q.right)) ∧
      ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ E := by
  classical
  obtain ⟨r, hmem, hpoint, hsmooth, _hder⟩ :=
    LocalNormalizedGraphPiece.exists_smooth_piece_with_derivatives P z hzero hA
  have hc : ContinuousAt (fun t ↦ fun i ↦ r.path i t) (z 0) :=
    (continuousOn_first P r.path _ r.trajectory).continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hnot₀ : (fun i ↦ r.path i (z 0)) ∉ E := by rw [hpoint]; exact hnot
  obtain ⟨a, b, hmem', hsub, havoid⟩ := FiniteSetAvoidingInterval.exists_interval
    (fun t ↦ fun i ↦ r.path i t) (z 0) (Ioo r.left r.right)
      (isOpen_Ioo.mem_nhds hmem) hc E hnot₀
  let q : LocalNormalizedGraphPiece.Piece P :=
    { left := a
      right := b
      ordered := hmem'.1.trans hmem'.2
      path := r.path
      trajectory := ⟨(fun t ht ↦ r.trajectory.1 t (hsub ht)),
        (fun t ht i ↦ r.trajectory.2 t (hsub ht) i)⟩
      equation := fun t ht ↦ r.equation t (hsub ht)
      first_coordinate := fun t ht ↦ r.first_coordinate t (hsub ht) }
  exact ⟨q, hmem', hpoint, (fun i ↦ (hsmooth i).mono hsub), havoid⟩

theorem exists_second (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hA : eval z (pderiv 0 P) ≠ 0)
    (E : Finset (Fin 2 → ℝ)) (hnot : z ∉ E) :
    ∃ q : TransposedNormalizedGraphPiece.Piece P,
      z 1 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (z 1)) = z ∧
      (∀ i, ContDiffOn ℝ ∞ (q.path i) (Ioo q.left q.right)) ∧
      ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ E := by
  classical
  obtain ⟨r, hmem, hpoint, hsmooth, _hder⟩ :=
    TransposedNormalizedGraphPiece.exists_smooth_piece_with_derivatives P z hzero hA
  have hc : ContinuousAt (fun t ↦ fun i ↦ r.path i t) (z 1) :=
    (continuousOn_second P r.path _ r.trajectory).continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hnot₀ : (fun i ↦ r.path i (z 1)) ∉ E := by rw [hpoint]; exact hnot
  obtain ⟨a, b, hmem', hsub, havoid⟩ := FiniteSetAvoidingInterval.exists_interval
    (fun t ↦ fun i ↦ r.path i t) (z 1) (Ioo r.left r.right)
      (isOpen_Ioo.mem_nhds hmem) hc E hnot₀
  let q : TransposedNormalizedGraphPiece.Piece P :=
    { left := a
      right := b
      ordered := hmem'.1.trans hmem'.2
      path := r.path
      trajectory := ⟨(fun t ht ↦ r.trajectory.1 t (hsub ht)),
        (fun t ht i ↦ r.trajectory.2 t (hsub ht) i)⟩
      equation := fun t ht ↦ r.equation t (hsub ht)
      second_coordinate := fun t ht ↦ r.second_coordinate t (hsub ht) }
  exact ⟨q, hmem', hpoint, (fun i ↦ (hsmooth i).mono hsub), havoid⟩

end PaperP1.NormalizedGraphFiniteAvoidance
