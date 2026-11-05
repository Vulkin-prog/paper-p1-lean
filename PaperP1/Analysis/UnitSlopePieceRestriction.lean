module

public import PaperP1.Analysis.UnitSlopeNormalizedCharts
public import PaperP1.Analysis.FiniteSetAvoidingInterval

/-! # Restricting actual unit-slope pieces while avoiding finite point sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitSlopePieceRestriction

open MvPolynomial Set UnitSlopeNormalizedCharts
open scoped ContDiff

def restrict {P : MvPolynomial (Fin 2) ℝ} {r : ℕ} (q : Piece P r)
    (a b : ℝ) (hab : a < b) (hsub : Ioo a b ⊆ Ioo q.left q.right) : Piece P r where
  independent := q.independent
  left := a
  right := b
  ordered := hab
  path := q.path
  normalized_coordinate := fun t ht ↦ q.normalized_coordinate t (hsub ht)
  trajectory := by
    by_cases hi : q.independent = 0
    · have hbig : GraphTangentEvaluation.Trajectory P q.path (Ioo q.left q.right) := by
        simpa only [hi, ite_true] using q.trajectory
      have hsmall : GraphTangentEvaluation.Trajectory P q.path (Ioo a b) :=
        ⟨(fun t ht ↦ hbig.1 t (hsub ht)), (fun t ht i ↦ hbig.2 t (hsub ht) i)⟩
      simpa only [hi, ite_true] using hsmall
    · have hbig : TransposedNormalizedGraphPiece.Trajectory P q.path (Ioo q.left q.right) := by
        simpa only [hi, ite_false] using q.trajectory
      have hsmall : TransposedNormalizedGraphPiece.Trajectory P q.path (Ioo a b) :=
        ⟨(fun t ht ↦ hbig.1 t (hsub ht)), (fun t ht i ↦ hbig.2 t (hsub ht) i)⟩
      simpa only [hi, ite_false] using hsmall
  smooth := fun i ↦ (q.smooth i).mono hsub
  equation := fun t ht ↦ q.equation t (hsub ht)
  avoids := fun t ht ↦ q.avoids t (hsub ht)
  derivative_signs := fun n hn t ht u hu ↦ q.derivative_signs n hn t (hsub ht) u (hsub hu)
  slope := fun t ht ↦ q.slope t (hsub ht)
  distance := fun t ht u hu ↦ q.distance t (hsub ht) u (hsub hu)

theorem exists_avoiding (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P r)
    (x₀ : ℝ) (hx : x₀ ∈ Ioo q.left q.right) (E : Finset (Fin 2 → ℝ))
    (hnot : (fun i ↦ q.path i x₀) ∉ E) :
    ∃ q' : Piece P r, x₀ ∈ Ioo q'.left q'.right ∧ q'.path = q.path ∧
      q'.independent = q.independent ∧ ∀ t ∈ Ioo q'.left q'.right, (fun i ↦ q'.path i t) ∉ E := by
  have hc : ContinuousOn (fun t ↦ fun i ↦ q.path i t) (Ioo q.left q.right) :=
    continuousOn_pi.mpr (fun i ↦ (q.smooth i).continuousOn)
  obtain ⟨a, b, hmem, hsub, havoid⟩ := FiniteSetAvoidingInterval.exists_interval
    (fun t ↦ fun i ↦ q.path i t) x₀ (Ioo q.left q.right) (isOpen_Ioo.mem_nhds hx)
      (hc.continuousAt (isOpen_Ioo.mem_nhds hx)) E hnot
  exact ⟨restrict q a b (hmem.1.trans hmem.2) hsub, hmem, rfl, rfl, havoid⟩

end PaperP1.UnitSlopePieceRestriction
