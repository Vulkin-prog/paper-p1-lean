module

public import PaperP1.Analysis.RegularCurveComponentGraphs
public import PaperP1.Analysis.TransposedGraphImageNeighborhood
public import PaperP1.Analysis.NormalizedScaledTangent

/-! # Actual finite-population charts on second-orientation regular components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondRegularCurveComponentGraphs

open MvPolynomial Set Filter PlaneCoordinateSwap ConnectedGraphReachability
open scoped Topology


def region (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {z | eval z P = 0 ∧ eval z (pderiv 0 P) ≠ 0} ∩ O

def pointImage {P : MvPolynomial (Fin 2) ℝ} (q : TransposedNormalizedGraphPiece.Piece P) : Set (Fin 2 → ℝ) :=
  (fun t ↦ fun i ↦ q.path i t) '' Ioo q.left q.right

def restrict {P : MvPolynomial (Fin 2) ℝ} (q : TransposedNormalizedGraphPiece.Piece P)
    (a b : ℝ) (hab : a < b) (hsub : Ioo a b ⊆ Ioo q.left q.right) : TransposedNormalizedGraphPiece.Piece P where
  left := a
  right := b
  ordered := hab
  path := q.path
  trajectory := ⟨(fun t ht ↦ q.trajectory.1 t (hsub ht)), (fun t ht i ↦ q.trajectory.2 t (hsub ht) i)⟩
  equation := fun t ht ↦ q.equation t (hsub ht)
  second_coordinate := fun t ht ↦ q.second_coordinate t (hsub ht)

theorem exists_local_chart_in_region (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (z : Fin 2 → ℝ) (hz : z ∈ region P O) :
    ∃ q : TransposedNormalizedGraphPiece.Piece P, z 1 ∈ Ioo q.left q.right ∧
      (fun i ↦ q.path i (z 1)) = z ∧ pointImage q ⊆ region P O := by
  obtain ⟨q, hmem, hpoint⟩ := TransposedNormalizedGraphPiece.exists_piece P z hz.1.1 hz.1.2
  have hsmooth := NormalizedScaledTangent.second_smooth P q.path (Ioo q.left q.right) isOpen_Ioo q.trajectory
  have hc : ContinuousAt (fun t : ℝ ↦ fun i ↦ q.path i t) (z 1) := by
    apply continuousAt_pi.mpr
    intro i
    exact (hsmooth i).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hpointO : (fun i ↦ q.path i (z 1)) ∈ O := by rw [hpoint]; exact hz.2
  have hnear : ∀ᶠ t in 𝓝 (z 1), (fun i ↦ q.path i t) ∈ O := hc.eventually (hO.mem_nhds hpointO)
  have hn : {t : ℝ | t ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i t) ∈ O} ∈ 𝓝 (z 1) :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hmem) hnear
  obtain ⟨a, b, hzab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let q' := restrict q a b (hzab.1.trans hzab.2) (fun t ht ↦ (hsub ht).1)
  refine ⟨q', hzab, hpoint, ?_⟩
  intro w hw
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨⟨q'.equation t ht, q'.trajectory.1 t ht⟩, (hsub ht).2⟩

theorem local_charts_on_component (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (anchor : Fin 2 → ℝ) :
    ∀ z ∈ connectedComponentIn (region P O) anchor, ∃ q : TransposedNormalizedGraphPiece.Piece P,
      z 1 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (z 1)) = z ∧
        pointImage q ⊆ connectedComponentIn (region P O) anchor := by
  intro z hz
  have hzregion := connectedComponentIn_subset (region P O) anchor hz
  obtain ⟨q, hparam, hpoint, hsub⟩ := exists_local_chart_in_region P O hO z hzregion
  have hc : ContinuousOn (fun t ↦ fun i ↦ q.path i t) (Ioo q.left q.right) :=
    BothGraphDerivativeFormulas.continuousOn_second P q.path _ q.trajectory
  have hconn : IsPreconnected (pointImage q) := isPreconnected_Ioo.image _ hc
  have hzimage : z ∈ pointImage q := ⟨z 1, hparam, hpoint⟩
  have hsubz := hconn.subset_connectedComponentIn hzimage hsub
  have heq := connectedComponentIn_eq hz
  rw [← heq] at hsubz
  exact ⟨q, hparam, hpoint, hsubz⟩

theorem finite_population_chart (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P O)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ z ∈ S, z ∈ connectedComponentIn (region P O) anchor) :
    ∃ q : TransposedNormalizedGraphPiece.Piece P, anchor 1 ∈ Ioo q.left q.right ∧
      (fun i ↦ q.path i (anchor 1)) = anchor ∧ pointImage q ⊆ connectedComponentIn (region P O) anchor ∧
        ∀ z ∈ S, z ∈ pointImage q := by
  classical
  let C := connectedComponentIn (region P O) anchor
  let C' := point '' C
  have hC' : IsPreconnected C' := isPreconnected_connectedComponentIn.image _
    TransposedGraphImageNeighborhood.continuous_point.continuousOn
  have hlocal' : LocalCharts (polynomial P) C' := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hw
    obtain ⟨q, hparam, hpoint, hsub⟩ := local_charts_on_component P O hO anchor z hz
    let q' := TransposedGraphOverlapUniqueness.firstPiece P q
    refine ⟨q', ?_, ?_, ?_⟩
    · change point z 0 ∈ Ioo q.left q.right
      simpa only [point, index_zero] using hparam
    · funext i
      change q.path (index i) (point z 0) = point z i
      simpa only [point, index_zero] using congrFun hpoint (index i)
    · intro v hv
      obtain ⟨t, ht, rfl⟩ := hv
      exact ⟨(fun i ↦ q.path i t), hsub ⟨t, ht, rfl⟩, rfl⟩
  have ha' : point anchor ∈ C' := ⟨anchor, mem_connectedComponentIn ha, rfl⟩
  let S' := S.image point
  have hS' : ∀ w ∈ S', w ∈ C' := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨z, hS z hz, rfl⟩
  obtain ⟨A, hcover⟩ := exists_chart_for_finite_population (polynomial P) C' (point anchor) ha' hC' hlocal' S' hS'
  let q := TransposedNormalizedGraphPiece.transposePiece P A.chart
  have hinitX : (fun i ↦ A.chart.path i (anchor 1)) = point anchor := by
    have hh := A.anchor_eq
    simpa only [point, index_zero] using hh
  refine ⟨q, ?_, TransposedNormalizedGraphPiece.initial_point P A.chart anchor hinitX, ?_, ?_⟩
  · change anchor 1 ∈ Ioo A.chart.left A.chart.right
    simpa only [point, index_zero] using A.anchor_mem
  · intro w hw
    obtain ⟨t, ht, rfl⟩ := hw
    have hX : (fun i ↦ A.chart.path i t) ∈ C' := A.image_subset ⟨t, ht, rfl⟩
    obtain ⟨v, hv, he⟩ := hX
    have hpointY : (fun i ↦ q.path i t) = v := by
      funext i
      have hh := congrFun he (index i)
      change A.chart.path (index i) t = v i
      simpa only [point, index_twice] using hh.symm
    change (fun i ↦ q.path i t) ∈ C
    rw [hpointY]
    exact hv
  · intro z hz
    have hz' : point z ∈ S' := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    obtain ⟨t, ht, he⟩ := hcover (point z) hz'
    refine ⟨t, ht, ?_⟩
    funext i
    have hh := congrFun he (index i)
    change A.chart.path (index i) t = z i
    simpa only [point, index_twice] using hh

end PaperP1.SecondRegularCurveComponentGraphs
