module

public import PaperP1.Analysis.RegularCurveComponentGraphs

/-! # A coordinate-minimum endpoint of a regular curve component leaves its region -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularComponentMinimumBoundary

open MvPolynomial Set RegularCurveComponentGraphs AnchoredNormalizedGraph

theorem minimum_not_in_region (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (anchor w : Fin 2 → ℝ)
    (hw : w ∈ closure (connectedComponentIn (region P O) anchor))
    (hmin : ∀ z ∈ closure (connectedComponentIn (region P O) anchor), w 0 ≤ z 0) :
    w ∉ region P O := by
  intro hwregion
  obtain ⟨q, hparam, hpoint, hsub⟩ := exists_local_chart_in_region P O hO w hwregion
  obtain ⟨U, hUopen, hUmem, hUcover⟩ :=
    NormalizedGraphImageNeighborhood.exists_open_neighborhood P q (w 0) hparam
  have hwU : w ∈ U := by rw [← hpoint]; exact hUmem
  obtain ⟨v, hvU, hvC⟩ := mem_closure_iff.mp hw U hUopen hwU
  have hvzero := (connectedComponentIn_subset (region P O) anchor hvC).1.1
  obtain ⟨hvparam, hvpoint⟩ := hUcover v hvU hvzero
  have hvimage : v ∈ pointImage q := ⟨v 0, hvparam, hvpoint⟩
  have hcont : ContinuousOn (fun t ↦ fun i ↦ q.path i t) (Ioo q.left q.right) := by
    apply continuousOn_pi.mpr
    intro i
    exact HasDerivAt.continuousOn (fun t ht ↦ q.trajectory.2 t ht i)
  have hconn : IsPreconnected (pointImage q) := isPreconnected_Ioo.image _ hcont
  have himageC : pointImage q ⊆ connectedComponentIn (region P O) anchor := by
    have hs := hconn.subset_connectedComponentIn hvimage hsub
    rw [← connectedComponentIn_eq hvC] at hs
    exact hs
  let t : ℝ := (q.left + w 0) / 2
  have htleft : q.left < t := by dsimp [t]; linarith only [hparam.1]
  have htw : t < w 0 := by dsimp [t]; linarith only [hparam.1]
  have ht : t ∈ Ioo q.left q.right := ⟨htleft, htw.trans hparam.2⟩
  have hlow := hmin (fun i ↦ q.path i t) (subset_closure (himageC ⟨t, ht, rfl⟩))
  rw [q.first_coordinate t ht] at hlow
  exact (not_le_of_gt htw) hlow

end PaperP1.RegularComponentMinimumBoundary
