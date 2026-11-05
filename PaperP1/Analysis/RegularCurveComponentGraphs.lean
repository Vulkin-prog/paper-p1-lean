module

public import PaperP1.Analysis.ConnectedGraphReachability

/-! # Actual single charts containing every finite population in a regular curve component

Open ambient restrictions are allowed. Local charts inside each connected
component are constructed from the actual polynomial ODE and connectedness.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularCurveComponentGraphs

open MvPolynomial Set Filter LocalNormalizedGraphPiece AnchoredNormalizedGraph ConnectedGraphReachability
open scoped Topology


def region (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {z | eval z P = 0 ∧ eval z (pderiv 1 P) ≠ 0} ∩ O

def restrict {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) (a b : ℝ) (hab : a < b)
    (hsub : Ioo a b ⊆ Ioo q.left q.right) : Piece P where
  left := a
  right := b
  ordered := hab
  path := q.path
  trajectory := ⟨(fun t ht ↦ q.trajectory.1 t (hsub ht)), (fun t ht i ↦ q.trajectory.2 t (hsub ht) i)⟩
  equation := fun t ht ↦ q.equation t (hsub ht)
  first_coordinate := fun t ht ↦ q.first_coordinate t (hsub ht)

theorem exists_local_chart_in_region (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (z : Fin 2 → ℝ) (hz : z ∈ region P O) :
    ∃ q : Piece P, z 0 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (z 0)) = z ∧ pointImage q ⊆ region P O := by
  obtain ⟨q, hmem, hpoint⟩ := LocalNormalizedGraphPiece.exists_piece P z hz.1.1 hz.1.2
  have hsmooth := GraphTangentSmooth.contDiffOn_trajectory P q.path (Ioo q.left q.right) isOpen_Ioo q.trajectory
  have hc : ContinuousAt (fun t : ℝ ↦ fun i ↦ q.path i t) (z 0) := by
    apply continuousAt_pi.mpr
    intro i
    exact (hsmooth i).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hpointO : (fun i ↦ q.path i (z 0)) ∈ O := by rw [hpoint]; exact hz.2
  have hnear : ∀ᶠ t in 𝓝 (z 0), (fun i ↦ q.path i t) ∈ O := hc.eventually (hO.mem_nhds hpointO)
  have hn : {t : ℝ | t ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i t) ∈ O} ∈ 𝓝 (z 0) :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hmem) hnear
  obtain ⟨a, b, hzab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let q' := restrict q a b (hzab.1.trans hzab.2) (fun t ht ↦ (hsub ht).1)
  refine ⟨q', hzab, hpoint, ?_⟩
  intro w hw
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨⟨q'.equation t ht, q'.trajectory.1 t ht⟩, (hsub ht).2⟩

theorem local_charts_on_component (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (anchor : Fin 2 → ℝ) :
    LocalCharts P (connectedComponentIn (region P O) anchor) := by
  intro z hz
  have hzregion : z ∈ region P O := connectedComponentIn_subset (region P O) anchor hz
  obtain ⟨q, hparam, hpoint, hsub⟩ := exists_local_chart_in_region P O hO z hzregion
  have hc : ContinuousOn (fun t ↦ fun i ↦ q.path i t) (Ioo q.left q.right) := by
    apply continuousOn_pi.mpr
    intro i
    exact HasDerivAt.continuousOn (fun t ht ↦ q.trajectory.2 t ht i)
  have hconn : IsPreconnected (pointImage q) := isPreconnected_Ioo.image _ hc
  have hzimage : z ∈ pointImage q := ⟨z 0, hparam, hpoint⟩
  have hsubz := hconn.subset_connectedComponentIn hzimage hsub
  have heq := connectedComponentIn_eq hz
  rw [← heq] at hsubz
  exact ⟨q, hparam, hpoint, hsubz⟩

theorem finite_population_chart (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ))
    (hO : IsOpen O) (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P O)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ z ∈ S, z ∈ connectedComponentIn (region P O) anchor) :
    ∃ A : Anchored P (connectedComponentIn (region P O) anchor) anchor, ∀ z ∈ S, z ∈ pointImage A.chart :=
  exists_chart_for_finite_population P (connectedComponentIn (region P O) anchor) anchor
    (mem_connectedComponentIn ha) isPreconnected_connectedComponentIn (local_charts_on_component P O hO anchor) S hS

end PaperP1.RegularCurveComponentGraphs
