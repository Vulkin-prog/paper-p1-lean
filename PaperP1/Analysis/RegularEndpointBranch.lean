module

public import PaperP1.Analysis.ControlledRegularComponentEnds

/-! # One genuine right-hand branch shared by every component with a regular minimum end -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularEndpointBranch

open MvPolynomial Set RegularCurveComponentGraphs JointExceptionalComponentGridCount
open AnchoredNormalizedGraph

theorem exists_branch (P : MvPolynomial (Fin 2) ℝ) (E : Finset (Fin 2 → ℝ))
    (w : Fin 2 → ℝ) (hwP : eval w P = 0) (hwE : w ∈ E)
    (hwbox : w ∈ unitBox) (hwPy : eval w (pderiv 1 P) ≠ 0) :
    ∃ B : Set (Fin 2 → ℝ), B.Nonempty ∧ IsPreconnected B ∧
      B ⊆ region P (openRegion E) ∧
      ∀ anchor : Fin 2 → ℝ,
        w ∈ closure (connectedComponentIn (region P (openRegion E)) anchor) →
        (∀ z ∈ connectedComponentIn (region P (openRegion E)) anchor, w 0 ≤ z 0) →
        B ⊆ connectedComponentIn (region P (openRegion E)) anchor := by
  classical
  have hwregion : w ∈ region P (openRegion (E.erase w)) :=
    ⟨⟨hwP, hwPy⟩, hwbox, Finset.notMem_erase w E⟩
  obtain ⟨q, hparam, hpoint, hqsub⟩ := exists_local_chart_in_region P
    (openRegion (E.erase w)) (openRegion_isOpen _) w hwregion
  let Φ : ℝ → Fin 2 → ℝ := fun t i ↦ q.path i t
  let B : Set (Fin 2 → ℝ) := Φ '' Ioo (w 0) q.right
  have hdomain : Ioo (w 0) q.right ⊆ Ioo q.left q.right :=
    fun _ ht ↦ ⟨hparam.1.trans ht.1, ht.2⟩
  have hcont : ContinuousOn Φ (Ioo q.left q.right) := by
    apply continuousOn_pi.mpr
    intro i
    exact HasDerivAt.continuousOn (fun t ht ↦ q.trajectory.2 t ht i)
  have hconn : IsPreconnected B := isPreconnected_Ioo.image _ (hcont.mono hdomain)
  have hne : B.Nonempty := by
    refine ⟨Φ ((w 0 + q.right) / 2), (w 0 + q.right) / 2, ?_, rfl⟩
    constructor <;> linarith only [hparam.2]
  have hsub : B ⊆ region P (openRegion E) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hqr := hqsub ⟨t, hdomain ht, rfl⟩
    refine ⟨hqr.1, hqr.2.1, ?_⟩
    intro hzE
    have hneq : Φ t ≠ w := by
      intro he
      have he0 : t = w 0 := (q.first_coordinate t (hdomain ht)).symm.trans (congrFun he 0)
      exact (ne_of_gt ht.1) he0
    exact hqr.2.2 (Finset.mem_erase.mpr ⟨hneq, hzE⟩)
  refine ⟨B, hne, hconn, hsub, ?_⟩
  intro anchor hwclosure hmin
  obtain ⟨U, hUopen, hUmem, hUcover⟩ :=
    NormalizedGraphImageNeighborhood.exists_open_neighborhood P q (w 0) hparam
  have hwU : w ∈ U := by rw [← hpoint]; exact hUmem
  obtain ⟨v, hvU, hvC⟩ := mem_closure_iff.mp hwclosure U hUopen hwU
  have hvregion := connectedComponentIn_subset (region P (openRegion E)) anchor hvC
  obtain ⟨hvparam, hvpoint⟩ := hUcover v hvU hvregion.1.1
  have hvne : v ≠ w := by
    intro he
    exact hvregion.2.2 (he ▸ hwE)
  have hxne : w 0 ≠ v 0 := by
    intro he
    apply hvne
    rw [← he] at hvpoint
    exact hvpoint.symm.trans hpoint
  have hvB : v ∈ B := ⟨v 0, ⟨lt_of_le_of_ne (hmin v hvC) hxne, hvparam.2⟩, hvpoint⟩
  have hs := hconn.subset_connectedComponentIn hvB hsub
  rw [← connectedComponentIn_eq hvC] at hs
  exact hs

end PaperP1.RegularEndpointBranch
