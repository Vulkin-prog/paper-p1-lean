module

public import PaperP1.Analysis.CompactCurvePopulationEnds
public import PaperP1.Analysis.RegularComponentMinimumBoundary
public import PaperP1.Analysis.JointExceptionalComponentGridCount
public import PaperP1.Algebra.CurveComponentBarrier

/-! # Actual minimum endpoints of controlled regular components in the unit box -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ControlledRegularComponentEnds

open MvPolynomial Set RegularCurveComponentGraphs JointExceptionalComponentGridCount
open CompactCurvePopulationEnds CurveComponentBarrier

theorem exists_end_of_comparison (P : MvPolynomial (Fin 2) ℝ) (E : Finset (Fin 2 → ℝ))
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P (openRegion E))
    (hcomp : ∀ z ∈ connectedComponentIn (region P (openRegion E)) anchor,
      |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|) :
    ∃ w ∈ closure (connectedComponentIn (region P (openRegion E)) anchor),
      eval w P = 0 ∧ (∀ i, |w i| ≤ 1) ∧
      (∀ z ∈ closure (connectedComponentIn (region P (openRegion E)) anchor), w 0 ≤ z 0) ∧
      (eval w (barrier P) = 0 ∨ (w ∈ E ∧ w ∈ unitBox ∧ eval w (pderiv 1 P) ≠ 0)) := by
  let C := connectedComponentIn (region P (openRegion E)) anchor
  have hCbox : ∀ z ∈ C, ∀ i, |z i| ≤ 1 := by
    intro z hz i
    exact ((connectedComponentIn_subset (region P (openRegion E)) anchor hz).2.1 i).le
  obtain ⟨w, hw, hmin⟩ := exists_coordinate_minimum C ⟨anchor, mem_connectedComponentIn ha⟩ hCbox 0
  have hwP : eval w P = 0 := closure_curve P C
    (fun z hz ↦ (connectedComponentIn_subset (region P (openRegion E)) anchor hz).1.1) w hw
  have hwbox := closure_box C hCbox w hw
  have hwcomp := closure_comparison P C hcomp w hw
  refine ⟨w, hw, hwP, hwbox, hmin, ?_⟩
  by_cases hH : eval w (barrier P) = 0
  · exact Or.inl hH
  · apply Or.inr
    have hPy : eval w (pderiv 1 P) ≠ 0 := by
      intro hy
      have hx : eval w (pderiv 0 P) = 0 := abs_eq_zero.mp
        (le_antisymm (by simpa only [hy, abs_zero] using hwcomp) (abs_nonneg _))
      exact hH (zero_of_gradient P w (by intro i; fin_cases i <;> assumption))
    have hwinside : w ∈ unitBox := by
      intro i
      exact lt_of_le_of_ne (hwbox i) (fun he ↦ hH (zero_of_boundary P w ⟨i, he⟩))
    refine ⟨?_, hwinside, hPy⟩
    by_contra hnot
    exact RegularComponentMinimumBoundary.minimum_not_in_region P (openRegion E)
      (openRegion_isOpen E) anchor w hw hmin ⟨⟨hwP, hPy⟩, hwinside, hnot⟩

theorem exists_controlled_end (P : MvPolynomial (Fin 2) ℝ) (E : Finset (Fin 2 → ℝ))
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P (openRegion E)) (r : ℕ)
    (havoid : ∀ z ∈ connectedComponentIn (region P (openRegion E)) anchor,
      z ∉ GraphControlExceptions.points P r)
    (hinit : |eval anchor (pderiv 0 P)| ≤ |eval anchor (pderiv 1 P)|) :
    ∃ w ∈ closure (connectedComponentIn (region P (openRegion E)) anchor),
      eval w P = 0 ∧ (∀ i, |w i| ≤ 1) ∧
      (∀ z ∈ closure (connectedComponentIn (region P (openRegion E)) anchor), w 0 ≤ z 0) ∧
      (eval w (barrier P) = 0 ∨ (w ∈ E ∧ w ∈ unitBox ∧ eval w (pderiv 1 P) ≠ 0)) := by
  apply exists_end_of_comparison P E anchor ha
  intro z hz
  exact GradientComparisonControl.abs_le_propagates P r _ isPreconnected_connectedComponentIn
    id continuousOn_id (fun w hw ↦
      ⟨(connectedComponentIn_subset (region P (openRegion E)) anchor hw).1.1, havoid w hw⟩)
    anchor (mem_connectedComponentIn ha) hinit z hz

end PaperP1.ControlledRegularComponentEnds
