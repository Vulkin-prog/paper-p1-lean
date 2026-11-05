module

public import PaperP1.Analysis.PolynomialVelocitySmooth
public import Mathlib.Topology.Order.Compact

/-! # Actual coordinate minima on the closure of a bounded curve population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompactCurvePopulationEnds

open MvPolynomial Set

theorem closure_box (C : Set (Fin 2 → ℝ)) (hbox : ∀ z ∈ C, ∀ i, |z i| ≤ 1) :
    ∀ z ∈ closure C, ∀ i, |z i| ≤ 1 := by
  have hsub : C ⊆ Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
    intro z hz
    exact ⟨fun i ↦ (abs_le.mp (hbox z hz i)).1, fun i ↦ (abs_le.mp (hbox z hz i)).2⟩
  have hc := closure_minimal hsub isClosed_Icc
  intro z hz i
  exact abs_le.mpr ⟨(hc hz).1 i, (hc hz).2 i⟩

theorem closure_curve (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ))
    (hcurve : ∀ z ∈ C, eval z P = 0) : ∀ z ∈ closure C, eval z P = 0 := by
  have hcont := (PolynomialVelocitySmooth.contDiff_eval P 0).continuous
  have hsub : C ⊆ {z | eval z P = 0} := fun z hz ↦ hcurve z hz
  have hc : closure C ⊆ {z | eval z P = 0} :=
    closure_minimal hsub (isClosed_eq hcont continuous_const)
  exact fun z hz ↦ hc hz

theorem closure_comparison (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ))
    (hcomp : ∀ z ∈ C, |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|) :
    ∀ z ∈ closure C, |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)| := by
  have hc0 := (PolynomialVelocitySmooth.contDiff_eval (pderiv 0 P) 0).continuous.abs
  have hc1 := (PolynomialVelocitySmooth.contDiff_eval (pderiv 1 P) 0).continuous.abs
  have hsub : C ⊆ {z | |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|} :=
    fun z hz ↦ hcomp z hz
  have hc : closure C ⊆ {z | |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|} :=
    closure_minimal hsub (isClosed_le hc0 hc1)
  exact fun z hz ↦ hc hz

theorem exists_coordinate_minimum (C : Set (Fin 2 → ℝ)) (hne : C.Nonempty)
    (hbox : ∀ z ∈ C, ∀ i, |z i| ≤ 1) (i : Fin 2) :
    ∃ w ∈ closure C, ∀ z ∈ closure C, w i ≤ z i := by
  have hsub : closure C ⊆ Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
    intro z hz
    exact ⟨fun j ↦ (abs_le.mp (closure_box C hbox z hz j)).1,
      fun j ↦ (abs_le.mp (closure_box C hbox z hz j)).2⟩
  have hcompact : IsCompact (closure C) := isCompact_Icc.of_isClosed_subset isClosed_closure hsub
  exact hcompact.exists_isMinOn (hne.mono subset_closure) (continuous_apply i).continuousOn

end PaperP1.CompactCurvePopulationEnds
