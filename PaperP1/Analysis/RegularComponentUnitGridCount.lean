module

public import PaperP1.Analysis.RegularCurveComponentGraphs
public import PaperP1.Analysis.ControlledGraphGridPointCount

/-! # Actual unit-slope charts and grid counts for regular curve component populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularComponentUnitGridCount

open MvPolynomial Set AnchoredNormalizedGraph RegularCurveComponentGraphs
open scoped ContDiff


theorem exists_unit_piece (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ)) (hO : IsOpen O)
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P O) (r : ℕ)
    (havoid : ∀ w ∈ connectedComponentIn (region P O) anchor, w ∉ GraphControlExceptions.points P (r + 1))
    (hinit : |eval anchor (pderiv 0 P)| ≤ |eval anchor (pderiv 1 P)|)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ w ∈ S, w ∈ connectedComponentIn (region P O) anchor) :
    ∃ q : UnitSlopeNormalizedCharts.Piece P (r + 1),
      (∀ w ∈ S, ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w) ∧
      ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∈ connectedComponentIn (region P O) anchor := by
  obtain ⟨A, hcover⟩ := finite_population_chart P O hO anchor ha S hS
  have hsmooth := GraphTangentSmooth.contDiffOn_trajectory P A.chart.path
    (Ioo A.chart.left A.chart.right) isOpen_Ioo A.chart.trajectory
  have hnon : ∀ t ∈ Ioo A.chart.left A.chart.right,
      (fun i ↦ A.chart.path i t) ∉ GraphControlExceptions.points P (r + 1) :=
    fun t ht ↦ havoid _ (A.image_subset ⟨t, ht, rfl⟩)
  have hcomparison : |eval (fun i ↦ A.chart.path i (anchor 0)) (pderiv 0 P)| ≤
      |eval (fun i ↦ A.chart.path i (anchor 0)) (pderiv 1 P)| := by
    rw [A.anchor_eq]
    exact hinit
  let q := UnitSlopeNormalizedCharts.of_first P (r + 1) A.chart (anchor 0) A.anchor_mem hsmooth hnon hcomparison
  refine ⟨q, hcover, ?_⟩
  exact fun t ht ↦ A.image_subset ⟨t, ht, rfl⟩

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ)) (hO : IsOpen O)
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P O) (k : ℕ) (hk : 1 ≤ k)
    (havoid : ∀ w ∈ connectedComponentIn (region P O) anchor,
      w ∉ GraphControlExceptions.points P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1))
    (hWr : ∀ w ∈ connectedComponentIn (region P O) anchor, w ∉ MonomialWronskianExceptions.exceptionalPoints P k)
    (hinit : |eval anchor (pderiv 0 P)| ≤ |eval anchor (pderiv 1 P)|)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ w ∈ S, w ∈ connectedComponentIn (region P O) anchor)
    (hbox : ∀ w ∈ S, ∀ i, |w i| ≤ 1)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10 := by
  obtain ⟨q, hcover, hcomponent⟩ := exists_unit_piece P O hO anchor ha
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) havoid hinit S hS
  exact ControlledGraphGridPointCount.minimal_order_count P k hk q
    (fun t ht ↦ hWr _ (hcomponent t ht)) N hN hlog S hcover hbox hgrid

end PaperP1.RegularComponentUnitGridCount
