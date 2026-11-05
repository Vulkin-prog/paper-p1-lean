module

public import PaperP1.Analysis.SecondRegularCurveComponentGraphs
public import PaperP1.Analysis.ControlledGraphGridPointCount

/-! # Actual unit-slope charts and grid counts for second-orientation components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondRegularComponentUnitGridCount

open MvPolynomial Set SecondRegularCurveComponentGraphs
open scoped ContDiff


theorem exists_unit_piece (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ)) (hO : IsOpen O)
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P O) (r : ℕ)
    (havoid : ∀ w ∈ connectedComponentIn (region P O) anchor, w ∉ GraphControlExceptions.points P (r + 1))
    (hinit : |eval anchor (pderiv 1 P)| ≤ |eval anchor (pderiv 0 P)|)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ w ∈ S, w ∈ connectedComponentIn (region P O) anchor) :
    ∃ q : UnitSlopeNormalizedCharts.Piece P (r + 1),
      (∀ w ∈ S, ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w) ∧
      ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∈ connectedComponentIn (region P O) anchor := by
  obtain ⟨q₀, hmem, hpoint, hsub, hcover⟩ := finite_population_chart P O hO anchor ha S hS
  have hsmooth := NormalizedScaledTangent.second_smooth P q₀.path
    (Ioo q₀.left q₀.right) isOpen_Ioo q₀.trajectory
  have hnon : ∀ t ∈ Ioo q₀.left q₀.right,
      (fun i ↦ q₀.path i t) ∉ GraphControlExceptions.points P (r + 1) :=
    fun t ht ↦ havoid _ (hsub ⟨t, ht, rfl⟩)
  have hcomparison : |eval (fun i ↦ q₀.path i (anchor 1)) (pderiv 1 P)| ≤
      |eval (fun i ↦ q₀.path i (anchor 1)) (pderiv 0 P)| := by
    rw [hpoint]
    exact hinit
  let q := UnitSlopeNormalizedCharts.of_second P (r + 1) q₀ (anchor 1) hmem hsmooth hnon hcomparison
  refine ⟨q, hcover, ?_⟩
  exact fun t ht ↦ hsub ⟨t, ht, rfl⟩

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (O : Set (Fin 2 → ℝ)) (hO : IsOpen O)
    (anchor : Fin 2 → ℝ) (ha : anchor ∈ region P O) (k : ℕ) (hk : 1 ≤ k)
    (havoid : ∀ w ∈ connectedComponentIn (region P O) anchor,
      w ∉ GraphControlExceptions.points P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1))
    (hWr : ∀ w ∈ connectedComponentIn (region P O) anchor, w ∉ MonomialWronskianExceptions.exceptionalPoints P k)
    (hinit : |eval anchor (pderiv 1 P)| ≤ |eval anchor (pderiv 0 P)|)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ)) (hS : ∀ w ∈ S, w ∈ connectedComponentIn (region P O) anchor)
    (hbox : ∀ w ∈ S, ∀ i, |w i| ≤ 1)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10 := by
  obtain ⟨q, hcover, hcomponent⟩ := exists_unit_piece P O hO anchor ha
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) havoid hinit S hS
  exact ControlledGraphGridPointCount.minimal_order_count P k hk q
    (fun t ht ↦ hWr _ (hcomponent t ht)) N hN hlog S hcover hbox hgrid

end PaperP1.SecondRegularComponentUnitGridCount
