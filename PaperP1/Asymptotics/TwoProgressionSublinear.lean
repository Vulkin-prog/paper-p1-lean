module

public import PaperP1.Asymptotics.ResidualComponentRank
public import PaperP1.Arithmetic.PrimeFactorBudget
public import PaperP1.Arithmetic.TwoProgressionResidualRank

/-! # Sublinear residual rank with the actual omitted-prime budget discharged -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoProgressionSublinear

open Finset PaperP1.Arithmetic PaperP1.TwoProgressionPrimeRows PaperP1.FiniteResidualRank

theorem rank_sublinear (c D C₀ V ε : ℝ) (d : ℕ) (hc : 0 < c) (hD : 0 < D) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ S : Finset ℕ, ∀ H a b Ux Uy Rx Ry U R : ℕ,
      B ≤ H → (H : ℝ) ≤ C₀ * B → 0 < a → 0 < b → a * b ≤ B ^ d →
      Rx ≤ H → Ry ≤ H → S ⊆ progression a Ux Rx ∪ progression b Uy Ry →
      (∀ n ∈ S, U ≤ n) → (∀ n ∈ S, n ≤ U + R) →
      1 ≤ R → 2 * R ≤ U → c * B ≤ Real.log U →
      Real.log (64 * (R : ℝ)) ≤ D * Real.log B → (S.card : ℝ) ≤ V * B →
      (Module.finrank F₂ (valueKernel S) : ℝ) ≤ ε * B := by
  obtain ⟨Bbudget, hbudget⟩ := PrimeFactorBudget.exceptional_budget d C₀
  obtain ⟨Brank, hrank⟩ := ResidualComponentRank.residual_rank_sublinear
    c D (CoverRankPrimeBudget.constant C₀ + 1) V ε hc hD hε
  refine ⟨max Bbudget Brank, ?_⟩
  intro B hB S H a b Ux Uy Rx Ry U R hBH hH ha hb hheight hRx hRy hS hlower hupper hR hU hlogU hlogR hcard
  apply hrank B ((le_max_right _ _).trans hB) S (exceptionalPrimes H a b) U R
  · exact rows_le_two_actual_cutoff ha hb hRx hRy hS
  · exact hlower
  · exact hupper
  · exact hR
  · exact hU
  · exact hlogU
  · exact hlogR
  · exact hbudget B ((le_max_left _ _).trans hB) H a b hBH hH ha hb hheight
  · exact hcard


theorem row_rank_sublinear (c D C₀ V ε : ℝ) (d : ℕ) (hc : 0 < c) (hD : 0 < D) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ S : Finset ℕ, ∀ H a b Ux Uy Rx Ry U R : ℕ,
      B ≤ H → (H : ℝ) ≤ C₀ * B → 0 < a → 0 < b → a * b ≤ B ^ d →
      Rx ≤ H → Ry ≤ H → S ⊆ progression a Ux Rx ∪ progression b Uy Ry →
      (∀ n ∈ S, U ≤ n) → (∀ n ∈ S, n ≤ U + R) →
      1 ≤ R → 2 * R ≤ U → c * B ≤ Real.log U →
      Real.log (64 * (R : ℝ)) ≤ D * Real.log B → (S.card : ℝ) ≤ V * B →
      (Module.finrank F₂ (CoverGraphResolution.rowSolutions (PrimeRowComponents.rows S (exceptionalPrimes H a b))) : ℝ) ≤ ε * B := by
  obtain ⟨Bbudget, hbudget⟩ := PrimeFactorBudget.exceptional_budget d C₀
  obtain ⟨Brank, hrank⟩ := ResidualComponentRank.row_rank_sublinear
    c D (CoverRankPrimeBudget.constant C₀ + 1) V ε hc hD hε
  refine ⟨max Bbudget Brank, ?_⟩
  intro B hB S H a b Ux Uy Rx Ry U R hBH hH ha hb hheight hRx hRy hS hlower hupper hR hU hlogU hlogR hcard
  apply hrank B ((le_max_right _ _).trans hB) S (exceptionalPrimes H a b) U R
  · exact rows_le_two_actual_cutoff ha hb hRx hRy hS
  · exact hlower
  · exact hupper
  · exact hR
  · exact hU
  · exact hlogU
  · exact hlogR
  · exact hbudget B ((le_max_left _ _).trans hB) H a b hBH hH ha hb hheight
  · exact hcard

end PaperP1.TwoProgressionSublinear
