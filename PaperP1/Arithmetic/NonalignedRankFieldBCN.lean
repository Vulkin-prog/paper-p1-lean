module

public import PaperP1.Arithmetic.IntegerCurveRationalization
public import PaperP1.Arithmetic.NonalignedRankLimsup

/-! # Nonaligned rank with the same field-polynomial BCN input as the degree count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedRankFieldBCN

open Filter PaperP1.FreeComponentRank PaperP1.NonalignedRankLimsup
  PaperP1.IntegerCurveRationalization

theorem critical_rank_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ PaperP1.Model.dyadicBlock N, ∀ y ∈ PaperP1.Model.dyadicBlock N,
      ¬ CompressedTargetAlignment.Aligned 1 x y L →
        (pairIntersectionRank x y L : ℝ) ≤
          ((2 / 3) * Real.log 2 + ε) * ((L + 1 : ℕ) : ℝ) :=
  NonalignedRankUnderBCN.critical_rank_bound c κ hc (integer_input_of_field_input c κ hBCN) ε hε C

theorem article_13_6_under_field_BCN (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) (L : ℕ → ℕ)
    (hband : ∀ᶠ N : ℕ in atTop, |(L N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Filter.limsup (fun N ↦ maximalRatio N (L N)) atTop ≤ (2 / 3) * Real.log 2 ∧
      (2 / 3 : ℝ) * Real.log 2 < 1 / 2 :=
  article_13_6_under_BCN c κ hc (integer_input_of_field_input c κ hBCN) C L hband

theorem uniform_half_window_gap (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) :
    ∃ σ : ℝ, (2 / 3) * Real.log 2 < σ ∧ σ < 1 / 2 ∧ ∀ C : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → maximalRatio N L ≤ σ :=
  NonalignedRankLimsup.uniform_half_window_gap c κ hc (integer_input_of_field_input c κ hBCN)

end PaperP1.NonalignedRankFieldBCN
