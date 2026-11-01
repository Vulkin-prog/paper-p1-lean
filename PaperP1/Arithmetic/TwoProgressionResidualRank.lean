module

public import PaperP1.Arithmetic.TwoProgressionPrimeRows

/-! # The finite residual-rank estimate on a true subset of two progressions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoProgressionResidualRank

open Finset PaperP1.Arithmetic PaperP1.TwoProgressionPrimeRows PaperP1.FiniteResidualRank

theorem finite_rank_bound {S : Finset ℕ} {H a b Ux Uy Rx Ry U R K t : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hRx : Rx ≤ H) (hRy : Ry ≤ H)
    (hS : S ⊆ progression a Ux Rx ∪ progression b Uy Ry)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t) :
    Module.finrank F₂ (valueKernel S) <
      max ((exceptionalPrimes H a b).card + 1)
        (2 * t * 2 ^ (((exceptionalPrimes H a b).card + 1) / t + 1)) + S.card / (K + 1) := by
  exact FiniteResidualRank.finite_rank_bound (rows_le_two_actual_cutoff ha hb hRx hRy hS)
    hlower hupper hR hU hgrowth ht

theorem cardinal_budget {S : Finset ℕ} {a b Ux Uy Rx Ry : ℕ}
    (hS : S ⊆ progression a Ux Rx ∪ progression b Uy Ry) : S.card ≤ Rx + Ry + 2 := by
  have hcard := card_le_card hS
  have hunion := card_union_le (progression a Ux Rx) (progression b Uy Ry)
  have hleft : (progression a Ux Rx).card ≤ Rx + 1 := by
    exact card_image_le.trans (by simp only [Nat.card_Icc]; omega)
  have hright : (progression b Uy Ry).card ≤ Ry + 1 := by
    exact card_image_le.trans (by simp only [Nat.card_Icc]; omega)
  omega

end PaperP1.TwoProgressionResidualRank
