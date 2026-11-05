module

public import PaperP1.Arithmetic.NormalizedPairRankLoss
public import PaperP1.Model.RegularSetAsymptotic

/-! # The full source pair loss includes at most two local defect dimensions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalPairLossComparison

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedPairRankLoss
  PaperP1.FreeComponentRank

local instance primeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem finite_bound (x y L : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hrx : Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (hry : Module.finrank F₂ (WindowRelationCode.windowRelationCode (y - 1) (L + 1)) ≤ 1) :
    pairLoss x y L ≤ pairIntersectionRank x y L + 2 ∧ pairLoss x y L ≤ L + 2 := by
  have hxrank := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hx
  have hyrank := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hy
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have hi : pairIntersectionRank x y L ≤ Module.finrank F₂ (squareClassSpace x L) :=
    Submodule.finrank_mono inf_le_left
  unfold pairLoss pairIntersectionRank at *
  omega

theorem uniform_bound (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
      pairLoss x y L ≤ pairIntersectionRank x y L + 2 ∧ pairLoss x y L ≤ L + 2 := by
  obtain ⟨NR, hr⟩ := RegularSetAsymptotic.dyadic_critical_relation_rank_le_one C
  refine ⟨max 2 NR, by omega, ?_⟩
  intro N hN L hband x hx y hy
  exact finite_bound x y L (by have hh := (Finset.mem_Ico.mp hx).1; omega)
    (by have hh := (Finset.mem_Ico.mp hy).1; omega)
    (hr N (by omega) L hband x hx) (hr N (by omega) L hband y hy)

end PaperP1.CriticalPairLossComparison
