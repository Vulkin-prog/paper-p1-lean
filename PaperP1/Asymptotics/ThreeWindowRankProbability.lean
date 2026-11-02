module

public import PaperP1.Model.ThreeNormalizedFamilyRank
public import PaperP1.Asymptotics.BinaryRankPowers

/-! # A finite canonical-cardinality bound and the actual merged kernel control joint probability -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeWindowRankProbability

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateNormalizedFamilies

theorem upper {N L : ℕ} {C α d η : ℝ} (hN : 2 ≤ N) (hL : 0 < L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (hαη : 0 ≤ α - η)
    (c X : Fin 3 → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hcan : α * L - d ≤ (((valueUnion c X L).card - 1 : ℕ) : ℝ))
    (hdef : (Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion c X L)) : ℝ) ≤ η * (L + 1)) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      BinaryRankPowers.constant C (α - η) (d + 2 + η) * (N : ℝ) ^ (-(α - η)) := by
  let S := valueUnion c X L
  let R := Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂))
  have hcard := ThreeNormalizedFamilyRank.card_le_rank_add_kernel (L := L) c X hc hX
  have hcardR : (S.card : ℝ) ≤ (R : ℝ) + Module.finrank F₂ (FiniteResidualRank.valueKernel S) + 3 := by
    exact_mod_cast hcard
  have hSpos : 1 ≤ S.card := card_pos.mpr ((NormalizedWindowSets.normalized_nonempty (c 0) (X 0) L).mono
    (normalized_subset c X L 0))
  rw [Nat.cast_sub hSpos, Nat.cast_one] at hcan
  have hR : (α - η) * L - (d + 2 + η) ≤ (R : ℝ) := by nlinarith only [hcardR, hcan, hdef]
  exact (NormalizedFamilyDefectRank.actual_joint_le_rank X hL).trans (BinaryRankPowers.upper hN hαη hband hR)

end PaperP1.ThreeWindowRankProbability
