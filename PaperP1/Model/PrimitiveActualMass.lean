module

public import PaperP1.Model.WeightedPrimitiveMass
public import PaperP1.Model.PositiveMarginalRestriction

/-! # Actual primitive rank comparisons including zero-marginal sites -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveActualMass

open Finset PaperP1.Model.InfiniteStarts PaperP1.WeightedPrimitiveMass

theorem centered_le_weight (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : I.Nonempty) :
    |infiniteCenteredCoefficient L I| ≤ PaperP1.PrimitiveWindowMass.weight L I := by
  classical
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · exact PaperP1.PrimitiveWindowMass.centered_le_weight L hL I hI hp
  · push Not at hp
    obtain ⟨x, hx, hnot⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hnot
      (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    rw [PaperP1.PositiveMarginalRestriction.zero_centered L I x hx hz, abs_zero]
    exact PaperP1.PrimitiveWindowMass.weight_nonneg L I

theorem actual_le_rank (F : Finset (Finset ℕ)) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (hF : ∀ I ∈ F, I.Nonempty) : actualMass F L u ≤ 2 * rankMass F L u := by
  rw [rankMass, mul_sum]
  apply sum_le_sum
  intro I hI
  have hq := PaperP1.PrimitiveWindowMass.joint_le_weight L hL I
  have hc := centered_le_weight L hL I (hF I hI)
  have h := mul_le_mul_of_nonneg_left (show infiniteJointMoment L I + |infiniteCenteredCoefficient L I| ≤
    2 * PaperP1.PrimitiveWindowMass.weight L I by linarith only [hq, hc]) (pow_nonneg hu I.card)
  exact h.trans_eq (by ring)

end PaperP1.PrimitiveActualMass
