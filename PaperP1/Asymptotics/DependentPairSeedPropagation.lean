module

public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Model.DependentPairJointActivity

/-! # Any actual dependent-pair activity propagates positively to every fixed containing order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairSeedPropagation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ), F ⊆ DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2 →
      ∀ T : Finset (Finset ℕ),
      (∀ I ∈ T, I ⊆ dyadicBlock N ∧ I.card = 2 + k ∧ ∃ D ∈ F, D ⊆ I) →
      (∑ I ∈ T, infiniteJointMoment L I) ≤
        (2 * ((2 + k).factorial : ℝ)) * (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L F := by
  obtain ⟨N₀, hp⟩ := UnorderedSeedMassPropagation.uniform_mass 2 (by decide) k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL hband F hF T hT
  have hdata (D : Finset ℕ) (hD : D ∈ F) : D ⊆ dyadicBlock N ∧ D.card = 2 :=
    mem_powersetCard.mp (mem_filter.mp (hF hD)).1
  have hseed : (∑ D ∈ F, infiniteJointMoment L D) ≤ 2 * CompatibleActivitySplit.absolute L F := by
    calc
      _ ≤ ∑ D ∈ F, 2 * |infiniteCenteredCoefficient L D| := by
        apply sum_le_sum
        intro D hD
        exact DependentPairJointActivity.pointwise L hL D (hdata D hD).2 (mem_filter.mp (hF hD)).2
      _ = _ := by
        change _ = 2 * ∑ D ∈ F, |infiniteCenteredCoefficient L D|
        rw [mul_sum]
  calc
    _ ≤ ((2 + k).factorial : ℝ) * (N : ℝ) ^ ε * ∑ D ∈ F, infiniteJointMoment L D :=
      hp N hN L hL hband F hdata T hT
    _ ≤ ((2 + k).factorial : ℝ) * (N : ℝ) ^ ε * (2 * CompatibleActivitySplit.absolute L F) :=
      mul_le_mul_of_nonneg_left hseed (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = _ := by ring

end PaperP1.DependentPairSeedPropagation
