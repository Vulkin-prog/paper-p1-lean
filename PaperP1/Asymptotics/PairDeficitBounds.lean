module

public import PaperP1.Asymptotics.FixedPairExtensionDeficit
public import PaperP1.Asymptotics.FiniteGoodPartition

/-! # Unconditional fixed and finite-order pair deficits and partition bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairDeficitBounds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem fixed_order (k : ℕ) (hk : 1 ≤ k) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      FixedPairExtensions.deficit G L k ≤ (N : ℝ) ^ (-3 / 2 + ε) :=
  FixedPairExtensionDeficit.article_15_7 k hk C ε hε

theorem finite_orders (s : ℕ) (u C ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ k ∈ Ico 1 s, u ^ k * FixedPairExtensions.deficit G L k) ≤
          (∑ k ∈ Ico 1 s, u ^ k) * (N : ℝ) ^ (-3 / 2 + ε) := by
  have hper (i : Fin s) := fixed_order (i.val + 1) (by omega) C ε hε
  choose N₀ hN₀ hh using hper
  refine ⟨3 + univ.sup N₀, by omega, ?_⟩
  intro N hN L hband G hG
  rw [sum_mul]
  apply sum_le_sum
  intro k hk
  let i : Fin s := ⟨k - 1, by have h := (mem_Ico.mp hk).2; omega⟩
  have hNi : N₀ i ≤ univ.sup N₀ := le_sup (f := N₀) (mem_univ i)
  have hki : i.val + 1 = k := by have h := (mem_Ico.mp hk).1; dsimp [i]; omega
  have hbound := hh i N (by omega) L hband G hG
  rw [hki] at hbound
  exact mul_le_mul_of_nonneg_left hbound (pow_nonneg hu k)

theorem partition_inputs (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, 3 ≤ Q ∧ ∀ C ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
          |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
          CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak Q N (2 * Q * (L + 1)) L) ≤
            (N : ℝ) ^ (-1 + η + ε) ∧
          CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.exceptional Q N (2 * Q * (L + 1)) L) ≤
            (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Q, hQ, h⟩ := FiniteGoodPartition.companion_T7_1 η hη
  refine ⟨Q, hQ, ?_⟩
  intro C ε hε
  obtain ⟨N₀, hN₀, hh⟩ := h C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact ⟨(hh N hN L hband).1, (hh N hN L hband).2.1⟩

end PaperP1.PairDeficitBounds
