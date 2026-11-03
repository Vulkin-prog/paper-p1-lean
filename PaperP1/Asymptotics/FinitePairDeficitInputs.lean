module

public import PaperP1.Asymptotics.FixedPairExtensionDeficitUnderInputs
public import PaperP1.Asymptotics.FiniteGoodPartitionUnderInputs

/-! # A finite explicit bundle of the existing geometric inputs for pair deficit closure -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePairDeficitInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

structure Parameters where
  sourceDegree : ℕ
  sourceRadicals : ℕ
  ordinaryTwoRadicals : ℕ
  ordinaryThreeRadicals : ℕ
  sourceDegree_pos : 0 < sourceDegree

structure Hypotheses (p : Parameters) (K : ℕ) : Prop where
  source : UniformSourceSurfaceCover.UniformCover p.sourceRadicals K p.sourceDegree
  ordinaryTwo : UniformOrdinarySurfaceCover.UniformCover p.ordinaryTwoRadicals 2
  ordinaryThree : UniformOrdinarySurfaceCover.UniformCover p.ordinaryThreeRadicals 3
  sourceCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound ((p.sourceDegree + 2).choose 2 + p.sourceRadicals) M
  ordinaryTwoCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.ordinaryTwoRadicals + 3) M
  ordinaryThreeCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.ordinaryThreeRadicals + 3) M

theorem fixed_order (k : ℕ) (hk : 1 ≤ k) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        FixedPairExtensions.deficit G L k ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨D, j, j₁, j₂, hD, h⟩ := FixedPairExtensionDeficitUnderInputs.article_15_7 k hk C ε hε
  refine ⟨⟨D, j, j₁, j₂, hD⟩, ?_⟩
  intro hp
  exact h hp.source hp.ordinaryTwo hp.ordinaryThree hp.sourceCurves hp.ordinaryTwoCurves hp.ordinaryThreeCurves

theorem finite_orders (s : ℕ) (u C ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) :
    ∃ p : Fin s → Parameters,
      (∀ i, Hypotheses (p i) (GeneralGraphHostCount.sizeCap (ε / 4096))) →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ k ∈ Ico 1 s, u ^ k * FixedPairExtensions.deficit G L k) ≤
          (∑ k ∈ Ico 1 s, u ^ k) * (N : ℝ) ^ (-3 / 2 + ε) := by
  have hper (i : Fin s) := fixed_order (i.val + 1) (by omega) C ε hε
  choose p hp using hper
  refine ⟨p, ?_⟩
  intro hgeo
  have hthreshold (i : Fin s) := hp i (hgeo i)
  choose N₀ hN₀ hh using hthreshold
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
      ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 128)) →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
          |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
          CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak Q N (2 * Q * (L + 1)) L) ≤
            (N : ℝ) ^ (-1 + η + ε) ∧
          CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.exceptional Q N (2 * Q * (L + 1)) L) ≤
            (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Q, hQ, h⟩ := FiniteGoodPartitionUnderInputs.companion_T7_1 η hη
  refine ⟨Q, hQ, ?_⟩
  intro C ε hε
  obtain ⟨D, j, j₁, j₂, hD, hp⟩ := h C ε hε
  refine ⟨⟨D, j, j₁, j₂, hD⟩, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh⟩ := hp hgeo.source hgeo.ordinaryTwo hgeo.ordinaryThree
    hgeo.sourceCurves hgeo.ordinaryTwoCurves hgeo.ordinaryThreeCurves
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact ⟨(hh N hN L hband).1, (hh N hN L hband).2.1⟩

end PaperP1.FinitePairDeficitInputs
