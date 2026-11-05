module

public import PaperP1.Asymptotics.FiniteGoodPartition
public import PaperP1.Asymptotics.ChannelPairTargetCost

/-! # The literal sharp independent-target deficit without unproved inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpPairTargetDeficit

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PairTargetCost
  PaperP1.FiniteGoodChannelPartition PaperP1.FiniteAlignedChannelCover

theorem article_11_1 (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (IndependentTargetDeficit.deficit G L ≤ (N : ℝ) ^ (-3 / 2 + ε) ∧
          HeterogeneousRunConversion.absoluteMass G L ≤ (N : ℝ) ^ (-2 / 3 + ε)) := by
  obtain ⟨Q, _hQ, hp⟩ := FiniteGoodPartition.companion_T7_1 (ε / 8) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := hp C (ε / 4) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := ChannelPairTargetCost.uniform_restricted_mass C (ε / 8) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := ChannelPairTargetCost.uniform_private_union Q C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NP (max NT (max NG NF))), by omega, ?_⟩
  intro N hN L hband G hG
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpartition := hp N (by omega) L hband
  have hweaksub : weak Q N (2 * Q * (L + 1)) L ⊆ (dyadicBlock N).powersetCard 2 := by
    intro e he
    exact (mem_filter.mp (mem_inter.mp (mem_sdiff.mp he).1).1).1
  have hexsub : exceptional Q N (2 * Q * (L + 1)) L ⊆ (dyadicBlock N).powersetCard 2 := by
    intro e he
    exact (mem_filter.mp (mem_sdiff.mp he).1).1
  have hcost (F : Finset (Finset ℕ)) (hF : F ⊆ (dyadicBlock N).powersetCard 2)
      (hA : CompatibleActivitySplit.absolute L F ≤ (N : ℝ) ^ (-1 + ε / 8 + ε / 4)) :
      mass (dyadicBlock N) L F ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    calc
      _ ≤ CompatibleActivitySplit.absolute L F * (N : ℝ) ^ (-1 / 2 + ε / 8) := ht N (by omega) L hband F hF
      _ ≤ (N : ℝ) ^ (-1 + ε / 8 + ε / 4) * (N : ℝ) ^ (-1 / 2 + ε / 8) :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hweak := hcost _ hweaksub hpartition.1
  have hex := hcost _ hexsub (hpartition.2.1.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])))
  have hgood : mass (dyadicBlock N) L (good Q N (2 * Q * (L + 1)) L) ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    have hsub : good Q N (2 * Q * (L + 1)) L ⊆ privatePairs Q N (2 * Q * (L + 1)) L :=
      fun _ he ↦ (mem_filter.mp he).2.2
    exact (mass_mono hsub).trans ((hg N (by omega) L (2 * Q * (L + 1)) hband).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)))
  have hformula := partition_formula Q N (2 * Q * (L + 1)) L
  have hfull : IndependentTargetDeficit.deficit (dyadicBlock N) L ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    calc
      _ ≤ 3 * (N : ℝ) ^ (-3 / 2 + ε / 2) := by linarith only [hformula, hgood, hweak, hex]
      _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring
  exact ⟨(deficit_mono hG L).trans hfull,
    (hpartition.2.2.1 G hG).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))⟩

end PaperP1.SharpPairTargetDeficit
