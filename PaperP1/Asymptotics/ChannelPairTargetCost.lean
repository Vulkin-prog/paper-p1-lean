module

public import PaperP1.Model.PairTargetCost
public import PaperP1.Asymptotics.CompressedChannelTargetCount
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Asymptotics.IndependentTargetMass
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Sharp actual pair/independent-target cost for every fixed private channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelPairTargetCost

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PairTargetCost
  PaperP1.FiniteAlignedChannelCover

theorem uniform_channel (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L) ≤
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := CompressedChannelTargetCount.uniform_count a b ha hab.le C (ε / 3) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := PrivateChannelActivityRate.uniform_coefficient C (ε / 3) a b ha hab hcop (by positivity)
  obtain ⟨K, hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K
    (-2 + 1 / (b : ℝ) + 2 * ε / 3) (ε / 3) (by positivity)
  refine ⟨max 2 (max NC (max NW (max NM NF))), by omega, ?_⟩
  intro N hN L H hband
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount : ((events (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L)).card : ℝ) ≤
      (N : ℝ) ^ (1 + ε / 3) :=
    (show ((events (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L)).card : ℝ) ≤
      (CompressedChannelTargetHosts.allTargets N a b L).card by exact_mod_cast private_events_card N H a b L).trans
      (hc N (by omega) L hband)
  rw [mass_eq_events]
  calc
    _ ≤ ∑ _p ∈ events (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L),
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 3) * (K / N) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨he, hz⟩ := mem_product.mp (mem_filter.mp hp).1
      exact mul_le_mul (hw N (by omega) L H hband p.1 he) (hm N (by omega) L p.2 hband hz).2
        (MissingBlockProbabilities.infiniteMarginal_nonneg p.2 L) (by positivity)
    _ = ((events (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L)).card : ℝ) *
        ((N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 3) * (K / N)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + ε / 3) * ((N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 3) * (K / N)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = K * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + 2 * ε / 3) := by
      rw [show -2 + 1 / (b : ℝ) + 2 * ε / 3 =
        ((1 + ε / 3) + (-2 + 1 / (b : ℝ) + ε / 3)) - 1 by ring,
        Real.rpow_sub hn, Real.rpow_one,
        Real.rpow_add hn (1 + ε / 3) (-2 + 1 / (b : ℝ) + ε / 3)]
      ring
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) + 2 * ε / 3) + ε / 3) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_private_union (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass (dyadicBlock N) L (privatePairs Q N H L) ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  have heach (ab : ℕ × ℕ) (hab : ab ∈ channels Q) : ∀ᶠ N : ℕ in atTop, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass (dyadicBlock N) L (PrivateChannelActivity.pairs N H ab.1 ab.2 L) ≤
        (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    obtain ⟨ha, hlt, _hint, hcop, hb, _hbQ⟩ := channel_data hab
    obtain ⟨N₀, _hN₀, hu⟩ := uniform_channel ab.1 ab.2 ha hlt hcop C (ε / 2) (by positivity)
    refine eventually_atTop.mpr ⟨max 2 N₀, ?_⟩
    intro N hN L H hband
    have hinv : 1 / (ab.2 : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb)
    exact (hu N (by omega) L H hband).trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [hinv]))
  obtain ⟨NE, he⟩ := eventually_atTop.mp ((Finset.eventually_all (channels Q)).mpr heach)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((channels Q).card : ℝ)
    (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NE NF), by omega, ?_⟩
  intro N hN L H hband
  calc
    _ ≤ ∑ ab ∈ channels Q, mass (dyadicBlock N) L (PrivateChannelActivity.pairs N H ab.1 ab.2 L) :=
      GraphStarWeights.sum_biUnion_le_nonneg (channels Q) _ (cost (dyadicBlock N) L)
        (cost_nonneg (dyadicBlock N) L)
    _ ≤ ∑ _ab ∈ channels Q, (N : ℝ) ^ (-5 / 3 + ε / 2) :=
      sum_le_sum fun ab hab ↦ he N (by omega) ab hab L H hband
    _ = ((channels Q).card : ℝ) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((-5 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_restricted_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      F ⊆ (dyadicBlock N).powersetCard 2 →
      mass (dyadicBlock N) L F ≤ CompatibleActivitySplit.absolute L F * (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NM, hm⟩ := IndependentTargetMass.uniform_mass 2 C ε hε
  refine ⟨max 2 NM, by omega, ?_⟩
  intro N hN L hband F hF
  unfold mass cost CompatibleActivitySplit.absolute
  rw [sum_mul]
  apply sum_le_sum
  intro e he
  obtain ⟨heN, hecard⟩ := mem_powersetCard.mp (hF he)
  exact mul_le_mul_of_nonneg_left
    (hm N (by omega) L (dyadicBlock N) e hband (subset_refl _) heN hecard) (abs_nonneg _)

end PaperP1.ChannelPairTargetCost
