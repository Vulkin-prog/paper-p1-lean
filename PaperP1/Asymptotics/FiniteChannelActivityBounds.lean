module

public import PaperP1.Model.FiniteAlignedChannelCover
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Uniform actual activity and point weights in every fixed finite channel family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteChannelActivityBounds

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteAlignedChannelCover

theorem uniform_bounds (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (CompatibleActivitySplit.absolute L (privatePairs Q N (2 * Q * (L + 1)) L) ≤
        (N : ℝ) ^ (-2 / 3 + ε) ∧
      CompatibleActivitySplit.absolute L (defectivePairs Q N (2 * Q * (L + 1)) L) ≤
        (N : ℝ) ^ (-1 + ε) ∧
      ∀ ab ∈ channels Q, ∀ e ∈ PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L,
        |infiniteCenteredCoefficient L e| ≤ (N : ℝ) ^ (-2 + 1 / (ab.2 : ℝ) + ε)) := by
  have heach (ab : ℕ × ℕ) (hab : ab ∈ channels Q) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L) ≤
        (N : ℝ) ^ (-2 / 3 + ε / 2) ∧
      CompatibleActivitySplit.absolute L (NormalizedDefectPairActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L) ≤
        (N : ℝ) ^ (-1 + ε / 2) ∧
      ∀ e ∈ PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L,
        |infiniteCenteredCoefficient L e| ≤ (N : ℝ) ^ (-2 + 1 / (ab.2 : ℝ) + ε)) := by
    obtain ⟨ha, hlt, hint, hcop, hb, hbQ⟩ := channel_data hab
    obtain ⟨NP, _hNP, hp⟩ := PrivateChannelActivityRate.uniform_activity C (ε / 2) (2 * Q)
      ab.1 ab.2 ha hlt hint hcop (by positivity)
    obtain ⟨ND, _hND, hd⟩ := NormalizedDefectPairActivity.uniform_activity C (ε / 2) (2 * Q)
      ab.1 ab.2 ha hlt hcop (by positivity)
    obtain ⟨NW, _hNW, hw⟩ := PrivateChannelActivityRate.uniform_coefficient C ε ab.1 ab.2 ha hlt hcop hε
    refine eventually_atTop.mpr ⟨max 2 (max NP (max ND NW)), ?_⟩
    intro N hN L hband
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hcut : 2 * ab.2 * (L + 1) ≤ 2 * Q * (L + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hbQ)
    have hinv : 1 / (ab.2 : ℝ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb)
    refine ⟨(hp N (by omega) L (2 * Q * (L + 1)) hband hcut le_rfl).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hinv])),
      (hd N (by omega) L (2 * Q * (L + 1)) hband hcut le_rfl).trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hinv])), ?_⟩
    exact hw N (by omega) L (2 * Q * (L + 1)) hband
  obtain ⟨NE, he⟩ := eventually_atTop.mp ((Finset.eventually_all (channels Q)).mpr heach)
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption ((channels Q).card : ℝ)
    (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨ND, hd⟩ := HalfCountSchedule.factor_absorption ((channels Q).card : ℝ)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NE (max NP ND)), by omega, ?_⟩
  intro N hN L hband
  refine ⟨?_, ?_, fun ab hab ↦ (he N (by omega) ab hab L hband).2.2⟩
  · calc
      _ ≤ ∑ ab ∈ channels Q, CompatibleActivitySplit.absolute L
          (PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L) :=
        GraphStarWeights.sum_biUnion_le_nonneg (channels Q) _
          (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)
      _ ≤ ∑ _ab ∈ channels Q, (N : ℝ) ^ (-2 / 3 + ε / 2) :=
        sum_le_sum fun ab hab ↦ (he N (by omega) ab hab L hband).1
      _ = ((channels Q).card : ℝ) * (N : ℝ) ^ (-2 / 3 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hp N (by omega)
      _ = _ := by congr 1; ring
  · calc
      _ ≤ ∑ ab ∈ channels Q, CompatibleActivitySplit.absolute L
          (NormalizedDefectPairActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L) :=
        GraphStarWeights.sum_biUnion_le_nonneg (channels Q) _
          (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)
      _ ≤ ∑ _ab ∈ channels Q, (N : ℝ) ^ (-1 + ε / 2) :=
        sum_le_sum fun ab hab ↦ (he N (by omega) ab hab L hband).2.1
      _ = ((channels Q).card : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hd N (by omega)
      _ = _ := by congr 1; ring

end PaperP1.FiniteChannelActivityBounds
