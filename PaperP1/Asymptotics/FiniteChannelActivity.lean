module

public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Any fixed finite union of good channels has the sharp coarse pair exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteChannelActivity

open Finset Filter PaperP1.Model.InfiniteStarts PaperP1.PrivateChannelActivity

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (F : Finset (ℕ × ℕ)) (N H L : ℕ) : Finset (Finset ℕ) :=
  F.biUnion fun ab ↦ PrivateChannelActivity.pairs N H ab.1 ab.2 L

theorem uniform_activity (F : Finset (ℕ × ℕ)) (C ε : ℝ) (D : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ 3 ≤ ab.2)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ ab ∈ F, 2 * ab.2 * (L + 1) ≤ H) → H ≤ D * (L + 1) →
      CompatibleActivitySplit.absolute L (pairs F N H L) ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  have heach (ab : ℕ × ℕ) (hab : ab ∈ F) : ∀ᶠ N : ℕ in atTop, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * ab.2 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N H ab.1 ab.2 L) ≤
        (N : ℝ) ^ (-1 + 1 / (ab.2 : ℝ) + ε / 2) := by
    obtain ⟨ha, hablt, hinterior, hcop, _⟩ := hF ab hab
    obtain ⟨N₀, _hN₀, hN₀⟩ := PrivateChannelActivityRate.uniform_activity C (ε / 2) D ab.1 ab.2
      ha hablt hinterior hcop (by positivity)
    exact eventually_atTop.mpr ⟨N₀, fun N hN ↦ hN₀ N hN⟩
  obtain ⟨NF, hf⟩ := eventually_atTop.mp ((Finset.eventually_all F).mpr heach)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (F.card : ℝ) (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NF NA), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ ∑ ab ∈ F, CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N H ab.1 ab.2 L) :=
      GraphStarWeights.sum_biUnion_le_nonneg F (fun ab ↦ PrivateChannelActivity.pairs N H ab.1 ab.2 L)
        (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)
    _ ≤ ∑ _ab ∈ F, (N : ℝ) ^ (-2 / 3 + ε / 2) := by
      apply sum_le_sum
      intro ab hab
      apply (hf N (by omega) ab hab L H hband (hcut ab hab) hH).trans
      apply Real.rpow_le_rpow_of_exponent_le hn1
      have hinv : 1 / (ab.2 : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num)
        (by exact_mod_cast (hF ab hab).2.2.2.2)
      linarith only [hinv]
    _ = (F.card : ℝ) * (N : ℝ) ^ (-2 / 3 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FiniteChannelActivity
