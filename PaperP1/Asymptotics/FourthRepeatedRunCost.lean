module

public import PaperP1.Model.FourthRunRemainder
public import PaperP1.Asymptotics.FullFixedActivity
public import PaperP1.Asymptotics.PairActivity
public import PaperP1.Asymptotics.CriticalActualMean

/-! # Coarse third activity suffices for a rate-two fourth-cumulant repeated-index remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthRepeatedRunCost

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |FourthRunRemainder.remainder G L| ≤ (N : ℝ) ^ (-2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨N3, _hN3, ht⟩ := FullFixedActivity.uniform_range 3 C η hη
  obtain ⟨N2, _hN2, hpair⟩ := PairActivity.uniform_pair_activity C η hη
  obtain ⟨NP, _hNP, hcap⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (72 * K + 72 * K ^ 2 + 6 * K ^ 4)
    (-2 + η) η hη
  refine ⟨max NM (max N3 (max N2 (max NP NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp (x : ℕ) (hx : x ∈ G) : infiniteMarginal x L ≤ K / N :=
    hcap N (by omega) L hband x (hG hx)
  have htriple : CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-1 + η) := by
    change (∑ I ∈ G.powersetCard 3, |infiniteCenteredCoefficient L I|) ≤ _
    exact ht N (by omega) L hband 3 (by norm_num) le_rfl G hG
  have hm : actualMean G L ≤ K := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hmean N (by omega) L hband).2
  have hfirst : 72 * (K / N) * (N : ℝ) ^ (-1 + η) = 72 * K * (N : ℝ) ^ (-2 + η) := by
    rw [show -2 + η = (-1 + η) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
    ring
  have hsecond : 72 * (K / N) ^ 2 * (N : ℝ) ^ (-2 / 3 + η) ≤
      72 * K ^ 2 * (N : ℝ) ^ (-2 + η) := by
    calc
      _ = 72 * K ^ 2 * (N : ℝ) ^ (-8 / 3 + η) := by
        rw [show -8 / 3 + η = (-2 / 3 + η) - 2 by ring, Real.rpow_sub hn, Real.rpow_two, div_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity)
  have hthird : 6 * (K / N) ^ 3 * actualMean G L ≤ 6 * K ^ 4 * (N : ℝ) ^ (-2 + η) := by
    calc
      _ ≤ 6 * (K / N) ^ 3 * K := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 6 * K ^ 4 * (N : ℝ) ^ (-3 : ℝ) := by
        rw [Real.rpow_neg hn.le, Real.rpow_ofNat (N : ℝ) 3, div_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hη])) (by positivity)
  have hf := FourthRunRemainder.finite_bound hG (K / N) (by positivity) hp
  calc
    _ ≤ 72 * (K / N) * (N : ℝ) ^ (-1 + η) +
        72 * (K / N) ^ 2 * (N : ℝ) ^ (-2 / 3 + η) + 6 * (K / N) ^ 3 * actualMean G L :=
      hf.trans (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left htriple (by positivity))
        (mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity))) le_rfl)
    _ ≤ (72 * K + 72 * K ^ 2 + 6 * K ^ 4) * (N : ℝ) ^ (-2 + η) := by
      rw [hfirst]
      nlinarith only [hsecond, hthird]
    _ ≤ (N : ℝ) ^ ((-2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.FourthRepeatedRunCost
