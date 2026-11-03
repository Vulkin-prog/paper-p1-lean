module

public import PaperP1.Asymptotics.SubpowerFixedCountMoments
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Algebra.ElementarySymmetricBound

/-! # Full actual absolute pair activity is subpolynomial without geometric or BCN assumptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubpowerPairAbsoluteActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) ≤ (N : ℝ) ^ ε := by
  let M := 2 * (2 : ℝ) ^ C
  obtain ⟨NJ, _hNJ, hj⟩ := SubpowerFixedCountMoments.uniform_joint_mass 2 C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 + M ^ 2 / 2) (ε / 2) (ε / 2) (by positivity)
  refine ⟨2 + NJ + NM + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hμ : 0 ≤ actualMean G L := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment Subset.rfl
      _ ≤ _ := (hm N (by omega) L hband).2
  have hindep : SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G 2 ≤ M ^ 2 / 2 := by
    apply (ElementarySymmetricBound.elementary_le_power_div _
      (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) G 2).trans
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hμ hμM 2) (by norm_num)
  have hlarge : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ N by omega)) (by positivity)
  calc
    _ ≤ (∑ e ∈ G.powersetCard 2, infiniteJointMoment L e) +
        SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G 2 := by
      rw [SubsetPowerSums.elementary, ← sum_add_distrib]
      apply sum_le_sum
      intro e he
      rw [CompressedJointMoments.centered_pair L e (mem_powersetCard.mp he).2]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (infiniteJointMoment_nonneg L e),
        abs_of_nonneg (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)])
    _ ≤ (N : ℝ) ^ (ε / 2) + M ^ 2 / 2 := add_le_add (hj N (by omega) L hband G hG) hindep
    _ ≤ (1 + M ^ 2 / 2) * (N : ℝ) ^ (ε / 2) := by
      have h := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ M ^ 2 / 2 by positivity)
      nlinarith only [h]
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.SubpowerPairAbsoluteActivity
