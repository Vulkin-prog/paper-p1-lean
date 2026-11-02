module

public import PaperP1.Model.ContactCenteredTruncation
public import PaperP1.Asymptotics.ContactSeedMass
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The actual positive contact seed kernel costs N^(-1+epsilon), without BCN -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactSeedKernel

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum
  PaperP1.ContactCenteredTruncation

theorem uniform_joint_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ e ∈ ClosePairs.pairs G L, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NJ, hj⟩ := ContactSeedMass.forward_sum C δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2) (-1 + δ) δ hδ
  refine ⟨max 2 (max NJ (max NG NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hsum : (∑ x ∈ dyadicBlock N, infiniteJointMoment L {x, x + L}) ≤
      ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 + δ) := by
    simpa only [dyadicBlock, ContactFamilySeeds.prescribed_contact L hL] using
      hj N (by omega) L hband (fun _ ↦ Affine.startRhs L)
  calc
    _ ≤ ∑ x ∈ G, infiniteJointMoment L {x, x + L} := ContactFamilySeeds.joint_sum_bound G L hL
    _ ≤ ∑ x ∈ dyadicBlock N, infiniteJointMoment L {x, x + L} :=
      sum_le_sum_of_subset_of_nonneg hG (fun x _ _ ↦ infiniteJointMoment_nonneg L {x, x + L})
    _ ≤ _ := hsum
    _ ≤ (N : ℝ) ^ ((-1 + δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

theorem uniform_independent_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ e ∈ ClosePairs.pairs G L, ∏ x ∈ e, infiniteMarginal x L) ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NL, hl⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow CriticalBandScale.upperScale 1 δ hδ
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (K ^ 2) (-1 + δ) δ hδ
  refine ⟨max 2 (max NP (max NM (max NS (max NL NF)))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpow : (L : ℝ) ≤ (N : ℝ) ^ δ := by
    have hle : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    exact hle.trans ((hs N (by omega) L hband).2.trans
      (by simpa only [Real.rpow_one] using hl N (by omega)))
  have hmean : actualMean G L ≤ K := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hm N (by omega) L hband).2
  calc
    _ ≤ (L : ℝ) * (K / N) * actualMean G L := ClosePairs.independent_weight_bound G L
      (fun x ↦ infiniteMarginal x L) (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      (K / N) (by positivity) (fun x hx ↦ hp N (by omega) L hband x (hG hx))
    _ ≤ (L : ℝ) * (K / N) * K := mul_le_mul_of_nonneg_left hmean (by positivity)
    _ ≤ (N : ℝ) ^ δ * (K / N) * K := by
      have h := mul_le_mul_of_nonneg_right hLpow (mul_nonneg (div_nonneg hK hn.le) hK)
      simpa only [mul_assoc] using h
    _ = K ^ 2 * (N : ℝ) ^ (-1 + δ) := by
      rw [show -1 + δ = δ - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

theorem uniform_kernel (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      seedKernel G L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NJ, _hNJ, hj⟩ := uniform_joint_mass C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := uniform_independent_mass C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NJ (max NP NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hJ := hj N (by omega) L hband G hG
  have hP := hp N (by omega) L hband G hG
  have heq : seedKernel G L = (∑ e ∈ ClosePairs.pairs G L, infiniteJointMoment L e) +
      3 * ∑ e ∈ ClosePairs.pairs G L, ∏ x ∈ e, infiniteMarginal x L := by
    rw [seedKernel, sum_add_distrib, mul_sum]
  calc
    _ ≤ 4 * (N : ℝ) ^ (-1 + ε / 2) := by rw [heq]; linarith only [hJ, hP]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.ContactSeedKernel
