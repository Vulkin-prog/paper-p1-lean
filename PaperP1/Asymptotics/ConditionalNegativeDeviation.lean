module

public import PaperP1.Model.SourceConditionalDeviations
public import PaperP1.Model.SourceConditionalCountMean
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Model.LocalRigidityConsequences

/-! # Uniform negative conditional deviation after any fixed number of sources

This proves the negative-deviation and source-deletion part of companion
T2.7. Its positive-excess arithmetic estimate is a separate open task.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalNegativeDeviation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.SourceConditionalDeviations
  PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget PaperP1.FiniteChannelHierarchy

local instance conditionalNegativeDeviationDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_negative (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ dyadicBlock N → A.card ≤ j → 0 < infiniteJointMoment L A →
      negativeDeviation N L A ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NE, hNE, hcount⟩ := FixedWindowBranching.badStarts_card_critical C j (ε / 2) (by positivity)
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C)
    (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NE (max NG NF), by omega, ?_⟩
  intro N hN L hband A hA hj hq
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  calc
    _ ≤ (badStarts N L (rawValues A L)).card * (2 ^ L : ℝ)⁻¹ := finite_negative_bound hNtwo hL hA hq
    _ ≤ (N : ℝ) ^ (1 / 2 + ε / 2) * ((2 : ℝ) ^ C / N) :=
      mul_le_mul (hcount N (by omega) L hband A hA hj)
        (LocalRigidityConsequences.nominal_marginal_bound hNtwo hband)
        (by positivity) (Real.rpow_nonneg hn.le _)
    _ = (2 : ℝ) ^ C * (N : ℝ) ^ (-1 / 2 + ε / 2) := by
      rw [show -1 / 2 + ε / 2 = (1 / 2 + ε / 2) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_source_cost (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ A : Finset ℕ, A.card ≤ j →
      (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption ((j : ℝ) * (2 : ℝ) ^ C) (-1) ε hε
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband A hj
  calc
    _ ≤ (j : ℝ) * ((2 : ℝ) ^ C / N) :=
      mul_le_mul (by exact_mod_cast hj) (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband)
        (by positivity) (by positivity)
    _ = ((j : ℝ) * (2 : ℝ) ^ C) * (N : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]; ring
    _ ≤ _ := hfactor N (by omega)

theorem uniform_mean_lower (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ dyadicBlock N → A.card ≤ j → 0 < infiniteJointMoment L A →
      nominalMean N L - (N : ℝ) ^ (-1 / 2 + ε) ≤ freshMean N L A := by
  obtain ⟨NN, hNN, hnegative⟩ := uniform_negative C j (ε / 2) (by positivity)
  obtain ⟨NS, hNS, hsource⟩ := uniform_source_cost C j (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 2 (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NN (max NS NF), by omega, ?_⟩
  intro N hN L hband A hA hj hq
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hneg := hnegative N (by omega) L hband A hA hj hq
  have hsrc : (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 / 2 + ε / 2) :=
    (hsource N (by omega) L hband A hj).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hf : 2 * (N : ℝ) ^ (-1 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    convert hfactor N (by omega) using 1
    congr 1
    ring
  have hp := positive_nonneg N L A
  rw [mean_decomposition hA]
  linarith only [hneg, hsrc, hf, hp]

theorem uniform_weighted_negative (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ), ∀ w : Finset ℕ → ℝ,
      (∀ A ∈ F, A ⊆ dyadicBlock N ∧ A.card ≤ j ∧ 0 < infiniteJointMoment L A ∧ 0 ≤ w A) →
      (∑ A ∈ F, w A * negativeDeviation N L A) ≤
        (∑ A ∈ F, w A) * (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨N₀, hN₀, hnegative⟩ := uniform_negative C j ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F w hF
  rw [sum_mul]
  apply sum_le_sum
  intro A hA
  obtain ⟨hsub, hcard, hq, hw⟩ := hF A hA
  exact mul_le_mul_of_nonneg_left (hnegative N hN L hband A hsub hcard hq) hw

theorem uniform_normalized_negative (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ), ∀ w : Finset ℕ → ℝ,
      (∀ A ∈ F, A ⊆ dyadicBlock N ∧ A.card ≤ j ∧ 0 < infiniteJointMoment L A ∧ 0 ≤ w A) →
      0 < ∑ A ∈ F, w A →
      (∑ A ∈ F, w A * negativeDeviation N L A) / (∑ A ∈ F, w A) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨N₀, hN₀, hweighted⟩ := uniform_weighted_negative C j ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F w hF hmass
  exact (div_le_iff₀ hmass).mpr (by simpa only [mul_comm] using hweighted N hN L hband F w hF)

theorem uniform_conditional_expectation_lower (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ dyadicBlock N → A.card ≤ j → 0 < infiniteJointMoment L A →
      nominalMean N L - (N : ℝ) ^ (-1 / 2 + ε) ≤
        (∫ ω, if ω ∈ JointBranchingEvents.jointEvent A L then
          (infiniteStartCount (dyadicBlock N) L ω : ℝ) - A.card else 0
          ∂Model.InfiniteRademacher.infiniteRademacherMeasure) /
            Model.InfiniteRademacher.infiniteRademacherMeasure.real (JointBranchingEvents.jointEvent A L) := by
  obtain ⟨NM, hNM, hmean⟩ := uniform_mean_lower C j ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NM NG, by omega, ?_⟩
  intro N hN L hband A hA hj hq
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  rw [← SourceConditionalCountMean.freshMean_eq_full_minus_source_integral N L A hL hA]
  exact hmean N (by omega) L hband A hA hj hq

end PaperP1.ConditionalNegativeDeviation
