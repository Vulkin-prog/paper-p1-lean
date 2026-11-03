module

public import PaperP1.Asymptotics.RelationCoreIndependentBudget
public import PaperP1.Model.PrimitiveRankAmplification
public import PaperP1.Model.PrimitiveActualMass

/-! # Every large ten-core below two ranks has actual mass of power 3/2 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeTenCoreMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.WeightedPrimitiveMass PaperP1.RelationCoreWitnesses

theorem uniform_rank (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Core 10 L I ∧
        relativeNullityOn (fun x ↦ squareClassSpace x L) I ≤ 2 * L) →
      rankMass F L u ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := PaperP1.RelationCoreIndependentBudget.uniform_ten
    u C (ε / 2) hu (by positivity)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    (((2 : ℝ) ^ C) ^ 2) (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NB + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hamp : ∀ I ∈ F,
      (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) ≤ ((2 : ℝ) ^ L) ^ 2 := by
    intro I hI
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hF I hI).2.2.2
    simpa only [Nat.mul_comm 2 L, pow_mul] using h
  have hindep := hb N (by omega) L hband F (by
    intro I hI
    exact ⟨(hF I hI).1, (hF I hI).2.1, (hF I hI).2.2.1⟩)
  have hword := PaperP1.CriticalChannelPowers.word_upper (by omega : 2 ≤ N) hband
  have hwordSquare : ((2 : ℝ) ^ L) ^ 2 ≤ ((2 : ℝ) ^ C * N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hword 2
  calc
    _ ≤ ((2 : ℝ) ^ L) ^ 2 * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L :=
      PaperP1.PrimitiveRankAmplification.mass_bound F L u _ hu.le hamp
    _ ≤ ((2 : ℝ) ^ C * N) ^ 2 * (N : ℝ) ^ (-7 / 2 + ε / 2) :=
      mul_le_mul hwordSquare hindep
        (sum_nonneg fun I _ ↦ prod_nonneg fun x _ ↦
          mul_nonneg hu.le (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L))
        (by positivity)
    _ = ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) := by
      conv_rhs =>
        rw [show (-3 : ℝ) / 2 + ε / 2 = 2 + (-7 / 2 + ε / 2) by ring,
          Real.rpow_add hn, Real.rpow_two]
      ring
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_actual (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Core 10 L I ∧
        relativeNullityOn (fun x ↦ squareClassSpace x L) I ≤ 2 * L) →
      actualMass F L u ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_rank u C (ε / 2) hu (by positivity)
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C 12 (by norm_num)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    2 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NR + NF + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hne : ∀ I ∈ F, I.Nonempty := by
    intro I hI
    have hsize := (hF I hI).2.1
    exact card_pos.mp (by omega)
  calc
    _ ≤ 2 * rankMass F L u := PaperP1.PrimitiveActualMass.actual_le_rank F L (by omega) u hu.le hne
    _ ≤ 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hr N (by omega) L hband F hF) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.LargeTenCoreMass
