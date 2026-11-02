module

public import PaperP1.Asymptotics.CoarsePrimitiveJointMassUnderBCN
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.RetainedModifiedLaw

/-! # Uniform vanishing of the actual retained-modification error under explicit BCN

The truncation order is chosen after the final tolerance and before N.
Only finitely many fixed-order primitive estimates are assembled. This
proves convergence to zero, not the source N^(-4/5+epsilon) rate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedBadProbabilityUnderBCN

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveActiveSeeds PaperP1.HeterogeneousDirectMaximum PaperP1.RetainedCountCylinder

theorem uniform_badProbability (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ H : ℝ, badProbability H N L G ≤ ε := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * M / ε)
  let K := max 2 J
  have hJK : J ≤ K := le_max_right _ _
  have hKM : 2 * M / ε < (K : ℝ) := hJ.trans_le (by exact_mod_cast hJK)
  have htail : M / (K + 1 : ℕ) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (K + 1 : ℕ))).mpr
    have hmul := (div_lt_iff₀ hε).mp hKM
    push_cast
    nlinarith only [hmul, hε]
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NQ, _hNQ, hmass⟩ := CoarsePrimitiveJointMassUnderBCN.uniform_finite_orders K c κ hc hBCN C (1 / 4) (by norm_num)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption
    (2 * ((K + 1 : ℕ) : ℝ) / ε) (-1 / 4) (1 / 4) (by norm_num)
  refine ⟨max NM (max NQ NF), by omega, ?_⟩
  intro N hN L hband G hG H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmG : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L :=
        sum_le_sum_of_subset_of_nonneg hG (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ M := (hmean N (by omega) L hband).2
  have hfrac : actualMean G L / (K + 1 : ℕ) ≤ ε / 2 :=
    (div_le_div_of_nonneg_right hmG (by positivity)).trans htail
  have hf := hfactor N (by omega)
  norm_num only [show (-1 / 4 : ℝ) + 1 / 4 = 0 by ring, Real.rpow_zero] at hf
  have hbudget : ((K + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 / 4 : ℝ) ≤ ε / 2 := by
    have hs := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ ε / 2)
    have hid : (ε / 2) * (2 * ((K + 1 : ℕ) : ℝ) / ε) = ((K + 1 : ℕ) : ℝ) := by
      calc
        _ = ((K + 1 : ℕ) : ℝ) * (ε / ε) := by ring
        _ = _ := by rw [div_self hε.ne', mul_one]
    rw [← mul_assoc, hid, mul_one] at hs
    simpa only [neg_div] using hs
  have hcard : ((Icc 2 K).card : ℝ) ≤ (K + 1 : ℕ) := by
    exact_mod_cast (show (Icc 2 K).card ≤ K + 1 by rw [Nat.card_Icc]; omega)
  have hsum : (∑ r ∈ Icc 2 K, jointMass G L r) ≤ ε / 2 := by
    calc
      _ ≤ ∑ _r ∈ Icc 2 K, (N : ℝ) ^ (-1 / 4 : ℝ) := by
        apply sum_le_sum
        intro r hr
        simpa only [show (-1 / 2 : ℝ) + 1 / 4 = -1 / 4 by ring] using
          hmass N (by omega) L hband G hG r hr
      _ = ((Icc 2 K).card : ℝ) * (N : ℝ) ^ (-1 / 4 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((K + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hn.le _)
      _ ≤ _ := hbudget
  calc
    _ ≤ actualMean G L / (K + 1 : ℕ) + ∑ r ∈ Icc 2 K, jointMass G L r :=
      PrimitiveActiveSeeds.badProbability_bound H N L G K
    _ ≤ ε / 2 + ε / 2 := add_le_add hfrac hsum
    _ = _ := by ring

theorem uniform_totalVariation (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ H : ℝ, AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw G L)
        (RetainedModifiedLaw.law H N L G) ≤ ε := by
  obtain ⟨N₀, hN₀, hbad⟩ := uniform_badProbability c κ hc hBCN C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG H
  exact (RetainedModifiedLaw.coupling H N L G).trans (hbad N hN L hband G hG H)

end PaperP1.RetainedBadProbabilityUnderBCN
