module

public import PaperP1.Asymptotics.PairActivityUnderBCN
public import PaperP1.Asymptotics.CriticalActualMean
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform decay of the exact second cumulant under the common BCN input

The estimate concerns the original count and every deterministic restriction.
It does not assert the sharper channel asymptotic or positivity of the cumulant.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondCumulantUnderBCN

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousRunConversion
  PaperP1.HeterogeneousBernoulli PaperP1.PairActivityHostCap PaperP1.PairActivityUnderBCN
  PaperP1.CountObservables

theorem diagonal_bound {N L : ℕ} (hN : 0 < N) {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    {K : ℝ} (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ K / N) :
    powerSum G (fun x ↦ infiniteMarginal x L) 2 ≤ K ^ 2 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : (G.card : ℝ) ≤ N := by
    exact_mod_cast (card_le_card hG).trans_eq (dyadicBlock_card N)
  calc
    _ ≤ ∑ _x ∈ G, (K / N) ^ 2 := sum_le_sum (fun x hx ↦
      pow_le_pow_left₀ (marginal_bounds x L).1 (hcap x hx) 2)
    _ = (G.card : ℝ) * (K / N) ^ 2 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (K / N) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by field_simp

theorem uniform_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NA, hNA, hactivity⟩ := uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨K, hK, NM, hmarg⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (K ^ 2 + 2) (-1 / 2 + η) η hη
  refine ⟨max NA (max NM NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag := diagonal_bound (by omega : 0 < N) hG
    (fun x hx ↦ (hmarg N (by omega) L x hband (hG hx)).2)
  have hd : powerSum G (fun x ↦ infiniteMarginal x L) 2 ≤
      K ^ 2 * (N : ℝ) ^ (-1 / 2 + η) := by
    calc
      _ ≤ K ^ 2 / N := hdiag
      _ = K ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (sq_nonneg K)
  calc
    _ ≤ 2 * absoluteMass G L + powerSum G (fun x ↦ infiniteMarginal x L) 2 :=
      second_cumulant_absolute_bound hG
    _ ≤ 2 * (N : ℝ) ^ (-1 / 2 + η) + K ^ 2 * (N : ℝ) ^ (-1 / 2 + η) :=
      add_le_add (mul_le_mul_of_nonneg_left (hactivity N (by omega) L hband G hG) (by norm_num)) hd
    _ = (K ^ 2 + 2) * (N : ℝ) ^ (-1 / 2 + η) := by ring
    _ ≤ (N : ℝ) ^ ((-1 / 2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_eventually_small (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤ δ := by
  obtain ⟨NA, hNA, hbound⟩ := uniform_bound c κ hc hBCN C (1 / 4) (by norm_num)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨NT, htail⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hδ))
  refine ⟨max NA NT, by omega, ?_⟩
  intro N hN L hband G hG
  have h := hbound N (by omega) L hband G hG
  norm_num only [show -(1 : ℝ) / 2 + 1 / 4 = -(1 / 4) by ring] at h
  exact h.trans (htail N (by omega)).le

theorem uniform_parameter_gap (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L| ≤
          countMoment (dyadicBlock N) L 1 / 2 ∧
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L <
          countMoment (dyadicBlock N) L 1 := by
  have hmean : 0 < CriticalActualMean.lowerMean C := CriticalActualMean.lowerMean_pos C
  obtain ⟨NA, hNA, hsmall⟩ := uniform_eventually_small c κ hc hBCN C
    (CriticalActualMean.lowerMean C / 4) (by positivity)
  obtain ⟨NM, hNM, hmeanbound⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨max NA NM, by omega, ?_⟩
  intro N hN L hband
  have ha := hsmall N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hm := (hmeanbound N (by omega) L hband).1
  have hh := le_abs_self (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)
  constructor <;> linarith only [hmean, ha, hm, hh]

end PaperP1.SecondCumulantUnderBCN
