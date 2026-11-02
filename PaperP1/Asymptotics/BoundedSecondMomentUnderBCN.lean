module

public import PaperP1.Model.SecondMomentPairCap
public import PaperP1.Asymptotics.JointFamilyProbabilityUnderBCN
public import PaperP1.Asymptotics.OriginalPairHosts

/-! # A bounded actual second factorial moment from the same explicit BCN input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedSecondMomentUnderBCN

open Finset PaperP1.Model PaperP1.FactorialCountMoments

def seedConstant (C : ℝ) : ℝ := ((2 : ℝ) ^ C) ^ 2 + 1

theorem seedConstant_gt_one (C : ℝ) : 1 < seedConstant C := by
  have hp : 0 < (2 : ℝ) ^ C := Real.rpow_pos_of_pos (by norm_num) C
  unfold seedConstant
  nlinarith only [sq_pos_of_pos hp]

theorem uniform_bound (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        factorialCountMoment (dyadicBlock N) L 2 ≤ seedConstant C := by
  obtain ⟨NH, hNHtwo, hhosts⟩ := OriginalPairHosts.uniform_count C (1 / 8) (by norm_num)
  obtain ⟨NP, hpairs⟩ := JointFamilyProbabilityUnderBCN.uniform_pair_probability
    c κ hc hBCN C (1 / 8) (by norm_num)
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NH (max NP NG), ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hfinite := SecondMomentPairCap.finite_bound hNtwo hL
    (Real.rpow_nonneg hn.le (-3 / 2 + 1 / 8))
    (fun x hx y hy hxy ↦ hpairs N (by omega) L x y hband hx hy hxy)
  have hhost := hhosts N (by omega) L hband
  have hmass : ((PairHostCover.hosts N L).card : ℝ) * (N : ℝ) ^ (-3 / 2 + 1 / 8 : ℝ) ≤ 1 := by
    calc
      _ ≤ (N : ℝ) ^ (1 + 1 / 8 : ℝ) * (N : ℝ) ^ (-3 / 2 + 1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hhost (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (-1 / 4 : ℝ) := by rw [← Real.rpow_add hn]; norm_num
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn₁ (by norm_num)
  have hnom := LocalRigidityConsequences.nominal_marginal_bound hNtwo hband
  have hnp : (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (2 : ℝ) ^ C := by
    simpa only [mul_comm] using (le_div_iff₀ hn).mp hnom
  have hsquare : (N : ℝ) ^ 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ C) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ) * (2 ^ L : ℝ)⁻¹) hnp 2
  exact hfinite.trans (add_le_add hsquare hmass)

end PaperP1.BoundedSecondMomentUnderBCN
