module

public import PaperP1.Model.PrimitiveActiveSeeds
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.JointFamilyProbabilityUnderBCN

/-! # A common vanishing bound for every fixed primitive order under explicit BCN

The two-site branch uses BCN. Orders at least three use the unconditional
fixed-order primitive estimate. A finite order cutoff is fixed before N.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarsePrimitiveJointMassUnderBCN

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveActiveSeeds

theorem uniform_pair_mass (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L 2 ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  classical
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NC, hcount⟩ := OriginalWindowFamilyCounts.uniform_hosts 2 (by decide) C η hη
  obtain ⟨NP, hprob⟩ := JointFamilyProbabilityUnderBCN.uniform_family_probability c κ hc hBCN C η hη
  refine ⟨max 2 (max NC NP), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := (hcount N (by omega) L G hband hG).2
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hcard
  calc
    _ ≤ ∑ _I ∈ primitiveFamilies G L 2, (N : ℝ) ^ (-3 / 2 + η) := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hIG, hsize⟩ := mem_powersetCard.mp (mem_filter.mp hI).1
      exact hprob N (by omega) L hband I (hIG.trans hG) (by omega)
    _ = ((primitiveFamilies G L 2).card : ℝ) * (N : ℝ) ^ (-3 / 2 + η) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + η) * (N : ℝ) ^ (-3 / 2 + η) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [η]; ring

theorem uniform_mass (r : ℕ) (hr : 2 ≤ r) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  by_cases hr2 : r = 2
  · subst r
    exact uniform_pair_mass c κ hc hBCN C ε hε
  · obtain ⟨NP, hprob⟩ := PrimitiveGeneralMass.actual_joint_submass r hr C ε hε
    refine ⟨max 2 NP, by omega, ?_⟩
    intro N hN L hband G hG
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
    exact (hprob N (by omega) L G (primitiveFamilies G L r) hband hG (subset_refl _)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hrR]))

theorem uniform_finite_orders (K : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ r ∈ Icc 2 K, jointMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  have heach (r : ℕ) (hr : r ∈ Icc 2 K) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    obtain ⟨NR, _hNR, hR⟩ := uniform_mass r (mem_Icc.mp hr).1 c κ hc hBCN C ε hε
    exact eventually_atTop.mpr ⟨NR, fun N hN ↦ hR N hN⟩
  obtain ⟨NF, hF⟩ := eventually_atTop.mp ((Finset.eventually_all (Icc 2 K)).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband G hG r hr
  exact hF N (by omega) r hr L hband G hG

end PaperP1.CoarsePrimitiveJointMassUnderBCN
