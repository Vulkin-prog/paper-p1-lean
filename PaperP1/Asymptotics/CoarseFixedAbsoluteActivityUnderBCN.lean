module

public import PaperP1.Asymptotics.DependentProductMass
public import PaperP1.Model.AbsoluteActivityDecomposition
public import PaperP1.Asymptotics.CoarseDependentFamilyMassUnderBCN

/-! # Absolute centered activity vanishes at every fixed positive order under BCN

This includes every dyadic subground, zero marginals and incompatible
families. The order is fixed before N. The source 4/5 exponent for connected
orders at least three and its separate contact bound remain open.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseFixedAbsoluteActivityUnderBCN

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DependentFamilySeeds
  PaperP1.HeterogeneousDirectMaximum PaperP1.ConnectedWindowFamilies

theorem uniform_dependent_orders (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ s ∈ range (r + 1), dependentMass G L s ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  have heach (s : ℕ) (_hs : s ∈ range (r + 1)) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      dependentMass G L s ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    obtain ⟨NS, _hNS, hS⟩ := CoarseDependentFamilyMassUnderBCN.uniform_dependent_mass s c κ hc hBCN C ε hε
    exact eventually_atTop.mpr ⟨NS, fun N hN ↦ hS N hN⟩
  obtain ⟨NF, hF⟩ := eventually_atTop.mp ((Finset.eventually_all (range (r + 1))).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband G hG s hs
  exact hF N (by omega) s hs L hband G hG

theorem uniform_absolute_activity (r : ℕ) (hr : 1 ≤ r) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let B : ℝ := (2 : ℝ) ^ r + ∑ s ∈ range (r + 1), M ^ (r - s) / ((r - s).factorial : ℝ)
  obtain ⟨NP, _hNP, hproduct⟩ := DependentProductMass.uniform_mass r C η hη
  obtain ⟨NQ, _hNQ, hmass⟩ := uniform_dependent_orders r c κ hc hBCN C η hη
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption B (-1 / 2 + η) η hη
  refine ⟨max NM (max NP (max NQ (max NG NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hμ : 0 ≤ actualMean G L := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hmean N (by omega) L hband).2
  let T := (N : ℝ) ^ (-1 / 2 + η)
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hp : DependentProductMass.mass G L r ≤ T :=
    (hproduct N (by omega) L hband G hG).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hsum : (∑ s ∈ range (r + 1), dependentMass G L s *
      (actualMean G L ^ (r - s) / ((r - s).factorial : ℝ))) ≤
      T * ∑ s ∈ range (r + 1), M ^ (r - s) / ((r - s).factorial : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro s hs
    exact mul_le_mul (hmass N (by omega) L hband G hG s hs)
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hμ hμM (r - s)) (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg hμ _) (Nat.cast_nonneg _)) hT
  calc
    _ ≤ (2 : ℝ) ^ r * DependentProductMass.mass G L r +
        ∑ s ∈ range (r + 1), dependentMass G L s *
          (actualMean G L ^ (r - s) / ((r - s).factorial : ℝ)) :=
      AbsoluteActivityDecomposition.absolute_power_bound G L r hL hr
    _ ≤ (2 : ℝ) ^ r * T + T * ∑ s ∈ range (r + 1), M ^ (r - s) / ((r - s).factorial : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) hsum
    _ = B * T := by dsimp [B]; ring
    _ ≤ (N : ℝ) ^ ((-1 / 2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_connected_activity (r : ℕ) (hr : 1 ≤ r) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ I ∈ connectedFamilies G L r, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  classical
  obtain ⟨N₀, hN₀, hbound⟩ := uniform_absolute_activity r hr c κ hc hBCN C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun I _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))).trans
    (hbound N hN L hband G hG)

end PaperP1.CoarseFixedAbsoluteActivityUnderBCN
