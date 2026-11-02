module

public import PaperP1.Asymptotics.CoarseThirdCumulantUnderBCN
public import PaperP1.Asymptotics.ThirdCumulantReduction

/-! # Coarse independent-target and incompatible-triple bounds

The exponent 1 is weaker than the source exponent 3/2. These intermediate
results retain the actual deficit and both signs of incompatible activity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseIncompatibleTripleUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.TripleActivityConnected
  PaperP1.ThirdRunFactorialCumulant

theorem uniform_deficit (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      IndependentTargetDeficit.deficit G L ≤ (N : ℝ) ^ (-1 + ε) := by
  have hη : 0 < ε / 2 := by positivity
  obtain ⟨ND, hdeficit⟩ := IndependentTargetMass.deficit_bound C (ε / 2) hη
  obtain ⟨NA, hNA, hpair⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C (ε / 2) hη
  refine ⟨max ND NA, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ CompatibleActivitySplit.absolute L (G.powersetCard 2) * (N : ℝ) ^ (-1 / 2 + ε / 2) :=
      hdeficit N (by omega) L G hband hG
    _ ≤ (N : ℝ) ^ (-1 / 2 + ε / 2) * (N : ℝ) ^ (-1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hpair N (by omega) L hband G hG) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_incompatible (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
      CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-1 + ε) := by
  have hη : 0 < ε / 2 := by positivity
  obtain ⟨ND, hND, hdeficit⟩ := uniform_deficit c κ hc hBCN C (ε / 2) hη
  obtain ⟨NI, hincompatible⟩ := IncompatibleTripleReduction.reduced_bound C (ε / 2) hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) hη
  refine ⟨max ND (max NI NF), by omega, ?_⟩
  intro N hN L hband G hG hp
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hi := hincompatible N (by omega) L G hband hG hp
  have hd := hdeficit N (by omega) L hband G hG
  have he : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  calc
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hi, hd, he]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_activity_comparison (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
      0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3) ∧
      CompatibleActivitySplit.absolute L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NI, hNI, hincompatible⟩ := uniform_incompatible c κ hc hBCN C ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NI NG, by omega, ?_⟩
  intro N hN L hband G hG hp
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  rw [absolute_comparison L hL (G.powersetCard 3) (fun I hI ↦ (mem_powersetCard.mp hI).2)
    (fun I hI x hx ↦ hp x ((mem_powersetCard.mp hI).1 hx))]
  exact ⟨sum_nonneg fun _ _ ↦ abs_nonneg _, hincompatible N (by omega) L hband G hG hp⟩

theorem uniform_cumulant_comparison (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
      |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| ≤
        (N : ℝ) ^ (-1 + ε) := by
  have hη : 0 < ε / 2 := by positivity
  obtain ⟨NI, hNI, hincompatible⟩ := uniform_incompatible c κ hc hBCN C (ε / 2) hη
  obtain ⟨NR, hNR, hrepeat⟩ := CoarseThirdCumulantUnderBCN.uniform_repeated_cost c κ hc hBCN C (ε / 2) hη
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 7 (-1 + ε / 2) (ε / 2) hη
  refine ⟨max NI (max NR (max NG NF)), by omega, ?_⟩
  intro N hN L hband G hG hp
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hi := hincompatible N (by omega) L hband G hG hp
  have hr : |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      (N : ℝ) ^ (-1 + ε / 2) :=
    (hrepeat N (by omega) L hband G hG).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hs := signed_comparison L hL (G.powersetCard 3)
    (fun I hI ↦ (mem_powersetCard.mp hI).2)
    (fun I hI x hx ↦ hp x ((mem_powersetCard.mp hI).1 hx))
  rw [ThirdRunActivityComparison.exact_decomposition hG]
  have hid : 6 * CompatibleActivitySplit.signed L (G.powersetCard 3) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G -
      6 * positiveConnected L (G.powersetCard 3) =
      6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G := by ring
  rw [hid]
  calc
    _ ≤ |6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3))| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := abs_add_le _ _
    _ = 6 * |CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := by
      rw [abs_mul]; norm_num
    _ ≤ 7 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hs, hi, hr]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.CoarseIncompatibleTripleUnderBCN
