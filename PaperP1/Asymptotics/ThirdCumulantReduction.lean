module

public import PaperP1.Asymptotics.RepeatedRunCost
public import PaperP1.Asymptotics.IncompatibleTripleReduction

/-! # The actual third-cumulant error is reduced to the two remaining arithmetic activities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThirdCumulantReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.TripleActivityConnected
  PaperP1.ThirdRunFactorialCumulant PaperP1.IndependentTargetDeficit

theorem absolute_reduction (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
        0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3) ∧
        CompatibleActivitySplit.absolute L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3) ≤
          (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) + deficit G L := by
  obtain ⟨NR, hNR⟩ := IncompatibleTripleReduction.reduced_bound C ε hε
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  refine ⟨max NR NL, ?_⟩
  intro N hN L G hband hG hp
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  rw [absolute_comparison L hL (G.powersetCard 3) (fun I hI ↦ (mem_powersetCard.mp hI).2)
    (fun I hI x hx ↦ hp x ((mem_powersetCard.mp hI).1 hx))]
  exact ⟨sum_nonneg fun _ _ ↦ abs_nonneg _, hNR N (by omega) L G hband hG hp⟩

theorem cumulant_reduction (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
        |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| ≤
          (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) + 6 * deficit G L +
          12 * K / N * CompatibleActivitySplit.absolute L (G.powersetCard 2) + 2 * K ^ 3 / (N : ℝ) ^ 2 := by
  obtain ⟨K, hK, NM, hNM⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NI, hNI⟩ := IncompatibleTripleReduction.reduced_bound C (ε / 2) (by positivity)
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption 6 (-(3 : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨K, hK, max 1 (max NM (max NI (max NL NF))), ?_⟩
  intro N hN L G hband hG hp
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  have hI := hNI N (by omega) L G hband hG hp
  have hR := RepeatedRunCost.finite_bound hG (by omega) K hK.le
    (fun x hx ↦ (hNM N (by omega) L x hband (hG hx)).2)
  have hS := signed_comparison L hL (G.powersetCard 3) (fun I hI ↦ (mem_powersetCard.mp hI).2)
    (fun I hI x hx ↦ hp x ((mem_powersetCard.mp hI).1 hx))
  have hF : 6 * (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) := by
    convert hNF N (by omega) using 1
    congr 1
    ring
  rw [ThirdRunActivityComparison.exact_decomposition hG]
  have hid : 6 * CompatibleActivitySplit.signed L (G.powersetCard 3) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G -
      6 * positiveConnected L (G.powersetCard 3) =
      6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G := by ring
  rw [hid]
  have htriangle := abs_add_le
    (6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)))
    (RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G)
  have hsix : |6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3))| =
      6 * |CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)| := by
    rw [abs_mul]
    norm_num
  rw [hsix] at htriangle
  have hSI := mul_le_mul_of_nonneg_left (hS.trans hI) (by norm_num : (0 : ℝ) ≤ 6)
  nlinarith only [htriangle, hSI, hR, hF]

end PaperP1.ThirdCumulantReduction
