module

public import PaperP1.Asymptotics.SharpPairTargetDeficitUnderInputs
public import PaperP1.Asymptotics.ThirdCumulantReduction

/-! # Sharp absolute incompatible activity and third-cumulant comparison under explicit geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpThirdCancellationUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.TripleActivityConnected
  PaperP1.ThirdRunFactorialCumulant

theorem connected_activity_eq (G : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    CompatibleActivitySplit.absolute L (G.powersetCard 3) =
      CompatibleActivitySplit.absolute L (ConnectedWindowFamilies.connectedFamilies G L 3) := by
  classical
  symm
  apply sum_subset (filter_subset _ _)
  intro T hT hnot
  have hconn : ¬ ConnectedWindowFamilies.Connected L T := fun h ↦ hnot (mem_filter.mpr ⟨hT, h⟩)
  have hc := coefficient_zero_of_disconnected L hL T (mem_powersetCard.mp hT).2
    (fun x hx ↦ hp x ((mem_powersetCard.mp hT).1 hx)) hconn
  rw [hc, abs_zero]

theorem uniform_cancellation (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 2048)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∀ x ∈ G, 0 < infiniteMarginal x L) →
        (CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-3 / 2 + ε) ∧
        0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3) ∧
        CompatibleActivitySplit.absolute L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3) ≤
          (N : ℝ) ^ (-3 / 2 + ε) ∧
        |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| ≤ (N : ℝ) ^ (-3 / 2 + ε) ∧
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
          (N : ℝ) ^ (-5 / 3 + ε))) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, he⟩ := SharpPairTargetDeficitUnderInputs.article_11_1 C (ε / 4) (by positivity)
  rw [show (ε / 4) / 512 = ε / 2048 by ring] at he
  obtain ⟨NI, hi⟩ := IncompatibleTripleReduction.reduced_bound C (ε / 4) (by positivity)
  obtain ⟨K, hK, NR, hr⟩ := RepeatedRunCost.uniform_bound C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (12 * K + 2 * K ^ 3)
    (-5 / 3 + ε / 4) (ε / 4) (by positivity)
  obtain ⟨N2, h2⟩ := HalfCountSchedule.factor_absorption 2 (-3 / 2 + ε / 4) (ε / 4) (by positivity)
  obtain ⟨N7, h7⟩ := HalfCountSchedule.factor_absorption 7 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NE, _hNE, he⟩ := he hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NE (max NI (max NR (max NG (max NF (max N2 N7)))))), by omega, ?_⟩
  intro N hN L hband G hG hp
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hest := he N (by omega) L hband G hG
  have hincompat : CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    have hfinite := hi N (by omega) L G hband hG hp
    calc
      _ ≤ 2 * (N : ℝ) ^ (-3 / 2 + ε / 4) := by linarith only [hfinite, hest.1]
      _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 4) + ε / 4) := h2 N (by omega)
      _ = _ := by congr 1; ring
  have hrepeat : |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    have hfinite := hr N (by omega) L G hband hG
    have hid : 12 * K / N * (N : ℝ) ^ (-2 / 3 + ε / 4) =
        12 * K * (N : ℝ) ^ (-5 / 3 + ε / 4) := by
      rw [show -5 / 3 + ε / 4 = (-2 / 3 + ε / 4) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    have htwo : 2 * K ^ 3 / (N : ℝ) ^ 2 ≤ 2 * K ^ 3 * (N : ℝ) ^ (-5 / 3 + ε / 4) := by
      rw [div_eq_mul_inv, ← Real.rpow_two, ← Real.rpow_neg hn.le]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) (by positivity)
    calc
      _ ≤ 12 * K / N * (N : ℝ) ^ (-2 / 3 + ε / 4) + 2 * K ^ 3 / (N : ℝ) ^ 2 :=
        hfinite.trans (add_le_add (mul_le_mul_of_nonneg_left hest.2 (by positivity)) le_rfl)
      _ ≤ (12 * K + 2 * K ^ 3) * (N : ℝ) ^ (-5 / 3 + ε / 4) := by rw [hid]; linarith only [htwo]
      _ ≤ (N : ℝ) ^ ((-5 / 3 + ε / 4) + ε / 4) := hf N (by omega)
      _ = _ := by congr 1; ring
  have hrepeat' : |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := hrepeat.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith))
  have hgap := absolute_comparison L hL (G.powersetCard 3)
    (fun T hT ↦ (mem_powersetCard.mp hT).2)
    (fun T hT x hx ↦ hp x ((mem_powersetCard.mp hT).1 hx))
  have hs := signed_comparison L hL (G.powersetCard 3)
    (fun T hT ↦ (mem_powersetCard.mp hT).2)
    (fun T hT x hx ↦ hp x ((mem_powersetCard.mp hT).1 hx))
  have hcum : |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| ≤
      (N : ℝ) ^ (-3 / 2 + ε) := by
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
          |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := by rw [abs_mul]; norm_num
      _ ≤ 7 * (N : ℝ) ^ (-3 / 2 + ε / 2) := by linarith only [hs, hincompat, hrepeat']
      _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := h7 N (by omega)
      _ = _ := by congr 1; ring
  have hfinal : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-3 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
  refine ⟨hincompat.trans hfinal, ?_, ?_, hcum, hrepeat.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))⟩
  · rw [hgap]
    exact sum_nonneg fun _ _ ↦ abs_nonneg _
  · rw [hgap]
    exact hincompat.trans hfinal

end PaperP1.SharpThirdCancellationUnderInputs
