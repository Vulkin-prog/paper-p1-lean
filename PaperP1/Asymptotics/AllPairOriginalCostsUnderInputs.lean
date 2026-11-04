module

public import PaperP1.Asymptotics.AllPairResidualMassUnderInputs
public import PaperP1.Model.AllPairCountMeans
public import PaperP1.Probability.WeightedPoissonNorm

/-! # Actual distribution, mean and weighted recurrence costs in T19.14 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairOriginalCostsUnderInputs

open MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AllPairResidualMass
  PaperP1.AllPairOriginalLaws PaperP1.AllPairCountMeans PaperP1.AtomicProbability

theorem finite_weighted_cost {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H M : ℝ)
    (hM : goodMean H N L ≤ M) :
    |WeightedPoissonNorm.weightedNorm (goodLaw H N L) (goodMean H N L) -
      WeightedPoissonNorm.weightedNorm (allLaw N L) (allMean N L)| ≤ (4 + 2 * M) * tau H N L := by
  have hc := original_cost hN hL H
  have hs := WeightedPoissonNorm.weightedNorm_stability_bounded (goodLaw H N L) (allLaw N L)
    (goodMean H N L) (allMean N L) M (goodMean_nonneg H N L) hM
  have hgap : |goodMean H N L - allMean N L| ≤ 2 * tau H N L := by
    have h0 : 0 ≤ goodMean H N L - allMean N L := hc.2.1
    rw [abs_of_nonneg h0]
    exact hc.2.2
  have hM0 : 0 ≤ M := (goodMean_nonneg H N L).trans hM
  have hscale := mul_le_mul_of_nonneg_left hc.1 (by positivity : 0 ≤ 2 * (1 + M))
  linarith only [hs, hgap, hscale]

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 512)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let H : ℝ := (8 * (L + 1) : ℕ)
        totalVariation (goodLaw H N L) (allLaw N L) + |goodMean H N L - allMean N L| +
          |WeightedPoissonNorm.weightedNorm (goodLaw H N L) (goodMean H N L) -
            WeightedPoissonNorm.weightedNorm (allLaw N L) (allMean N L)| ≤
              (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := AllPairResidualMassUnderInputs.uniform_tau C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let K : ℝ := 7 + 2 * M
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 256 = ε / 512 := by ring
  obtain ⟨NT, _hNT, ht⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NM + NG + NF + NT, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let H : ℝ := (8 * (L + 1) : ℕ)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hM : goodMean H N L ≤ M := (goodMean_le_original H N L).trans (hm N (by omega) L hband).2
  have hc := original_cost (by omega : 2 ≤ N) hL H
  have hw := finite_weighted_cost (by omega : 2 ≤ N) hL H M hM
  have hgap : |goodMean H N L - allMean N L| ≤ 2 * tau H N L := by
    have h0 : 0 ≤ goodMean H N L - allMean N L := hc.2.1
    rw [abs_of_nonneg h0]
    exact hc.2.2
  have htotal : totalVariation (goodLaw H N L) (allLaw N L) + |goodMean H N L - allMean N L| +
      |WeightedPoissonNorm.weightedNorm (goodLaw H N L) (goodMean H N L) -
        WeightedPoissonNorm.weightedNorm (allLaw N L) (allMean N L)| ≤ K * tau H N L := by
    dsimp only [K]
    linarith only [hc.1, hgap, hw]
  have hK : 0 ≤ K := by dsimp only [K, M]; positivity
  apply htotal.trans
  apply (mul_le_mul_of_nonneg_left (ht N (by omega) L hband) hK).trans
  convert hf N (by omega) using 1
  congr 1
  ring

end PaperP1.AllPairOriginalCostsUnderInputs
