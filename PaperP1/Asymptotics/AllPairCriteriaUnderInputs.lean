module

public import PaperP1.Asymptotics.AllPairOriginalCostsUnderInputs
public import PaperP1.Asymptotics.CriticalPairNegligible

/-! # Uniform equivalence of the actual all-pair and erased Poisson criteria -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairCriteriaUnderInputs

open PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AllPairOriginalLaws
  PaperP1.AllPairCountMeans PaperP1.AtomicProbability PaperP1.CriticalPairNegligible

def goodResidual (N L : ℕ) : ℝ := WeightedPoissonNorm.weightedNorm
  (goodLaw (8 * (L + 1) : ℕ) N L) (goodMean (8 * (L + 1) : ℕ) N L)

def allResidual (N L : ℕ) : ℝ := WeightedPoissonNorm.weightedNorm (allLaw N L) (allMean N L)

def goodPoissonDistance (N L : ℕ) : ℝ := totalVariation (goodLaw (8 * (L + 1) : ℕ) N L)
  (WeightedPoissonNorm.poisson (goodMean (8 * (L + 1) : ℕ) N L)
    (goodMean_nonneg (8 * (L + 1) : ℕ) N L))

theorem goodResidual_nonneg (N L : ℕ) : 0 ≤ goodResidual N L := WeightedRecurrence.l1_nonneg _

theorem allResidual_nonneg (N L : ℕ) : 0 ≤ allResidual N L := WeightedRecurrence.l1_nonneg _

theorem goodPoissonDistance_nonneg (N L : ℕ) : 0 ≤ goodPoissonDistance N L := totalVariation_nonneg _ _

theorem uniform_poisson_comparison (C : ℝ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      goodResidual N L ≤ A * goodPoissonDistance N L ∧
        goodPoissonDistance N L ≤ B * goodResidual N L := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨2 * (1 + M), Real.exp M, by positivity, (Real.exp_pos _).le, 10 + NM, by omega, ?_⟩
  intro N hN L hband
  let H : ℝ := (8 * (L + 1) : ℕ)
  let μ := goodMean H N L
  have hμ : 0 ≤ μ := goodMean_nonneg H N L
  have hμM : μ ≤ M := (goodMean_le_original H N L).trans (hm N (by omega) L hband).2
  have hc := WeightedPoissonNorm.poisson_comparison_nonnegative (goodLaw H N L) μ hμ
  have htv0 := goodPoissonDistance_nonneg N L
  have hv0 := goodResidual_nonneg N L
  constructor
  · have hcoef : 2 * (1 + μ) * goodPoissonDistance N L ≤
        2 * (1 + M) * goodPoissonDistance N L := mul_le_mul_of_nonneg_right (by linarith only [hμM]) htv0
    exact hc.2.trans hcoef
  · have hs := mul_le_mul_of_nonneg_left hc.1 (Real.exp_pos μ).le
    have he : Real.exp μ * Real.exp (-μ) = 1 := by rw [← Real.exp_add]; simp
    rw [← mul_assoc, he, one_mul] at hs
    have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hμM) hv0
    exact hs.trans hb

theorem good_criterion_iff (C : ℝ) :
    Negligible C goodResidual ↔ Negligible C goodPoissonDistance := by
  obtain ⟨A, B, hA, hB, N₀, _hN₀, h⟩ := uniform_poisson_comparison C
  constructor
  · intro hv
    apply of_abs_le C B hB goodResidual goodPoissonDistance hv
    exact ⟨N₀, fun N hN L hband ↦ by
      rw [abs_of_nonneg (goodPoissonDistance_nonneg N L), abs_of_nonneg (goodResidual_nonneg N L)]
      exact (h N hN L hband).2⟩
  · intro hp
    apply of_abs_le C A hA goodPoissonDistance goodResidual hp
    exact ⟨N₀, fun N hN L hband ↦ by
      rw [abs_of_nonneg (goodResidual_nonneg N L), abs_of_nonneg (goodPoissonDistance_nonneg N L)]
      exact (h N hN L hband).1⟩

theorem uniform_criterion_iff (C : ℝ) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 15360)) →
      Negligible C (fun N L ↦ goodResidual N L - allResidual N L) ∧
        (Negligible C allResidual ↔ Negligible C goodResidual) ∧
        (Negligible C allResidual ↔ Negligible C goodPoissonDistance) := by
  obtain ⟨p, hp⟩ := AllPairOriginalCostsUnderInputs.uniform_bound C (1 / 30) (by norm_num)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (1 / 30 : ℝ) / 512 = 1 / 15360 := by norm_num
  obtain ⟨N₀, _hN₀, h⟩ := hp (by simpa only [hscale] using hgeo)
  have he : Negligible C (fun N L ↦ goodResidual N L - allResidual N L) := by
    apply of_power_bound C (23 / 30) (by norm_num)
    refine ⟨N₀, ?_⟩
    intro N hN L hband
    have hh := h N hN L hband
    have ht := totalVariation_nonneg (goodLaw (8 * (L + 1) : ℕ) N L) (allLaw N L)
    have hm := abs_nonneg (goodMean (8 * (L + 1) : ℕ) N L - allMean N L)
    have hpow : (-4 / 5 + 1 / 30 : ℝ) = -(23 / 30) := by norm_num
    rw [hpow] at hh
    change _ + _ + |goodResidual N L - allResidual N L| ≤ _ at hh
    linarith only [hh, ht, hm]
  have hiff := (iff_of_error C goodResidual allResidual he).symm
  exact ⟨he, hiff, hiff.trans (good_criterion_iff C)⟩

end PaperP1.AllPairCriteriaUnderInputs
