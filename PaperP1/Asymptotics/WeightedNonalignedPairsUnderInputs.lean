module

public import PaperP1.Model.PairRankCovarianceBound
public import PaperP1.Asymptotics.NonalignedSourceResidualUnderInputs
public import PaperP1.Asymptotics.FinitePairDeficitInputs
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The complete homogeneous nonaligned pair sum and its actual covariance consequence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedNonalignedPairsUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairRankCovarianceBound

theorem uniform_families (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 32)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, p.1 ≠ p.2) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∑ p ∈ F, rankWeight L {p.1, p.2}) ≤ (N : ℝ) ^ (1 + ε) ∧
      (∑ p ∈ F, |infiniteCenteredCoefficient L {p.1, p.2}|) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨D, j, j₁, j₂, hD, hp⟩ := NonalignedSourceResidualUnderInputs.uniform_weighted_hosts C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  let M : ℝ := 2 * (2 : ℝ) ^ C
  refine ⟨⟨D, j, j₁, j₂, hD⟩, ?_⟩
  intro hgeo
  obtain ⟨A, hA, NA, ha⟩ := hp (by simpa only [show ε / 2 / 16 = ε / 32 by ring] using hgeo.source)
    hgeo.ordinaryTwo hgeo.ordinaryThree hgeo.sourceCurves hgeo.ordinaryTwoCurves hgeo.ordinaryThreeCurves
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption A (1 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption (M ^ 2 * A) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NG (max NM (max NA (max NF NC)))), by omega, ?_⟩
  intro N hN L hband F hF hneq hnon
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have hl := (hg N (by omega) L hband).2.2.1; omega
  have hraw := ha N (by omega) L hband F hF hnon
  have hrank : (∑ p ∈ F, rankWeight L {p.1, p.2}) ≤ A * (N : ℝ) ^ (1 + ε / 2) := by
    apply le_trans _ hraw
    apply sum_le_sum
    intro p hpF
    have hx : 0 < p.1 := by have h := (mem_Ico.mp (hF p hpF).1).1; omega
    have hy : 0 < p.2 := by have h := (mem_Ico.mp (hF p hpF).2).1; omega
    exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (AlignedChannelFamilies.relative_le_loss hx hy (hneq p hpF))) 1
  have hcovariance : (∑ p ∈ F, |infiniteCenteredCoefficient L {p.1, p.2}|) ≤
      M ^ 2 * A * (N : ℝ) ^ (-1 + ε / 2) := by
    calc
      _ ≤ ∑ p ∈ F, (M / N) ^ 2 * rankWeight L {p.1, p.2} := sum_le_sum fun p hpF ↦
        pair_cap hL (hneq p hpF) M
          (hm N (by omega) L hband p.1 (hF p hpF).1)
          (hm N (by omega) L hband p.2 (hF p hpF).2)
      _ = (M / N) ^ 2 * ∑ p ∈ F, rankWeight L {p.1, p.2} := (mul_sum _ _ _).symm
      _ ≤ (M / N) ^ 2 * (A * (N : ℝ) ^ (1 + ε / 2)) := mul_le_mul_of_nonneg_left hrank (sq_nonneg _)
      _ = _ := by
        rw [show -1 + ε / 2 = (1 + ε / 2) - 2 by ring, Real.rpow_sub hn, Real.rpow_two, div_pow]
        ring
  constructor
  · exact hrank.trans (by convert hf N (by omega) using 1; congr 1; ring)
  · exact hcovariance.trans (by convert hc N (by omega) using 1; congr 1; ring)

def regularPairs (N L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((RegularStarts.regularStarts N L) ×ˢ (RegularStarts.regularStarts N L)).filter
    (fun p ↦ (L : ℤ) < |(p.1 : ℤ) - p.2| ∧ ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L)

theorem regular_nullity_eq_loss {N L x y : ℕ}
    (hx : x ∈ RegularStarts.regularStarts N L) (hy : y ∈ RegularStarts.regularStarts N L)
    (hxy : x ≠ y) :
    runRelativeNullity L {x, y} = NormalizedPairRankLoss.pairLoss x y L := by
  have hdim := Affine.rank_add_nullity_on (fun z ↦ squareClassSpace z L) {x, y}
  rw [sum_pair hxy, (RegularStarts.mem_regularStarts.mp hx).2, (RegularStarts.mem_regularStarts.mp hy).2] at hdim
  change Module.finrank F₂ (SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {x, y}) +
    runRelativeNullity L {x, y} = L + L at hdim
  rw [RetainedNullity.span_pair] at hdim
  unfold NormalizedPairRankLoss.pairLoss
  omega

theorem article_18_2 (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 32)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ p ∈ regularPairs N L, ((2 ^ runRelativeNullity L {p.1, p.2} : ℝ) - 1)) ≤ (N : ℝ) ^ (1 + ε) ∧
      (∑ p ∈ regularPairs N L,
        |infiniteJointMoment L {p.1, p.2} - infiniteMarginal p.1 L * infiniteMarginal p.2 L|) ≤
          (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨p, hp⟩ := uniform_families C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hdata (p : ℕ × ℕ) (hpF : p ∈ regularPairs N L) := mem_filter.mp hpF
  have hneq (p : ℕ × ℕ) (hpF : p ∈ regularPairs N L) : p.1 ≠ p.2 := by
    intro heq
    have hs := (hdata p hpF).2.1
    rw [heq, sub_self, abs_zero] at hs
    have hL0 : (0 : ℤ) ≤ L := Int.natCast_nonneg L
    omega
  have h := hh N hN L hband (regularPairs N L)
    (fun p hpF ↦ ⟨RegularStarts.regularStarts_subset N L (mem_product.mp (hdata p hpF).1).1,
      RegularStarts.regularStarts_subset N L (mem_product.mp (hdata p hpF).1).2⟩)
    hneq (fun p hpF ↦ (hdata p hpF).2.2)
  refine ⟨h.1, ?_⟩
  apply le_trans _ h.2
  apply sum_le_sum
  intro p hpF
  rw [CompressedJointMoments.centered_pair L _ (card_pair (hneq p hpF)), prod_pair (hneq p hpF)]

theorem article_18_2_rank_deficit (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 32)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ p ∈ regularPairs N L, ((2 ^ NormalizedPairRankLoss.pairLoss p.1 p.2 L : ℝ) - 1)) ≤
        (N : ℝ) ^ (1 + ε) ∧
      (∑ p ∈ regularPairs N L,
        |infiniteJointMoment L {p.1, p.2} - infiniteMarginal p.1 L * infiniteMarginal p.2 L|) ≤
          (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨p, hp⟩ := article_18_2 C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have h := hh N hN L hband
  refine ⟨?_, h.2⟩
  apply le_trans _ h.1
  apply sum_le_sum
  intro p hpF
  obtain ⟨hpR, hsep, _hnon⟩ := mem_filter.mp hpF
  obtain ⟨hx, hy⟩ := mem_product.mp hpR
  have hxy : p.1 ≠ p.2 := by
    intro heq
    rw [heq, sub_self, abs_zero] at hsep
    have hL0 : (0 : ℤ) ≤ L := Int.natCast_nonneg L
    omega
  rw [regular_nullity_eq_loss hx hy hxy]

end PaperP1.WeightedNonalignedPairsUnderInputs
