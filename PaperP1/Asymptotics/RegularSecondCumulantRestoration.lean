module

public import PaperP1.Asymptotics.IrregularPairActivity
public import PaperP1.Asymptotics.SecondCumulantUnderBCN
public import PaperP1.Model.HeterogeneousRunConversion

/-! # The full actual second factorial cumulant differs from its regular restriction by N^(-1+epsilon), unconditionally -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularSecondCumulantRestoration

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic

theorem pair_difference (G H : Finset ℕ) :
    G.powersetCard 2 \ H.powersetCard 2 = TouchingEdgeWeights.touching G (G \ H) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨hG, hnot⟩ := mem_sdiff.mp he
    obtain ⟨heG, hcard⟩ := mem_powersetCard.mp hG
    have hnsub : ¬e ⊆ H := fun h ↦ hnot (mem_powersetCard.mpr ⟨h, hcard⟩)
    obtain ⟨x, hxe, hxH⟩ := not_subset.mp hnsub
    exact mem_filter.mpr ⟨hG, x, mem_sdiff.mpr ⟨heG hxe, hxH⟩, hxe⟩
  · intro he
    obtain ⟨hG, x, hx, hxe⟩ := mem_filter.mp he
    refine mem_sdiff.mpr ⟨hG, ?_⟩
    intro hH
    exact (mem_sdiff.mp hx).2 ((mem_powersetCard.mp hH).1 hxe)

theorem covariance_difference (G H : Finset ℕ) (hHG : H ⊆ G) (L : ℕ) :
    |(∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) -
      ∑ e ∈ H.powersetCard 2, infiniteCenteredCoefficient L e| ≤
        ∑ e ∈ TouchingEdgeWeights.touching G (G \ H), |infiniteCenteredCoefficient L e| := by
  classical
  have hsub : H.powersetCard 2 ⊆ G.powersetCard 2 := by
    intro e he
    obtain ⟨heH, hcard⟩ := mem_powersetCard.mp he
    exact mem_powersetCard.mpr ⟨heH.trans hHG, hcard⟩
  have hs := sum_sdiff hsub (f := infiniteCenteredCoefficient L)
  have heq : (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) -
      (∑ e ∈ H.powersetCard 2, infiniteCenteredCoefficient L e) =
      ∑ e ∈ TouchingEdgeWeights.touching G (G \ H), infiniteCenteredCoefficient L e := by
    rw [← pair_difference G H]
    linarith only [hs]
  rw [heq]
  exact abs_sum_le_sum_abs _ _

theorem finite_bound {N L : ℕ} (G H : Finset ℕ) (hG : G ⊆ dyadicBlock N) (hHG : H ⊆ G) :
    |RegularCumulantTransfer.secondFactorialCumulant G L -
      RegularCumulantTransfer.secondFactorialCumulant H L| ≤
        2 * (∑ e ∈ TouchingEdgeWeights.touching G (G \ H), |infiniteCenteredCoefficient L e|) +
          ∑ x ∈ G, infiniteMarginal x L ^ 2 := by
  have hfull := HeterogeneousRunConversion.second_cumulant_formula (L := L) hG
  have hrest := HeterogeneousRunConversion.second_cumulant_formula (L := L) (hHG.trans hG)
  change RegularCumulantTransfer.secondFactorialCumulant G L =
    2 * (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) - ∑ x ∈ G, infiniteMarginal x L ^ 2 at hfull
  change RegularCumulantTransfer.secondFactorialCumulant H L =
    2 * (∑ e ∈ H.powersetCard 2, infiniteCenteredCoefficient L e) - ∑ x ∈ H, infiniteMarginal x L ^ 2 at hrest
  have hdlo : 0 ≤ (∑ x ∈ G, infiniteMarginal x L ^ 2) - ∑ x ∈ H, infiniteMarginal x L ^ 2 :=
    sub_nonneg.mpr (sum_le_sum_of_subset_of_nonneg hHG (fun x _ _ ↦ sq_nonneg _))
  have hdhi : (∑ x ∈ G, infiniteMarginal x L ^ 2) - (∑ x ∈ H, infiniteMarginal x L ^ 2) ≤
      ∑ x ∈ G, infiniteMarginal x L ^ 2 := sub_le_self _ (sum_nonneg fun x _ ↦ sq_nonneg _)
  have hid : RegularCumulantTransfer.secondFactorialCumulant G L -
      RegularCumulantTransfer.secondFactorialCumulant H L =
      2 * ((∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) -
        ∑ e ∈ H.powersetCard 2, infiniteCenteredCoefficient L e) -
          ((∑ x ∈ G, infiniteMarginal x L ^ 2) - ∑ x ∈ H, infiniteMarginal x L ^ 2) := by
    rw [hfull, hrest]
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hdlo]
  exact add_le_add (mul_le_mul_of_nonneg_left (covariance_difference G H hHG L) (by norm_num)) hdhi

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
        RegularCumulantTransfer.secondFactorialCumulant (RegularStarts.regularStarts N L) L| ≤
          (N : ℝ) ^ (-1 + ε) := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨NI, _hNI, hi⟩ := IrregularPairActivity.uniform_activity C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + M ^ 2) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NI + NM + NF, by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) (Subset.refl (dyadicBlock N))
    (fun x hx ↦ hm N (by omega) L hband x hx)
  change (∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2) ≤ M ^ 2 / N at hdiag
  have hdi : (∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2) ≤ M ^ 2 * (N : ℝ) ^ (-1 + ε / 2) := hdiag.trans (by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) (sq_nonneg M))
  have heq : TouchingEdgeWeights.touching (dyadicBlock N) (dyadicBlock N \ RegularStarts.regularStarts N L) =
      IrregularPairActivity.pairs N L (dyadicBlock N) := by
    rw [IrregularPairActivity.pairs, inter_eq_right.mpr (show RegularStarts.irregularStarts N L ⊆ dyadicBlock N from sdiff_subset)]
    rfl
  have hir := hi N (by omega) L hband (dyadicBlock N) Subset.rfl
  have hfinite := finite_bound (L := L) (dyadicBlock N) (RegularStarts.regularStarts N L) Subset.rfl
    (RegularStarts.regularStarts_subset N L)
  rw [heq] at hfinite
  change (∑ e ∈ IrregularPairActivity.pairs N L (dyadicBlock N), |infiniteCenteredCoefficient L e|) ≤ (N : ℝ) ^ (-1 + ε / 2) at hir
  calc
    _ ≤ (2 + M ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hfinite, hir, hdi]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RegularSecondCumulantRestoration
