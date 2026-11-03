module

public import PaperP1.Asymptotics.DenseWeightedSectorUnderInputs
public import PaperP1.Asymptotics.DenseNonalignedProfileReduction
public import PaperP1.Combinatorics.PairSubfamilyWeights
public import PaperP1.Model.CompatibleTripleJointBound

/-! # Actual dense nonaligned pair activity from the conditional geometric counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePairActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DenseNonalignedProfileReduction
  PaperP1.RawPairRelationRank PaperP1.LargePrimeGraphResolution

theorem nonaligned_host {N L x y : ℕ} (hxy : x ≠ y)
    (he : {x, y} ∈ AllAlignedPairs.nonaligned N L) :
    ¬ CompressedTargetAlignment.Aligned 1 x y L := by
  classical
  intro ha
  obtain ⟨heN, hnot⟩ := mem_sdiff.mp he
  apply hnot
  apply mem_filter.mpr
  refine ⟨heN, ?_⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact ⟨x, y, rfl, hlt, ha⟩
  · exact ⟨y, x, pair_comm x y, hgt, DegreeOneGraphHostCount.alignment_symm ha⟩

theorem dense_components {N L x y : ℕ} (hL : 1 ≤ L)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (he : {x, y} ∈ dense N L)
    (hd : (defectiveVertexCount x y L : ℝ) ≤ (1 / 100) * ((L + 1 : ℕ) : ℝ)) :
    (1 / 100) * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount x y L := by
  have hr := (dense_data he).2.2.2.1
  have hraw := relative_le_full x y L
  have hfull := rank_le_components (L := L) hx hy
  have hrawR : (runRelativeNullity L {x, y} : ℝ) ≤ fullRank x y L := by exact_mod_cast hraw
  have hfullR : (fullRank x y L : ℝ) ≤ defectiveVertexCount x y L + nontrivialComponentCount x y L := by exact_mod_cast hfull
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  simp only [Nat.cast_add, Nat.cast_one] at hd ⊢
  nlinarith only [hr, hrawR, hfullR, hd, hLR]

theorem centered_host_bound {N L x y : ℕ} (M : ℝ) (hL : 0 < L) (hxy : x ≠ y)
    (hq : 0 < infiniteJointMoment L {x, y})
    (hpx : infiniteMarginal x L ≤ M / N) (hpy : infiniteMarginal y L ≤ M / N) :
    |infiniteCenteredCoefficient L {x, y}| ≤
      (4 * (M / N) ^ 2) * (2 ^ fullRank x y L : ℝ) := by
  have hpos := CompatibleTripleJointBound.marginals_pos_of_joint L {x, y} hq
  have hc := infinite_centered_compatible_nullity_bound L {x, y} hL hpos
  rw [runCompatibleNullity_eq_of_positive_joint L {x, y} hq, card_pair hxy, prod_pair hxy] at hc
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at hc
  have hpx0 := MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hpy0 := MissingBlockProbabilities.infiniteMarginal_nonneg y L
  have hcap0 : 0 ≤ M / N := hpx0.trans hpx
  have hprod : infiniteMarginal x L * infiniteMarginal y L ≤ (M / N) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hpx hpy hpy0 hcap0
  have hpow : (2 ^ runRelativeNullity L {x, y} : ℝ) ≤ (2 ^ fullRank x y L : ℝ) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (relative_le_full x y L)
  exact hc.trans (mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num)) hpow
    (by positivity) (by positivity))

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 100)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        CompatibleActivitySplit.absolute L (dense N L) ≤ (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hweighted⟩ :=
    DenseWeightedSectorUnderInputs.uniform_full_weight C (ε / 2) (1 / 100) (by positivity) (by norm_num)
  obtain ⟨Nm, _hNm, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨Nd, hd⟩ := CriticalPairKernelPowers.defects_small C (1 / 100) (by norm_num)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let M := 2 * (2 : ℝ) ^ C
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, Nw, hw⟩ := hweighted hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (4 * M ^ 2 * A)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nm (max Nd (max Ng (max Nw Na)))), by omega, ?_⟩
  intro N hN L hcrit
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 1 ≤ L := by have h := (hg N (by omega) L hcrit).2.2.1; omega
  let G := dyadicBlock N
  let F := dense N L
  let U := PairSubfamilyWeights.hosts G F
  have hdata : ∀ p ∈ U, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧
      p.1 ≠ p.2 ∧ {p.1, p.2} ∈ dense N L := by
    intro p hp
    exact (PairSubfamilyWeights.mem_hosts G F p).mp hp
  have hdyadic : ∀ p ∈ U, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N :=
    fun p hp ↦ ⟨(hdata p hp).1, (hdata p hp).2.1⟩
  have hnon : ∀ p ∈ U, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L := by
    intro p hp
    have hpdata := hdata p hp
    exact nonaligned_host hpdata.2.2.1 (mem_inter.mp hpdata.2.2.2).1
  have hdensity : ∀ p ∈ U,
      (1 / 100 : ℝ) * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L := by
    intro p hp
    have hpdata := hdata p hp
    have hx : 1 ≤ p.1 := by have h := (mem_Ico.mp hpdata.1).1; omega
    have hy : 1 ≤ p.2 := by have h := (mem_Ico.mp hpdata.2.1).1; omega
    exact dense_components hL hx hy hpdata.2.2.2
      (hd N (by omega) L hcrit p.1 hpdata.1 p.2 hpdata.2.1)
  have hcount := hw N (by omega) L hcrit U hdyadic hnon hdensity
  have hcenter : ∀ p ∈ U, |infiniteCenteredCoefficient L {p.1, p.2}| ≤
      (4 * (M / N) ^ 2) * (2 ^ fullRank p.1 p.2 L : ℝ) := by
    intro p hp
    have hpdata := hdata p hp
    exact centered_host_bound M (by omega) hpdata.2.2.1 (dense_data hpdata.2.2.2).2.2.2.2
      (hm N (by omega) L hcrit p.1 hpdata.1) (hm N (by omega) L hcrit p.2 hpdata.2.1)
  have hsum := sum_le_sum hcenter
  rw [← mul_sum] at hsum
  have hF : F ⊆ G.powersetCard 2 := by
    intro e he
    exact (mem_sdiff.mp (mem_inter.mp he).1).1
  have hpair := PairSubfamilyWeights.weighted_sum G F hF (fun e ↦ |infiniteCenteredCoefficient L e|)
  have hnonneg : 0 ≤ ∑ e ∈ F, |infiniteCenteredCoefficient L e| := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hfinite : CompatibleActivitySplit.absolute L (dense N L) ≤
      (4 * (M / N) ^ 2) * (∑ p ∈ U, (2 ^ fullRank p.1 p.2 L : ℝ)) := by
    change (∑ e ∈ F, |infiniteCenteredCoefficient L e|) ≤ _
    change (∑ p ∈ U, |infiniteCenteredCoefficient L {p.1, p.2}|) = _ at hpair
    linarith only [hpair, hsum, hnonneg]
  calc
    _ ≤ (4 * (M / N) ^ 2) * (A * (N : ℝ) ^ (1 + ε / 2)) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hcount (by positivity))
    _ = (4 * M ^ 2 * A) * (N : ℝ) ^ (-1 + ε / 2) := by
      have hneg : ((N : ℝ) ^ 2)⁻¹ = (N : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hNpos.le, Real.rpow_two]
      rw [div_pow, div_eq_mul_inv, hneg]
      calc
        _ = (4 * M ^ 2 * A) * ((N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ (1 + ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hNpos]; congr 2; ring

    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DensePairActivityUnderInputs
