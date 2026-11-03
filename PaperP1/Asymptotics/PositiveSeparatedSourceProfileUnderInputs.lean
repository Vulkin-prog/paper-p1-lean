module

public import PaperP1.Asymptotics.PrincipalPositiveResidual
public import PaperP1.Asymptotics.PrivateChannelPositiveProfile
public import PaperP1.Asymptotics.NonalignedSourceResidualUnderInputs
public import PaperP1.Asymptotics.DensePairActivityUnderInputs

/-! # The literal positive arithmetic profile over separated ordered pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveSeparatedSourceProfileUnderInputs

open Finset PaperP1.Model PaperP1.SourcePairPositiveWeight PaperP1.PrincipalPositiveCover
  PaperP1.PrivateChannelPositiveMass

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def mainTerm (N L : ℕ) : ℝ := (N : ℝ) / 3 *
  ((ChannelSumIdentity.unsigned L 2 3 : ℤ) + (ChannelSumIdentity.unsigned L 3 4 : ℤ))

theorem finite_profile_error {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) - mainTerm N L| ≤
      |channelWeight N H 2 3 L - (N : ℝ) * (ActualSourceTranslations.coefficient 2 3 : ℝ) *
        (ChannelSumIdentity.unsigned L 2 3 : ℤ)| +
      |channelWeight N H 3 4 L - (N : ℝ) * (ActualSourceTranslations.coefficient 3 4 : ℝ) *
        (ChannelSumIdentity.unsigned L 3 4 : ℤ)| +
      2 * (∑ e ∈ residual N H L, setWeight L e) +
      2 * (∑ e ∈ AllAlignedPairs.nonaligned N L, setWeight L e) := by
  let T := separated N L \ principal N H L
  have hsub : T ⊆ AllAlignedPairs.nonaligned N L ∪ residual N H L := by
    intro e he
    by_cases ha : e ∈ AllAlignedPairs.families N L
    · exact mem_union_right _ (mem_inter.mpr ⟨he, ha⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp he).1).1, ha⟩)
  have hTbound : (∑ e ∈ T, setWeight L e) ≤
      (∑ e ∈ AllAlignedPairs.nonaligned N L, setWeight L e) +
      ∑ e ∈ residual N H L, setWeight L e :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ setWeight_nonneg L e)).trans
      (GraphStarWeights.sum_union_le_nonneg _ _ (setWeight L) (setWeight_nonneg L))
  have hpartition := sum_sdiff (f := setWeight L) (principal_subset_separated (H := H) hN hlarge)
  have hprincipal := principal_mass_eq (H := H) hN hlarge
  have hordered := ordered_separated_sum N L
  let E := channelWeight N H 2 3 L - (N : ℝ) * (ActualSourceTranslations.coefficient 2 3 : ℝ) *
    (ChannelSumIdentity.unsigned L 2 3 : ℤ)
  let F := channelWeight N H 3 4 L - (N : ℝ) * (ActualSourceTranslations.coefficient 3 4 : ℝ) *
    (ChannelSumIdentity.unsigned L 3 4 : ℤ)
  have hmain : mainTerm N L =
      (N : ℝ) * (ActualSourceTranslations.coefficient 2 3 : ℝ) * (ChannelSumIdentity.unsigned L 2 3 : ℤ) +
      (N : ℝ) * (ActualSourceTranslations.coefficient 3 4 : ℝ) * (ChannelSumIdentity.unsigned L 3 4 : ℤ) := by
    norm_num [mainTerm, ActualSourceTranslations.coefficient]
    ring
  have heq : (∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) - mainTerm N L =
      E + F + 2 * (∑ e ∈ T, setWeight L e) := by
    dsimp only [E, F]
    rw [hmain, hordered]
    change (∑ e ∈ T, setWeight L e) + (∑ e ∈ principal N H L, setWeight L e) =
      ∑ e ∈ separated N L, setWeight L e at hpartition
    linarith only [hpartition, hprincipal]
  have hTpos : 0 ≤ 2 * (∑ e ∈ T, setWeight L e) :=
    mul_nonneg (by norm_num) (sum_nonneg fun e _ ↦ setWeight_nonneg L e)
  have htriangle := abs_add_le (E + F) (2 * (∑ e ∈ T, setWeight L e))
  rw [abs_of_nonneg hTpos] at htriangle
  have hEF := abs_add_le E F
  rw [heq]
  change _ ≤ |E| + |F| + _ + _
  linarith only [htriangle, hEF, hTbound]

theorem article_3_3_positive (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 64)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L,
          ((2 ^ PaperP1.NormalizedPairRankLoss.pairLoss p.1 p.2 L : ℝ) - 1)) -
          mainTerm N L| ≤ (N : ℝ) ^ (6 / 5 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hnon⟩ :=
    NonalignedSourceResidualUnderInputs.uniform_weighted_hosts C (ε / 4) (by positivity)
  rw [show (ε / 4) / 16 = ε / 64 by ring] at hnon
  obtain ⟨N23, _hN23, h23⟩ := PrivateChannelPositiveProfile.uniform_error C (ε / 4) 8 2 3
    (by decide) (by decide) (by decide) (by decide) (by positivity)
  obtain ⟨N34, _hN34, h34⟩ := PrivateChannelPositiveProfile.uniform_error C (ε / 4) 8 3 4
    (by decide) (by decide) (by decide) (by decide) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := PrincipalPositiveResidual.uniform_bound C (ε / 4) 8 (by positivity)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 29 (by norm_num) 1
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, NN, hn⟩ := hnon hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (A + 4) (6 / 5 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨max 2 (max N23 (max N34 (max NR (max NL (max NN NF))))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : 29 * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  let H := 8 * (L + 1)
  have h23' := h23 N (by omega) L H hband (by dsimp [H]; omega) le_rfl
  have h34' := h34 N (by omega) L H hband (by dsimp [H]; omega) le_rfl
  norm_num only [Nat.cast_ofNat] at h23' h34'
  have h23cap := h23'.trans (Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith : 5 / 6 + ε / 4 ≤ 6 / 5 + ε / 4))
  have h34cap := h34'.trans (Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith : 3 / 4 + ε / 4 ≤ 6 / 5 + ε / 4))
  have hres := hr N (by omega) L H hband le_rfl le_rfl
  let F := PairSubfamilyWeights.hosts (dyadicBlock N) (AllAlignedPairs.nonaligned N L)
  have hnonraw := hn N (by omega) L hband F
    (fun p hp ↦ by have hd := (PairSubfamilyWeights.mem_hosts _ _ p).mp hp; exact ⟨hd.1, hd.2.1⟩)
    (fun p hp ↦ by
      have hd := (PairSubfamilyWeights.mem_hosts _ _ p).mp hp
      exact DensePairActivityUnderInputs.nonaligned_host hd.2.2.1 hd.2.2.2)
  change (∑ p ∈ F, weight p.1 p.2 L) ≤ A * (N : ℝ) ^ (1 + ε / 4) at hnonraw
  rw [ordered_host_sum (dyadicBlock N) (AllAlignedPairs.nonaligned N L) L sdiff_subset] at hnonraw
  have hnoncap := hnonraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 1 + ε / 4 ≤ 6 / 5 + ε / 4)) hA.le)
  have hfinite := finite_profile_error (H := H) (by omega : 2 ≤ N) hlarge
  change |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) - mainTerm N L| ≤ _
  calc
    _ ≤ (A + 4) * (N : ℝ) ^ (6 / 5 + ε / 4) := by
      linarith only [hfinite, h23cap, h34cap, hres, hnoncap]
    _ ≤ (N : ℝ) ^ ((6 / 5 + ε / 4) + 3 * ε / 4) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PositiveSeparatedSourceProfileUnderInputs
