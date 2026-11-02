module

public import PaperP1.Asymptotics.SecondCumulantNonalignedReduction
public import PaperP1.Asymptotics.InitialPairPartition

/-! # Only regular compatible macroscopic nonaligned pairs remain in the full profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseNonalignedProfileReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges
  PaperP1.DependentFamilySeeds

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def dense (N L : ℕ) : Finset (Finset ℕ) :=
  AllAlignedPairs.nonaligned N L ∩ InitialPairPartition.remaining (dyadicBlock N) N L (1 / 10)

theorem dense_data {N L : ℕ} {e : Finset ℕ} (he : e ∈ dense N L) :
    e ⊆ RegularStarts.regularStarts N L ∧ e.card = 2 ∧ e ∉ AllAlignedPairs.families N L ∧
      (L : ℝ) / 10 < (runRelativeNullity L e : ℝ) ∧ 0 < infiniteJointMoment L e := by
  obtain ⟨hne, hremaining⟩ := mem_inter.mp he
  obtain ⟨hdep, hnot, hrank, hq⟩ := InitialPairPartition.remaining_data (dyadicBlock N) N L (1 / 10) e hremaining
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (mem_filter.mp hdep).1
  have hreg : e ⊆ RegularStarts.regularStarts N L := by
    intro x hx
    by_contra hxreg
    apply hnot
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨heG, hecard⟩, x,
      mem_inter.mpr ⟨heG hx, mem_sdiff.mpr ⟨heG hx, hxreg⟩⟩, hx⟩
  exact ⟨hreg, hecard, (mem_sdiff.mp hne).2, by linarith only [hrank], hq⟩

theorem nonaligned_activity_bound (N L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) ≤
      CompatibleActivitySplit.absolute L (InitialPairPartition.weak (dyadicBlock N) N L (1 / 10)) +
      CompatibleActivitySplit.absolute L (InitialPairPartition.exceptional (dyadicBlock N) N L) +
      CompatibleActivitySplit.absolute L (dense N L) := by
  let W := InitialPairPartition.weak (dyadicBlock N) N L (1 / 10)
  let E := InitialPairPartition.exceptional (dyadicBlock N) N L
  have hcover : ∀ e ∈ AllAlignedPairs.nonaligned N L, infiniteCenteredCoefficient L e ≠ 0 →
      e ∈ (W ∪ E) ∪ dense N L := by
    intro e he hn
    have hePow := (mem_sdiff.mp he).1
    have hpos : 0 < runRelativeNullity L e := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hne : e.Nonempty := card_pos.mp (by have h := (mem_powersetCard.mp hePow).2; omega)
      exact hn (AbsoluteActivityDecomposition.centered_zero_direct L hL e hne hz)
    have hdep : e ∈ dependentFamilies (dyadicBlock N) L 2 := mem_filter.mpr ⟨hePow, hpos⟩
    rw [← InitialPairPartition.cover (dyadicBlock N) N L (1 / 10)] at hdep
    rcases mem_union.mp hdep with hwe | hr
    · exact mem_union_left _ hwe
    · exact mem_union_right _ (mem_inter.mpr ⟨he, hr⟩)
  have h1 := ActivityFamilyCover.two_families L (AllAlignedPairs.nonaligned N L) (W ∪ E) (dense N L) hcover
  have h2 := ActivityFamilyCover.two_families L (W ∪ E) W E (fun _ he _ ↦ he)
  dsimp only [W, E] at h1 h2
  linarith only [h1, h2]

theorem uniform_bound (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 2 * beta N H L| ≤
        2 * CompatibleActivitySplit.absolute L (dense N L) + (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := SecondCumulantNonalignedReduction.uniform_bound C (ε / 2) D (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := InitialPairPartition.uniform_bounds C (1 / 10) (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 5 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NR (max NP (max NG NF))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hpartition := nonaligned_activity_bound N L hL
  have hparts := hp N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hw : CompatibleActivitySplit.absolute L (InitialPairPartition.weak (dyadicBlock N) N L (1 / 10)) ≤
      (N : ℝ) ^ (-4 / 5 + ε / 2) := hparts.1.trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith))
  have he : CompatibleActivitySplit.absolute L (InitialPairPartition.exceptional (dyadicBlock N) N L) ≤
      (N : ℝ) ^ (-4 / 5 + ε / 2) := hparts.2.trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith))
  have hprofile := hr N (by omega) L H hband hcut hH
  calc
    _ ≤ 2 * CompatibleActivitySplit.absolute L (dense N L) + 5 * (N : ℝ) ^ (-4 / 5 + ε / 2) :=
      by linarith only [hpartition, hw, he, hprofile]
    _ ≤ 2 * CompatibleActivitySplit.absolute L (dense N L) + (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) :=
      by
        have hh := hf N (by omega)
        linarith only [hh]
    _ = _ := by congr 2; ring

end PaperP1.DenseNonalignedProfileReduction
