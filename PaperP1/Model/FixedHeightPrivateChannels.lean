module

public import PaperP1.Model.FiniteGoodChannelPartition
public import PaperP1.Asymptotics.FiniteChannelHierarchyBounds

/-! # Exact fixed-height private channel sums and the literal omitted pair remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHeightPrivateChannels

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteAlignedChannelCover PaperP1.PrivateChannelSources

theorem source_channel_unique {Q N L : ℕ} (hN : 0 < N)
    (hlarge : 4 * Q ^ 2 * (L + 1) < N) {ab cd xy : ℕ × ℕ}
    (hab : ab ∈ channels Q) (hcd : cd ∈ channels Q)
    (hxy : xy ∈ FixedChannelSourceGeometry.unitSources N ab.1 ab.2 L)
    (huv : xy ∈ FixedChannelSourceGeometry.unitSources N cd.1 cd.2 L) : ab = cd := by
  have habd := channel_data hab
  have hcdd := channel_data hcd
  have h1 := FixedChannelLinearCount.unit_alignment hN hxy
  have h2 := FixedChannelLinearCount.unit_alignment hN huv
  have habQ : ab.1 ≤ Q := habd.2.1.le.trans habd.2.2.2.2.2
  have hcdQ : cd.1 ≤ Q := hcdd.2.1.le.trans hcdd.2.2.2.2.2
  have hbQ := habd.2.2.2.2.2
  have hdQ := hcdd.2.2.2.2.2
  have hx : N ≤ xy.1 := (mem_Ico.mp (mem_product.mp (mem_filter.mp hxy).1).1).1
  have h1cap : |(ab.2 : ℤ) * xy.1 - (ab.1 : ℤ) * xy.2| ≤ ((2 * Q * (L + 1) : ℕ) : ℤ) :=
    h1.trans (by exact_mod_cast Nat.mul_le_mul_right (L + 1) (show ab.1 + ab.2 ≤ 2 * Q by omega))
  have h2cap : |(cd.2 : ℤ) * xy.1 - (cd.1 : ℤ) * xy.2| ≤ ((2 * Q * (L + 1) : ℕ) : ℤ) :=
    h2.trans (by exact_mod_cast Nat.mul_le_mul_right (L + 1) (show cd.1 + cd.2 ≤ 2 * Q by omega))
  have hcomb := abs_sub ((cd.1 : ℤ) * ((ab.2 : ℤ) * xy.1 - (ab.1 : ℤ) * xy.2))
    ((ab.1 : ℤ) * ((cd.2 : ℤ) * xy.1 - (cd.1 : ℤ) * xy.2))
  rw [abs_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg cd.1), abs_of_nonneg (Int.natCast_nonneg ab.1)] at hcomb
  have heq : (cd.1 : ℤ) * ((ab.2 : ℤ) * xy.1 - (ab.1 : ℤ) * xy.2) -
      (ab.1 : ℤ) * ((cd.2 : ℤ) * xy.1 - (cd.1 : ℤ) * xy.2) =
      ((cd.1 : ℤ) * ab.2 - (ab.1 : ℤ) * cd.2) * xy.1 := by ring
  rw [heq, abs_mul, abs_of_nonneg (Int.natCast_nonneg xy.1)] at hcomb
  have hcap : |((cd.1 : ℤ) * ab.2 - (ab.1 : ℤ) * cd.2)| * xy.1 ≤
      ((4 * Q ^ 2 * (L + 1) : ℕ) : ℤ) := by
    have hfirst := mul_le_mul_of_nonneg_left h1cap (Int.natCast_nonneg cd.1)
    have hsecond := mul_le_mul_of_nonneg_left h2cap (Int.natCast_nonneg ab.1)
    have hca := mul_le_mul_of_nonneg_right (show (cd.1 : ℤ) ≤ Q by exact_mod_cast hcdQ)
      (show (0 : ℤ) ≤ (2 * Q * (L + 1) : ℕ) by positivity)
    have haa := mul_le_mul_of_nonneg_right (show (ab.1 : ℤ) ≤ Q by exact_mod_cast habQ)
      (show (0 : ℤ) ≤ (2 * Q * (L + 1) : ℕ) by positivity)
    push_cast at hfirst hsecond hca haa ⊢
    nlinarith only [hcomb, hfirst, hsecond, hca, haa]
  have hdet : (cd.1 : ℤ) * ab.2 - (ab.1 : ℤ) * cd.2 = 0 := by
    by_contra hn
    have hone : (1 : ℤ) ≤ |(cd.1 : ℤ) * ab.2 - (ab.1 : ℤ) * cd.2| := by
      by_cases hz : 0 ≤ (cd.1 : ℤ) * ab.2 - (ab.1 : ℤ) * cd.2
      · rw [abs_of_nonneg hz]; omega
      · rw [abs_of_neg (lt_of_not_ge hz)]; omega
    have hm := mul_le_mul_of_nonneg_right hone (Int.natCast_nonneg xy.1)
    have hl : ((4 * Q ^ 2 * (L + 1) : ℕ) : ℤ) < N := by exact_mod_cast hlarge
    have hxZ : (N : ℤ) ≤ xy.1 := by exact_mod_cast hx
    linarith only [hm, hcap, hl, hxZ]
  have hcross : cd.1 * ab.2 = ab.1 * cd.2 := by exact_mod_cast sub_eq_zero.mp hdet
  have hadvd : ab.1 ∣ cd.1 := habd.2.2.2.1.dvd_of_dvd_mul_left
    ⟨cd.2, by nlinarith only [hcross]⟩
  have hcdvd : cd.1 ∣ ab.1 := hcdd.2.2.2.1.dvd_of_dvd_mul_left
    ⟨ab.2, by nlinarith only [hcross]⟩
  have ha : ab.1 = cd.1 := Nat.dvd_antisymm hadvd hcdvd
  have hb : ab.2 = cd.2 := by
    rw [← ha] at hcross
    exact Nat.eq_of_mul_eq_mul_left habd.1 hcross
  exact Prod.ext ha hb

theorem pairwise_disjoint {Q N H L : ℕ} (hN : 2 ≤ N)
    (hlarge : 4 * Q ^ 2 * (L + 1) < N) :
    (↑(channels Q) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ab ↦ PrivateChannelActivity.pairs N H ab.1 ab.2 L) := by
  classical
  intro ab hab cd hcd hne
  apply disjoint_left.mpr
  intro e he hf
  have habd := channel_data hab
  have hcdd := channel_data hcd
  obtain ⟨xy, hxy, hxe⟩ := mem_image.mp he
  obtain ⟨uv, huv, hue⟩ := mem_image.mp hf
  have hsmall : 2 * Q * (L + 1) < N := by
    have hQ := habd.2.2.2.2.2
    have hb := habd.2.2.2.2.1
    nlinarith only [hlarge, hQ, hb, Nat.zero_le ((L + 1) * (Q - 1) ^ 2)]
  have hxylt := good_sources_order hN habd.2.1
    ((Nat.mul_le_mul_right (L + 1) (by omega : ab.1 + ab.2 ≤ 2 * Q)).trans_lt hsmall) hxy
  have huvlt := good_sources_order hN hcdd.2.1
    ((Nat.mul_le_mul_right (L + 1) (by omega : cd.1 + cd.2 ≤ 2 * Q)).trans_lt hsmall) huv
  have hsets : ({xy.1, xy.2} : Finset ℕ) = {uv.1, uv.2} := hxe.trans hue.symm
  have hx : xy.1 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← hsets]; simp
  have hy : xy.2 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← hsets]; simp
  simp only [mem_insert, mem_singleton] at hx hy
  have hsame : xy = uv := Prod.ext (by omega) (by omega)
  exact hne (source_channel_unique (by omega) hlarge hab hcd
    (good_sources_subset_unitSources N H ab.1 ab.2 L hxy)
    (hsame ▸ good_sources_subset_unitSources N H cd.1 cd.2 L huv))

theorem private_subset {Q N H L : ℕ} (hN : 2 ≤ N)
    (hlarge : 2 * Q * (L + 1) < N) :
    privatePairs Q N H L ⊆ (dyadicBlock N).powersetCard 2 := by
  classical
  intro e he
  obtain ⟨ab, hab, heab⟩ := mem_biUnion.mp he
  have hd := channel_data hab
  exact mem_powersetCard.mpr (PrivateChannelActivity.pair_data hN hd.2.1
    ((Nat.mul_le_mul_right (L + 1) (by omega : ab.1 + ab.2 ≤ 2 * Q)).trans_lt hlarge) heab)

theorem signed_remainder_bound {Q N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hlarge : 2 * Q * (L + 1) < N) :
    |CompatibleActivitySplit.signed L ((dyadicBlock N).powersetCard 2) -
      CompatibleActivitySplit.signed L (privatePairs Q N H L)| ≤
      CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak Q N H L) +
        CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.exceptional Q N H L) := by
  classical
  let F := (dyadicBlock N).powersetCard 2 \ privatePairs Q N H L
  have hs := sum_sdiff (private_subset (H := H) hN hlarge) (f := infiniteCenteredCoefficient L)
  have heq : CompatibleActivitySplit.signed L ((dyadicBlock N).powersetCard 2) -
      CompatibleActivitySplit.signed L (privatePairs Q N H L) = CompatibleActivitySplit.signed L F := by
    unfold CompatibleActivitySplit.signed
    change _ - _ = ∑ e ∈ F, infiniteCenteredCoefficient L e
    linarith only [hs]
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply ActivityFamilyCover.two_families
  intro e he hn
  obtain ⟨heE, hnot⟩ := mem_sdiff.mp he
  have hdep : e ∈ DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2 := by
    apply mem_filter.mpr
    refine ⟨heE, Nat.pos_of_ne_zero ?_⟩
    intro hz
    exact hn (AbsoluteActivityDecomposition.centered_zero_direct L hL e
      (card_pos.mp (by have hc := (mem_powersetCard.mp heE).2; omega)) hz)
  rw [← FiniteGoodChannelPartition.cover Q N H L] at hdep
  rcases mem_union.mp hdep with hgw | hexc
  · rcases mem_union.mp hgw with hg | hw
    · exact False.elim (hnot (mem_filter.mp hg).2.2)
    · exact mem_union_left _ hw
  · exact mem_union_right _ hexc

theorem absolute_private_sum {Q N H L : ℕ} (hN : 2 ≤ N)
    (hlarge : 4 * Q ^ 2 * (L + 1) < N) :
    CompatibleActivitySplit.absolute L (privatePairs Q N H L) =
      ∑ ab ∈ channels Q, CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N H ab.1 ab.2 L) :=
  sum_biUnion (pairwise_disjoint hN hlarge)

theorem main_terms (Q N L : ℕ) (hN : 0 < N) :
    (∑ ab ∈ channels Q, ChannelMainTermBounds.mainTerm N L ab.1 ab.2) =
      FiniteChannelHierarchy.coefficient N L Q := by
  rw [FiniteChannelHierarchyBounds.coefficient_eq_main_terms N L Q hN]
  apply sum_bij (fun ab _ ↦ (⟨ab.2, ab.1⟩ : Σ _b : ℕ, ℕ))
  · intro ab hab
    have hd := channel_data hab
    exact FiniteChannelHierarchy.mem_channels.mpr ⟨hd.2.2.2.2.1, hd.2.2.2.2.2, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩
  · intro ab _ cd _ heq
    have hb := congrArg Sigma.fst heq
    have ha := congrArg (fun z : Σ _b : ℕ, ℕ ↦ z.2) heq
    exact Prod.ext ha hb
  · intro z hz
    obtain ⟨hb, hbQ, ha, hab, hint, hcop⟩ := FiniteChannelHierarchy.mem_channels.mp hz
    refine ⟨(z.2, z.1), ?_, rfl⟩
    apply mem_filter.mpr
    exact ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ha, hab, hint, hcop, hb⟩
  · intro _ _
    rfl

end PaperP1.FixedHeightPrivateChannels
