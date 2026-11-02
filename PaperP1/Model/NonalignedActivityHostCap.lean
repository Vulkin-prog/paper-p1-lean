module

public import PaperP1.Model.AllAlignedPairs
public import PaperP1.Model.ActivityFamilyCover
public import PaperP1.Model.PairActivityHostCap

/-! # A joint cap on nonaligned hosts controls the literal nonaligned activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedActivityHostCap

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedPairRankLoss
  PaperP1.HeterogeneousRunConversion

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def sources (N L : ℕ) : Finset (ℕ × ℕ) :=
  (PairHostCover.hosts N L).filter fun p ↦ p.1 < p.2 ∧
    ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L

theorem ordered_data {N L : ℕ} {e : Finset ℕ} (he : e ∈ AllAlignedPairs.nonaligned N L) :
    ∃ x y : ℕ, x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧ x < y ∧ e = {x, y} ∧
      ¬ CompressedTargetAlignment.Aligned 1 x y L := by
  obtain ⟨hePow, hnot⟩ := mem_sdiff.mp he
  obtain ⟨heG, hcard⟩ := mem_powersetCard.mp hePow
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard
  have hx := heG (mem_insert_self x {y})
  have hy := heG (mem_insert_of_mem (mem_singleton_self y))
  by_cases hlt : x < y
  · refine ⟨x, y, hx, hy, hlt, rfl, ?_⟩
    intro ha
    exact hnot (mem_filter.mpr ⟨hePow, x, y, rfl, hlt, ha⟩)
  · have hyx : y < x := by omega
    refine ⟨y, x, hy, hx, hyx, pair_comm x y, ?_⟩
    intro ha
    exact hnot (mem_filter.mpr ⟨hePow, y, x, pair_comm x y, hyx, ha⟩)

theorem nonzero_cover {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) {e : Finset ℕ}
    (he : e ∈ AllAlignedPairs.nonaligned N L) (hc : infiniteCenteredCoefficient L e ≠ 0) :
    e ∈ (sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ)) := by
  obtain ⟨x, y, hx, hy, hxy, heq, hnon⟩ := ordered_data he
  have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have h := (mem_Ico.mp hy).1; omega
  have hloss : 0 < pairLoss x y L := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hc
    rw [heq]
    exact PairActivityHostCap.centered_zero_of_zero_loss hxpos hypos hxy.ne hL hz
  exact mem_image.mpr ⟨(x, y), mem_filter.mpr
    ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hloss⟩, hxy, hnon⟩, heq.symm⟩

theorem finite_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) {M : ℝ} (hM : 0 ≤ M)
    (hpair : ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N, x < y →
      ¬ CompressedTargetAlignment.Aligned 1 x y L → infiniteJointMoment L {x, y} ≤ M) :
    CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) ≤
      (PairHostCover.hosts N L).card * M + PairHostIndependentMass.mass N L := by
  have hcover := ActivityFamilyCover.two_families L (AllAlignedPairs.nonaligned N L)
    ((sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ))) ∅
    (fun _ he hn ↦ mem_union_left _ (nonzero_cover hN hL he hn))
  simp only [CompatibleActivitySplit.absolute, sum_empty, add_zero] at hcover
  calc
    _ ≤ ∑ e ∈ (sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ)),
        |infiniteCenteredCoefficient L e| := hcover
    _ ≤ ∑ p ∈ sources N L, |infiniteCenteredCoefficient L {p.1, p.2}| :=
      sum_image_le_of_nonneg (f := fun e : Finset ℕ ↦ |infiniteCenteredCoefficient L e|)
        (fun _ _ ↦ abs_nonneg _)
    _ ≤ ∑ p ∈ sources N L, (M + infiniteMarginal p.1 L * infiniteMarginal p.2 L) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpHost, hxy, hnon⟩ := mem_filter.mp hp
      obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hpHost).1
      have hq := infiniteJointMoment_nonneg L {p.1, p.2}
      have hprod := mul_nonneg (marginal_bounds p.1 L).1 (marginal_bounds p.2 L).1
      rw [CompressedJointMoments.centered_pair L _ (card_pair_eq_two_iff.mpr hxy.ne), prod_pair hxy.ne]
      have ht := abs_sub_le (infiniteJointMoment L {p.1, p.2}) 0
        (infiniteMarginal p.1 L * infiniteMarginal p.2 L)
      simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hq, abs_of_nonneg hprod] at ht
      exact ht.trans (add_le_add (hpair p.1 hx p.2 hy hxy hnon) le_rfl)
    _ ≤ ∑ p ∈ PairHostCover.hosts N L, (M + infiniteMarginal p.1 L * infiniteMarginal p.2 L) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ ↦
        add_nonneg hM (mul_nonneg (marginal_bounds p.1 L).1 (marginal_bounds p.2 L).1))
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]; rfl

end PaperP1.NonalignedActivityHostCap
