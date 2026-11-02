module

public import PaperP1.Model.PairActivityHostCap
public import PaperP1.Combinatorics.OrderedPairTuples

/-! # A positive selected joint mass gives a lower bound for the actual cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedPairCumulantLower

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic
  PaperP1.NormalizedPairRankLoss PaperP1.HeterogeneousRunConversion
  PaperP1.HeterogeneousPoissonCharlierConversion PaperP1.HeterogeneousBernoulli

def distinctHosts (N L : ℕ) : Finset (ℕ × ℕ) :=
  (PairHostCover.hosts N L).filter fun p ↦ p.1 ≠ p.2

theorem distinctHosts_subset_pairs (N L : ℕ) :
    distinctHosts N L ⊆ OrderedPairTuples.pairs (dyadicBlock N) := by
  intro p hp
  obtain ⟨hp, hne⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1, hne⟩

theorem swap_mem_distinctHosts (N L : ℕ) (p : ℕ × ℕ) :
    p.swap ∈ distinctHosts N L ↔ p ∈ distinctHosts N L := by
  simp only [distinctHosts, PairHostCover.hosts, mem_filter, mem_product, Prod.fst_swap,
    Prod.snd_swap, pairLoss_comm p.2 p.1 L, ne_comm]
  tauto

theorem ordered_covariance (G : Finset ℕ) (L : ℕ) :
    (∑ p ∈ OrderedPairTuples.pairs G, infiniteCenteredCoefficient L {p.1, p.2}) =
      2 * covarianceSum (G.powersetCard 2) (infiniteCenteredCoefficient L) :=
  OrderedPairTuples.weighted_subsets G (infiniteCenteredCoefficient L)

theorem restrict_to_hosts {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), infiniteCenteredCoefficient L {p.1, p.2}) =
      ∑ p ∈ distinctHosts N L, infiniteCenteredCoefficient L {p.1, p.2} := by
  symm
  apply sum_subset (distinctHosts_subset_pairs N L)
  intro p hp hnot
  obtain ⟨hpbox, hpne⟩ := mem_filter.mp hp
  obtain ⟨hx, hy⟩ := mem_product.mp hpbox
  have hxpos : 0 < p.1 := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < p.2 := by have := (mem_Ico.mp hy).1; omega
  have hloss : pairLoss p.1 p.2 L = 0 := by
    have hh : ¬ 0 < pairLoss p.1 p.2 L := fun h ↦
      hnot (mem_filter.mpr ⟨mem_filter.mpr ⟨hpbox, h⟩, hpne⟩)
    omega
  exact PairActivityHostCap.centered_zero_of_zero_loss hxpos hypos hpne hL hloss

theorem host_joint_identity {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ p ∈ distinctHosts N L, infiniteJointMoment L {p.1, p.2}) =
      2 * covarianceSum ((dyadicBlock N).powersetCard 2) (infiniteCenteredCoefficient L) +
        ∑ p ∈ distinctHosts N L, infiniteMarginal p.1 L * infiniteMarginal p.2 L := by
  have heq : (∑ p ∈ distinctHosts N L, infiniteJointMoment L {p.1, p.2}) -
      (∑ p ∈ distinctHosts N L, infiniteMarginal p.1 L * infiniteMarginal p.2 L) =
        2 * covarianceSum ((dyadicBlock N).powersetCard 2) (infiniteCenteredCoefficient L) := by
    calc
      _ = ∑ p ∈ distinctHosts N L, infiniteCenteredCoefficient L {p.1, p.2} := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro p hp
        have hne := (mem_filter.mp hp).2
        rw [CompressedJointMoments.centered_pair L _ (by simp [hne]), prod_pair hne]
      _ = _ := (restrict_to_hosts hN hL).symm.trans (ordered_covariance _ L)
  linarith only [heq]

theorem selected_joint_lower {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (F : Finset (ℕ × ℕ)) (hF : F ⊆ distinctHosts N L) :
    (∑ p ∈ F, infiniteJointMoment L {p.1, p.2}) - PairHostIndependentMass.mass N L ≤
      2 * covarianceSum ((dyadicBlock N).powersetCard 2) (infiniteCenteredCoefficient L) := by
  have hq : (∑ p ∈ F, infiniteJointMoment L {p.1, p.2}) ≤
      ∑ p ∈ distinctHosts N L, infiniteJointMoment L {p.1, p.2} :=
    sum_le_sum_of_subset_of_nonneg hF (fun p _ _ ↦ infiniteJointMoment_nonneg L _)
  have hi : (∑ p ∈ distinctHosts N L, infiniteMarginal p.1 L * infiniteMarginal p.2 L) ≤
      PairHostIndependentMass.mass N L :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ ↦ mul_nonneg (marginal_bounds p.1 L).1 (marginal_bounds p.2 L).1)
  rw [host_joint_identity hN hL] at hq
  linarith only [hq, hi]

theorem second_cumulant_lower {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (F : Finset (ℕ × ℕ)) (hF : F ⊆ distinctHosts N L) :
    (∑ p ∈ F, infiniteJointMoment L {p.1, p.2}) - PairHostIndependentMass.mass N L -
        powerSum (dyadicBlock N) (fun x ↦ infiniteMarginal x L) 2 ≤
      RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L := by
  rw [second_cumulant_formula (subset_refl _)]
  exact sub_le_sub_right (selected_joint_lower hN hL F hF) _

end PaperP1.SelectedPairCumulantLower
