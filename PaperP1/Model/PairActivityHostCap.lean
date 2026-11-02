module

public import PaperP1.Model.HeterogeneousRunConversion
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.PairHostMoment
public import PaperP1.Asymptotics.PairHostIndependentMass
public import PaperP1.Combinatorics.OrderedSubsetWeights

/-! # Actual absolute covariance mass from full-loss hosts and a joint cap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairActivityHostCap

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic
  PaperP1.Affine PaperP1.Probability PaperP1.PairHostMoment
  PaperP1.NormalizedPairRankLoss PaperP1.HeterogeneousRunConversion

theorem absoluteMass_mono {G H : Finset ℕ} (hGH : G ⊆ H) (L : ℕ) :
    absoluteMass G L ≤ absoluteMass H L := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨heG, hcard⟩ := mem_powersetCard.mp he
    exact mem_powersetCard.mpr ⟨heG.trans hGH, hcard⟩
  · intro _ _ _
    exact abs_nonneg _

theorem centered_zero_of_zero_loss {x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hL : 0 < L) (hloss : pairLoss x y L = 0) :
    infiniteCenteredCoefficient L {x, y} = 0 := by
  obtain ⟨hxrank, hyrank, hdisj⟩ := zero_loss hx hy hloss
  have hp (z : ℕ) (hz : z ∈ ({x, y} : Finset ℕ)) : 0 < infiniteMarginal z L := by
    obtain rfl | hz := mem_insert.mp hz
    · rw [TripleProbabilityBound.marginal_of_full_rank hx hL hxrank]
      positivity
    · rw [mem_singleton.mp hz, TripleProbabilityBound.marginal_of_full_rank hy hL hyrank]
      positivity
  have hnull := relativeNullityOn_pair_eq_zero (fun z ↦ squareClassSpace z L) x y hxy hdisj
  rw [CompressedJointMoments.centered_pair L {x, y} (by simp [hxy]),
    CompressedJointMoments.direct_joint_factor L hL {x, y} hp hnull, sub_self]

theorem ordered_mass (G : Finset ℕ) (L : ℕ) :
    (∑ t : OrderedTuple G 2, |infiniteCenteredCoefficient L (tupleValues t)|) =
      2 * absoluteMass G L := by
  have hp : OrderedSubsetWeights.population G 2 (G.powersetCard 2) = univ := by
    ext t
    simp only [OrderedSubsetWeights.population, mem_filter, mem_univ,
      mem_powersetCard, tupleValues_subset t, tupleValues_card t, and_self]
  have h := OrderedSubsetWeights.weighted_sum G 2 (G.powersetCard 2) (subset_refl _)
    (fun e ↦ |infiniteCenteredCoefficient L e|)
  rw [hp] at h
  simpa only [absoluteMass, HeterogeneousPoissonCharlierConversion.absolutePairMass,
    show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] using h

theorem restrict_bad_tuples {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ t : OrderedTuple (dyadicBlock N) 2, |infiniteCenteredCoefficient L (tupleValues t)|) =
      ∑ t ∈ badTuples N L, |infiniteCenteredCoefficient L (tupleValues t)| := by
  symm
  apply sum_subset (subset_univ _)
  intro t _ ht
  have hx : 0 < (t 0).val := by have := (mem_Ico.mp (t 0).property).1; omega
  have hy : 0 < (t 1).val := by have := (mem_Ico.mp (t 1).property).1; omega
  have hxy : (t 0).val ≠ (t 1).val := by
    intro h
    have hi := t.injective (Subtype.ext h)
    norm_num at hi
  have hloss : pairLoss (t 0).val (t 1).val L = 0 := by
    have hh : ¬ 0 < pairLoss (t 0).val (t 1).val L :=
      fun h ↦ ht (mem_filter.mpr ⟨mem_univ _, h⟩)
    omega
  rw [tupleValues_pair, centered_zero_of_zero_loss hx hy hxy hL hloss, abs_zero]

/-- The factor two is the exact unordered-to-ordered multiplicity. The
host-independent term retains all actual heterogeneous marginal products. -/
theorem finite_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) {M : ℝ} (hM : 0 ≤ M)
    (hpair : ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N, x ≠ y →
      infiniteJointMoment L {x, y} ≤ M) :
    2 * absoluteMass (dyadicBlock N) L ≤
      (PairHostCover.hosts N L).card * M + PairHostIndependentMass.mass N L := by
  rw [← ordered_mass, restrict_bad_tuples hN hL]
  calc
    _ ≤ ∑ p ∈ PairHostCover.hosts N L,
        (M + infiniteMarginal p.1 L * infiniteMarginal p.2 L) := by
      apply sum_le_sum_of_injOn tuplePair ((tuplePair_injective _).injOn)
      · intro p hp
        obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
        exact mem_filter.mpr ⟨mem_product.mpr ⟨(t 0).property, (t 1).property⟩,
          (mem_filter.mp ht).2⟩
      · intro t _
        have hxy : (t 0).val ≠ (t 1).val := by
          intro h
          have hi := t.injective (Subtype.ext h)
          norm_num at hi
        have hq := infiniteJointMoment_nonneg L {(t 0).val, (t 1).val}
        have hp := mul_nonneg (marginal_bounds (t 0).val L).1 (marginal_bounds (t 1).val L).1
        rw [tupleValues_pair, CompressedJointMoments.centered_pair L _ (by simp [hxy]), prod_pair hxy]
        have habs := abs_sub_le (infiniteJointMoment L {(t 0).val, (t 1).val}) 0
          (infiniteMarginal (t 0).val L * infiniteMarginal (t 1).val L)
        simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hq, abs_of_nonneg hp] at habs
        exact habs.trans (add_le_add (hpair _ (t 0).property _ (t 1).property hxy) le_rfl)
      · intro p _ _
        exact add_nonneg hM (mul_nonneg (marginal_bounds p.1 L).1 (marginal_bounds p.2 L).1)
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]; rfl

theorem covariance_sum_absolute_bound (G : Finset ℕ) (L : ℕ) :
    |HeterogeneousPoissonCharlierConversion.covarianceSum (G.powersetCard 2)
      (infiniteCenteredCoefficient L)| ≤ absoluteMass G L :=
  abs_sum_le_sum_abs _ _

theorem second_cumulant_absolute_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    |RegularCumulantTransfer.secondFactorialCumulant G L| ≤
      2 * absoluteMass G L + HeterogeneousBernoulli.powerSum G (fun x ↦ infiniteMarginal x L) 2 := by
  rw [second_cumulant_formula hG]
  have hs := HeterogeneousBernoulli.powerSum_nonneg G (fun x ↦ infiniteMarginal x L)
    (fun x _ ↦ (marginal_bounds x L).1) 2
  calc
    _ ≤ |2 * HeterogeneousPoissonCharlierConversion.covarianceSum (G.powersetCard 2)
          (infiniteCenteredCoefficient L)| +
        |HeterogeneousBernoulli.powerSum G (fun x ↦ infiniteMarginal x L) 2| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hs]
      exact add_le_add (mul_le_mul_of_nonneg_left (covariance_sum_absolute_bound G L) (by norm_num)) le_rfl

end PaperP1.PairActivityHostCap
