module

public import PaperP1.Model.SecondOrderIndependentDeficit
public import PaperP1.Algebra.AllPairPolynomialExpansion
public import PaperP1.Model.NonretainedPositiveMass
public import PaperP1.Probability.HeterogeneousPoissonCharlierConversion

/-! # Exact heterogeneous all-pair retained identity and its sharp finite independent-deficit comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondOrderRetainedReference

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.SecondOrderRetainedClass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def coefficient (L : ℕ) (I : Finset ℕ) : ℝ := (∏ x ∈ I, infiniteMarginal x L) +
  ∑ e ∈ I.powersetCard 2, infiniteCenteredCoefficient L e * ∏ x ∈ I \ e, infiniteMarginal x L

def discarded (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := G.powerset.filter fun I ↦ ¬Retained G L I

def retainedReference (G : Finset ℕ) (L : ℕ) : SignedLaw ℝ :=
  ∑ I ∈ retainedSets G (Retained G L), scalar (infiniteJointMoment L I) * forwardDifference ^ I.card

def pairReference (G : Finset ℕ) (L : ℕ) : SignedLaw ℝ :=
  HeterogeneousPoissonCharlierConversion.finiteReference G (G.powersetCard 2)
    (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L)

theorem pair_expansion (G : Finset ℕ) (L : ℕ) :
    pairReference G L = ∑ I ∈ G.powerset, scalar (coefficient L I) * forwardDifference ^ I.card := by
  have h := AllPairPolynomialExpansion.all_pair_expansion G
    (fun x ↦ scalar (infiniteMarginal x L)) (fun e ↦ scalar (infiniteCenteredCoefficient L e)) forwardDifference
  simpa only [pairReference, HeterogeneousPoissonCharlierConversion.finiteReference, coefficient,
    bernoulli, atom_zero, map_add, map_prod, map_sum, map_mul] using h

theorem retained_difference (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    retainedReference G L - pairReference G L =
      -(∑ I ∈ discarded G L, scalar (coefficient L I) * forwardDifference ^ I.card) := by
  have hret : retainedReference G L = ∑ I ∈ G.powerset.filter (Retained G L),
      scalar (coefficient L I) * forwardDifference ^ I.card := by
    apply sum_congr rfl
    intro I hI
    rw [joint_expansion G L hL I (mem_filter.mp hI).2]
    rfl
  have hsplit := sum_filter_add_sum_filter_not G.powerset (Retained G L)
    (fun I ↦ scalar (coefficient L I) * (forwardDifference : SignedLaw ℝ) ^ I.card)
  rw [hret, pair_expansion, ← hsplit]
  change _ = -(∑ I ∈ G.powerset.filter (fun I ↦ ¬Retained G L I), scalar (coefficient L I) * forwardDifference ^ I.card)
  ring

theorem coefficient_abs (L : ℕ) (I : Finset ℕ) :
    |coefficient L I| ≤ (∏ x ∈ I, infiniteMarginal x L) +
      ∑ e ∈ I.powersetCard 2, |infiniteCenteredCoefficient L e| * ∏ x ∈ I \ e, infiniteMarginal x L := by
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)]
  apply add_le_add le_rfl
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply sum_congr rfl
  intro e _he
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)]

theorem weighted_coefficient (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (hIG : I ⊆ G) (u : ℝ) (hu : 0 ≤ u) :
    u ^ I.card * |coefficient L I| ≤ (∏ x ∈ I, u * infiniteMarginal x L) +
      ∑ e ∈ G.powersetCard 2, if e ⊆ I then u ^ 2 * |infiniteCenteredCoefficient L e| *
        ∏ x ∈ I \ e, u * infiniteMarginal x L else 0 := by
  have h := mul_le_mul_of_nonneg_left (coefficient_abs L I) (pow_nonneg hu I.card)
  rw [mul_add, mul_sum] at h
  have hfilter : (G.powersetCard 2).filter (fun e ↦ e ⊆ I) = I.powersetCard 2 := by
    ext e
    simp only [mem_filter, mem_powersetCard]
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.trans hIG, h.2⟩, h.1⟩⟩
  rw [← sum_filter, hfilter]
  apply h.trans_eq
  congr 1
  · rw [prod_mul_distrib, prod_const]
  · apply sum_congr rfl
    intro e he
    rw [NonretainedPositiveMass.weighted_term L I e (mem_powersetCard.mp he).1 u _, (mem_powersetCard.mp he).2]

theorem scalar_term_norm (a : ℝ) (r : ℕ) :
    l1Norm (scalar a * (forwardDifference : SignedLaw ℝ) ^ r) ≤ (2 : ℝ) ^ r * |a| := by
  apply (l1Norm_mul _ _).trans
  rw [l1Norm_scalar, mul_comm]
  exact mul_le_mul_of_nonneg_right (l1Norm_forwardDifference_pow_le r) (abs_nonneg a)

theorem retained_error (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    l1Norm (retainedReference G L - pairReference G L) ≤
      Real.exp (∑ x ∈ G, 2 * infiniteMarginal x L) *
        (∑ D ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 D) +
        8 * AllPairExtensionDeficit.deficit G L 2 := by
  have hF : ∀ I ∈ discarded G L, I ⊆ G ∧ ¬Retained G L I := by
    intro I hI
    exact ⟨mem_powerset.mp (mem_filter.mp hI).1, (mem_filter.mp hI).2⟩
  have hnorm : l1Norm (retainedReference G L - pairReference G L) ≤
      ∑ I ∈ discarded G L, (2 : ℝ) ^ I.card * |coefficient L I| := by
    rw [retained_difference G L hL, l1Norm_neg]
    exact (l1Norm_sum _ _).trans (sum_le_sum fun I _ ↦ scalar_term_norm _ I.card)
  have hpoint := sum_le_sum fun I hI ↦ weighted_coefficient G L I (hF I hI).1 2 (by norm_num)
  simp only [sum_add_distrib] at hpoint
  have hind := SecondOrderIndependentDeficit.independent_bound G L hL 2 (by norm_num) (discarded G L) hF
  have hpair := SecondOrderIndependentDeficit.pair_bound G L 2 (by norm_num) (discarded G L) hF
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hpoint hind hpair
  linarith only [hnorm, hpoint, hind, hpair]

end PaperP1.SecondOrderRetainedReference
