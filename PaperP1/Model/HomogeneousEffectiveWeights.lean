module

public import PaperP1.Model.CompressedPrimitiveHomogeneousBounds
public import PaperP1.Model.PositiveMarginalRestriction

/-! # Exact heterogeneous rank weights are dominated by the homogeneous law

No regularity or affine compatibility is assumed. Zero actual marginals
are retained and kill the corresponding original centered coefficient.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousEffectiveWeights

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem singleton_rank (L x : ℕ) :
    HomogeneousRunMass.probability L {x} = (2 ^ Module.finrank F₂ (squareClassSpace x L) : ℝ)⁻¹ := by
  rw [HomogeneousRunMass.probability_rank, rank]
  have hspan : span (fun y ↦ squareClassSpace y L) {x} = squareClassSpace x L := by
    apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      rw [mem_singleton.mp i.property]
    · exact local_le_span (fun y ↦ squareClassSpace y L) {x} (mem_singleton_self x)
  rw [hspan]

theorem factor (L : ℕ) (I : Finset ℕ) :
    HomogeneousRunMass.probability L I =
      (∏ x ∈ I, HomogeneousRunMass.probability L {x}) *
        (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) := by
  have hdim := rank_add_nullity_on (fun x ↦ squareClassSpace x L) I
  simp_rw [singleton_rank]
  rw [prod_inv_distrib, prod_pow_eq_pow_sum, HomogeneousRunMass.probability_rank, ← hdim, pow_add]
  field_simp

theorem marginal_le (L : ℕ) (hL : 0 < L) (x : ℕ) :
    infiniteMarginal x L ≤ HomogeneousRunMass.probability L {x} := by
  have hh := HomogeneousRunMass.actual_joint_le L hL {x}
  rwa [InfiniteTripleCancellation.singleton_joint] at hh

theorem independent_product_le (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    (∏ x ∈ I, infiniteMarginal x L) ≤ HomogeneousRunMass.probability L I := by
  calc
    _ ≤ ∏ x ∈ I, HomogeneousRunMass.probability L {x} :=
      prod_le_prod₀ (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        (fun x _ ↦ marginal_le L hL x)
    _ ≤ _ := by
      rw [factor]
      exact le_mul_of_one_le_right (prod_nonneg fun x _ ↦ (HomogeneousRunMass.probability_pos L {x}).le)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem weight_le (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    PrimitiveWindowMass.weight L I ≤ HomogeneousRunMass.probability L I := by
  rw [factor, PrimitiveWindowMass.weight]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact prod_le_prod₀ (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun x _ ↦ marginal_le L hL x)

theorem centered_le (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hne : I.Nonempty) :
    |infiniteCenteredCoefficient L I| ≤ HomogeneousRunMass.probability L I := by
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · exact (PrimitiveWindowMass.centered_le_weight L hL I hne hp).trans (weight_le L hL I)
  · push Not at hp
    obtain ⟨x, hx, hp⟩ := hp
    have hz := PositiveMarginalRestriction.zero_centered L I x hx
      (le_antisymm hp (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
    rw [hz, abs_zero]
    exact (HomogeneousRunMass.probability_pos L I).le

theorem compressed_three_mass_le (L : ℕ) (hL : 0 < L) (e A : Finset ℕ) (he : e.card = 2)
    (hp : PairPrimitiveCompression.Primitive L e A) :
    infiniteJointMoment L (e ∪ A) + |CompressedPairCoefficient.value L e A| +
      |infiniteCenteredCoefficient L (e ∪ A)| ≤ 4 * HomogeneousRunMass.probability L (e ∪ A) := by
  have hq := HomogeneousRunMass.actual_joint_le L hL (e ∪ A)
  have hhat := CompressedPairCoefficient.primitive_abs_bound L hL e A he hp
  have hsource : infiniteJointMoment L e * (∏ x ∈ A, infiniteMarginal x L) ≤
      HomogeneousRunMass.probability L (e ∪ A) :=
    (mul_le_mul (HomogeneousRunMass.actual_joint_le L hL e) (independent_product_le L hL A)
      (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      (HomogeneousRunMass.probability_pos L e).le).trans
      (CompressedPrimitiveHomogeneousBounds.product_le L e A)
  have hne : (e ∪ A).Nonempty := by
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < e.card by omega)
    exact ⟨x, mem_union_left A hx⟩
  have hc := centered_le L hL (e ∪ A) hne
  linarith only [hq, hhat, hsource, hc]

end PaperP1.HomogeneousEffectiveWeights
