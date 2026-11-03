module

public import PaperP1.Model.BlockJointIntersection
public import PaperP1.Model.ConnectedTriplePositiveReduction

/-! # A connected triple with one small source/complement crossing costs only the independent and unary-deficit remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedTripleLowCrossing

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

theorem pointwise (L : ℕ) (hL : 0 < L) (T : Finset ℕ) (hcard : T.card = 3)
    (z : ℕ) (hz : z ∈ T) (K : ℝ) (hK : 0 ≤ K)
    (hpow : (2 ^ Module.finrank F₂ ↥(squareClassSpace z L ⊓
      span (fun x ↦ squareClassSpace x L) (T.erase z)) : ℝ) ≤ K) :
    infiniteJointMoment L T ≤ K *
      ((∑ x ∈ T, |infiniteCenteredCoefficient L (T.erase x)| * infiniteMarginal x L) +
        ∏ x ∈ T, infiniteMarginal x L) := by
  classical
  have hecard : (T.erase z).card = 2 := by have h := card_erase_add_one hz; omega
  have hdis : Disjoint (T.erase z) ({z} : Finset ℕ) := disjoint_singleton_right.mpr (notMem_erase _ _)
  have hspan : span (fun x ↦ squareClassSpace x L) {z} = squareClassSpace z L := by simp [span]
  have hb := BlockJointIntersection.upper_bound L hL (T.erase z) {z} hdis
  rw [union_singleton, insert_erase hz, InfiniteTripleCancellation.singleton_joint, hspan,
    inf_comm (span (fun x ↦ squareClassSpace x L) (T.erase z)) (squareClassSpace z L)] at hb
  have hscale : infiniteJointMoment L T ≤ K * (infiniteJointMoment L (T.erase z) * infiniteMarginal z L) :=
    hb.trans ((mul_le_mul_of_nonneg_left hpow (mul_nonneg (infiniteJointMoment_nonneg L _)
      (MissingBlockProbabilities.infiniteMarginal_nonneg z L))).trans_eq (by ring))
  have hc := CompressedJointMoments.centered_pair L (T.erase z) hecard
  have hp := prod_erase_mul T (fun x ↦ infiniteMarginal x L) hz
  have hterm := mul_le_mul_of_nonneg_right (le_abs_self (infiniteCenteredCoefficient L (T.erase z)))
    (MissingBlockProbabilities.infiniteMarginal_nonneg z L)
  have hcp := congrArg (fun t : ℝ ↦ t * infiniteMarginal z L) hc
  rw [sub_mul] at hcp
  have hpair : infiniteJointMoment L (T.erase z) * infiniteMarginal z L ≤
      |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L +
        ∏ x ∈ T, infiniteMarginal x L := by linarith only [hcp, hp, hterm]
  have hsum : |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L ≤
      ∑ x ∈ T, |infiniteCenteredCoefficient L (T.erase x)| * infiniteMarginal x L :=
    single_le_sum (f := fun x : ℕ ↦ |infiniteCenteredCoefficient L (T.erase x)| * infiniteMarginal x L)
      (fun x _ ↦ mul_nonneg (abs_nonneg _) (MissingBlockProbabilities.infiniteMarginal_nonneg x L)) hz
  exact hscale.trans (mul_le_mul_of_nonneg_left (hpair.trans (add_le_add hsum le_rfl)) hK)

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ))
    (hF : F ⊆ connectedFamilies G L 3) (K : ℝ) (hK : 0 ≤ K)
    (hlow : ∀ T ∈ F, ∃ z ∈ T, (2 ^ Module.finrank F₂ ↥(squareClassSpace z L ⊓
      span (fun x ↦ squareClassSpace x L) (T.erase z)) : ℝ) ≤ K) :
    (∑ T ∈ F, infiniteJointMoment L T) ≤ K * (IndependentTargetDeficit.deficit G L +
      FamilyIndependentMass.independentMass (connectedFamilies G L 3) L) := by
  classical
  let f := fun T : Finset ℕ ↦
    (∑ x ∈ T, |infiniteCenteredCoefficient L (T.erase x)| * infiniteMarginal x L) +
      ∏ x ∈ T, infiniteMarginal x L
  calc
    _ ≤ K * ∑ T ∈ F, f T := by
      rw [mul_sum]
      apply sum_le_sum
      intro T hT
      obtain ⟨z, hz, hpow⟩ := hlow T hT
      exact pointwise L hL T (mem_powersetCard.mp (mem_filter.mp (hF hT)).1).2 z hz K hK hpow
    _ ≤ K * ∑ T ∈ connectedFamilies G L 3, f T := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hF (fun T _ _ ↦ add_nonneg
        (sum_nonneg fun x _ ↦ mul_nonneg (abs_nonneg _) (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
        (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))) hK
    _ = K * ((∑ T ∈ connectedFamilies G L 3, ∑ x ∈ T,
          |infiniteCenteredCoefficient L (T.erase x)| * infiniteMarginal x L) +
        FamilyIndependentMass.independentMass (connectedFamilies G L 3) L) := by
      rw [sum_add_distrib]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (ConnectedTriplePositiveReduction.pair_cost G L hL) le_rfl) hK

end PaperP1.ConnectedTripleLowCrossing
