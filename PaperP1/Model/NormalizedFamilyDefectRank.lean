module

public import PaperP1.Model.EvenNormalizedFamilies
public import PaperP1.Model.ConnectedPrivateNormalizedFamilies
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # Actual family rank and probability bounds with the entire merged-value defect retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedFamilyDefectRank

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies PaperP1.FiniteResidualRank

theorem common_rank_defect {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L) :
    (valueUnion c X L).card - 1 ≤
      Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) +
      Module.finrank F₂ (valueKernel (valueUnion c X L)) := by
  have hh := NormalizedPairRankLoss.dimension_le_space_add_kernel (valueUnion c X L)
  rwa [PrivateNormalizedFamilyRank.common_normalized_space hr c X hc hX a ha] at hh

theorem connected_rank_defect {r L : ℕ} (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    (valueUnion c X L).card - 1 ≤
      Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) +
      Module.finrank F₂ (valueKernel (valueUnion c X L)) := by
  have hh := NormalizedPairRankLoss.dimension_le_space_add_kernel (valueUnion c X L)
  rwa [ConnectedPrivateNormalizedFamilies.connected_normalized_space c X hc hX hconn] at hh

theorem actual_joint_le_rank {r L : ℕ} (X : Fin r → ℕ) (hL : 0 < L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      (2 ^ Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) : ℝ)⁻¹ := by
  have hh := PrescribedTupleRank.joint_le_rank (L := L) (fun _ ↦ startRhs L) X
  rwa [JointTupleSupport.prescribed_eq_support X hL] at hh

theorem common_probability_upper {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      (2 ^ ((valueUnion c X L).card - 1 - Module.finrank F₂ (valueKernel (valueUnion c X L))) : ℝ)⁻¹ := by
  have hh := common_rank_defect hr c X hc hX a ha
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show
    (valueUnion c X L).card - 1 - Module.finrank F₂ (valueKernel (valueUnion c X L)) ≤
      Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) by omega)
  exact (actual_joint_le_rank X hL).trans
    (by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp)

theorem connected_probability_upper {r L : ℕ} (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      (2 ^ ((valueUnion c X L).card - 1 - Module.finrank F₂ (valueKernel (valueUnion c X L))) : ℝ)⁻¹ := by
  have hh := connected_rank_defect c X hc hX hconn
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show
    (valueUnion c X L).card - 1 - Module.finrank F₂ (valueKernel (valueUnion c X L)) ≤
      Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) by omega)
  exact (actual_joint_le_rank X hL).trans
    (by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp)

end PaperP1.NormalizedFamilyDefectRank
