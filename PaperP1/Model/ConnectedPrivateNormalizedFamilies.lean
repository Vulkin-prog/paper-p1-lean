module

public import PaperP1.Model.PrivateNormalizedFamilyRank
public import PaperP1.Arithmetic.ConnectedValueUnions

/-! # Exact private affine probabilities require only connected overlap, without a common value -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedPrivateNormalizedFamilies

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedWindowSets
  PaperP1.FiniteEvenSquareClasses PaperP1.PrivateNormalizedFamilies PaperP1.PrivateNormalizedFamilyRank
  PaperP1.ConnectedValueUnions

theorem connected_normalized_space {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    space (valueUnion c X L) = (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) := by
  have hh := connected_union_space (fun i ↦ normalized (c i) (X i) L)
    (fun i ↦ normalized_nonempty (c i) (X i) L) hconn
  have hspaces : (fun i ↦ space (normalized (c i) (X i) L)) = (fun i ↦ squareClassSpace (X i) L) :=
    funext (fun i ↦ space_normalized (hc i) (hX i))
  change space (valueUnion c X L) = iSup (fun i ↦ space (normalized (c i) (X i) L)) at hh
  rwa [hspaces] at hh

theorem connected_joint_rank {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hprivate : Private (valueUnion c X L))
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) = (valueUnion c X L).card - 1 := by
  rw [← connected_normalized_space c X hc hX hconn]
  exact finrank_space _ hprivate

theorem connected_actual_probability {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hprivate : Private (valueUnion c X L)) (hex : Exclusive c X L)
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = (2 ^ ((valueUnion c X L).card - 1) : ℝ)⁻¹ := by
  rw [actual_joint_rank c X hc hX hL hprivate hex, connected_joint_rank c X hc hX hprivate hconn]

theorem connected_probability_nullity {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hprivate : Private (valueUnion c X L)) (hex : Exclusive c X L)
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) (ρ : ℕ)
    (hdim : (valueUnion c X L).card - 1 + ρ = r * L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ ρ : ℝ) := by
  rw [connected_actual_probability c X hc hX hL hprivate hex hconn]
  exact rank_weight_identity L r _ ρ hdim

end PaperP1.ConnectedPrivateNormalizedFamilies
