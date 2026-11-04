module

public import PaperP1.Arithmetic.TargetWindowRank
public import PaperP1.Model.OneTargetCrossing
public import PaperP1.Model.AsymmetricJointWeight
public import PaperP1.Model.HomogeneousRunMass

/-! # The full target quotient rank bounds the actual pair-conditioned mass

No regularity or positivity is required of the new marginal. Affine
incompatibility is retained by the upper bound on the actual joint mass.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairTargetQuotientProbability

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

def addedRank (x y z L : ℕ) : ℕ :=
  Module.finrank F₂ ↥((squareClassSpace x L ⊔ squareClassSpace y L) ⊔ squareClassSpace z L) -
    Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)

theorem rank_add_cross (x y z L : ℕ) :
    addedRank x y z L + AsymmetricJointWeight.crossRank x y z L =
      Module.finrank F₂ (squareClassSpace z L) := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (squareClassSpace x L ⊔ squareClassSpace y L) (squareClassSpace z L)
  have hm : Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) ≤
      Module.finrank F₂ ↥((squareClassSpace x L ⊔ squareClassSpace y L) ⊔ squareClassSpace z L) :=
    Submodule.finrank_mono le_sup_left
  unfold addedRank AsymmetricJointWeight.crossRank
  omega

theorem added_le {x y z L : ℕ} (hz : 0 < z) : addedRank x y z L ≤ L := by
  have hh := rank_add_cross x y z L
  have hr := LocalRunRank.squareClass_rank_le z L hz
  omega

theorem deficiency_add {x y z L : ℕ} (hz : 0 < z) :
    TargetWindowRank.deficiency ∅ x y z L + addedRank x y z L = L := by
  rw [TargetWindowRank.deficiency_empty]
  change L - addedRank x y z L + addedRank x y z L = L
  exact Nat.sub_add_cancel (added_le hz)

theorem marginal_upper (z L : ℕ) (hL : 0 < L) :
    infiniteMarginal z L ≤ (2 ^ Module.finrank F₂ (squareClassSpace z L) : ℝ)⁻¹ := by
  by_cases hp : 0 < infiniteMarginal z L
  · exact (LocalRunRank.infiniteMarginal_eq_squareClass_rank hL hp).le
  · exact (not_lt.mp hp).trans (by positivity)

theorem joint_upper {x y z L : ℕ} (hL : 0 < L) (hzx : z ≠ x) (hzy : z ≠ y) :
    infiniteJointMoment L {x, y, z} ≤
      infiniteJointMoment L {x, y} * (2 ^ addedRank x y z L : ℝ)⁻¹ := by
  have hfresh : z ∉ ({x, y} : Finset ℕ) := by simp [hzx, hzy]
  have hh := OneTargetCrossing.joint_upper {x, y} L z hL hfresh
  have hs : OneTargetCrossing.sourceSpace {x, y} L = squareClassSpace x L ⊔ squareClassSpace y L := by
    rw [OneTargetCrossing.sourceSpace, span_insert]
    simp [span]
  have hc : OneTargetCrossing.rank {x, y} L z = AsymmetricJointWeight.crossRank x y z L := by
    unfold OneTargetCrossing.rank AsymmetricJointWeight.crossRank
    rw [hs, inf_comm]
  rw [hc] at hh
  have hset : insert z ({x, y} : Finset ℕ) = {x, y, z} :=
    (insert_comm z x {y}).trans (congrArg (insert x) (pair_comm z y))
  rw [hset] at hh
  have hp := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) (rank_add_cross x y z L)
  rw [pow_add] at hp
  have heq : (2 ^ Module.finrank F₂ (squareClassSpace z L) : ℝ)⁻¹ *
      (2 ^ AsymmetricJointWeight.crossRank x y z L : ℝ) = (2 ^ addedRank x y z L : ℝ)⁻¹ := by
    rw [← hp]
    field_simp
  calc
    _ ≤ infiniteJointMoment L {x, y} * infiniteMarginal z L *
        (2 ^ AsymmetricJointWeight.crossRank x y z L : ℝ) := hh
    _ ≤ infiniteJointMoment L {x, y} *
        (2 ^ Module.finrank F₂ (squareClassSpace z L) : ℝ)⁻¹ *
        (2 ^ AsymmetricJointWeight.crossRank x y z L : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (marginal_upper z L hL)
        (infiniteJointMoment_nonneg L _)) (by positivity)
    _ = _ := by rw [mul_assoc, heq]

end PaperP1.PairTargetQuotientProbability
