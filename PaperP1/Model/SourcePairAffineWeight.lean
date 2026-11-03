module

public import PaperP1.Arithmetic.SourcePairKernelComparison
public import PaperP1.Model.PairLossWeights

/-! # The exact arithmetic pair Fourier weight with local kernels and compatibility retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairAffineWeight

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedPairRankLoss

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def eta (x y L : ℕ) : ℕ := by
  classical
  exact if 0 < infiniteJointMoment L {x, y} then 1 else 0

theorem eta_eq_compatibility (M x y L : ℕ) (hL : 0 < L)
    (hcut : ∀ z ∈ ({x, y} : Finset ℕ), z + L ≤ M) :
    eta x y L = if Compatible (familyStartSystem M L (fun z : ({x, y} : Finset ℕ) ↦ z.val))
      (familyStartRhs L) then 1 else 0 := by
  classical
  simp only [eta, infiniteJointMoment_pos_iff_jointCompatible M L {x, y} hL hcut]

theorem joint_zero_or_nominal (x y L : ℕ) (hL : 0 < L) :
    infiniteJointMoment L {x, y} = 0 ∨ infiniteJointMoment L {x, y} =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
  let z : Fin 2 → ℕ := ![x, y]
  have hs : FiniteFamilyEnumeration.tupleSet z = {x, y} := by
    simp [FiniteFamilyEnumeration.tupleSet, z, univ_fin2]
  have hspan : (⨆ i, squareClassSpace (z i) L : Submodule F₂ (ℕ →₀ F₂)) =
      squareClassSpace x L ⊔ squareClassSpace y L := ContactPairMass.pair_span x y L
  have hmass := PrescribedTupleRank.joint_zero_or_rank (fun _ ↦ startRhs L) z
  rw [JointTupleSupport.prescribed_eq_support z hL, hs, hspan] at hmass
  rcases hmass with hz | hq
  · exact Or.inl hz
  · right
    let R := Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)
    have hx := SourcePairKernelComparison.local_rank_identity x L
    have hy := SourcePairKernelComparison.local_rank_identity y L
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
    have hcap : R ≤ 2 * L := by dsimp [R]; omega
    have hsum : R + pairLoss x y L = 2 * L := by unfold pairLoss; dsimp [R] at *; omega
    have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) hsum
    rw [pow_add, show 2 * L = L * 2 by omega, pow_mul] at hpow
    have heq : (2 ^ R : ℝ)⁻¹ = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
      field_simp
      nlinarith only [hpow]
    exact hq.trans heq

theorem joint_formula (x y L : ℕ) (hL : 0 < L) :
    infiniteJointMoment L {x, y} =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * ((eta x y L : ℝ) * (2 ^ pairLoss x y L : ℝ)) := by
  classical
  rcases joint_zero_or_nominal x y L hL with hz | hq
  · simp only [eta, hz, lt_self_iff_false, ite_false, Nat.cast_zero, zero_mul, mul_zero]
  · have hpos : 0 < infiniteJointMoment L {x, y} := by rw [hq]; positivity
    simpa only [eta, ite_true, hpos, Nat.cast_one, one_mul] using hq

def signedWeight (x y L : ℕ) : ℝ := (eta x y L : ℝ) * (2 ^ pairLoss x y L : ℝ) - 1

theorem scaled_signed_weight (x y L : ℕ) (hL : 0 < L) :
    ((2 ^ L : ℝ)⁻¹) ^ 2 * signedWeight x y L =
      infiniteJointMoment L {x, y} - ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  rw [joint_formula x y L hL]
  unfold signedWeight
  ring

end PaperP1.SourcePairAffineWeight
