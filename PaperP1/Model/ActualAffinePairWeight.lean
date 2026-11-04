module

public import PaperP1.Model.PairLossWeights
public import PaperP1.Model.PrivateUnitCovariance

/-! # Literal signed affine pair weight with all local relations retained

The compatibility bit is determined by the actual joint event. The
normalization is the ambient critical word rate, not an actual marginal
product. Private pairs have their exact predecessor-signed unit sum.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualAffinePairWeight

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedPairRankLoss

local instance actualAffinePairPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def compatibility (x y L : ℕ) : Bool := decide (0 < infiniteJointMoment L {x, y})

def weight (x y L : ℕ) : ℝ := (2 ^ L : ℝ) ^ 2 * infiniteJointMoment L {x, y} - 1

theorem rank_rate {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    (2 ^ Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) : ℝ)⁻¹ =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
  let R := Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have hrx := LocalRunRank.squareClass_rank_le x L hx
  have hry := LocalRunRank.squareClass_rank_le y L hy
  have hcap : R ≤ 2 * L := by dsimp [R]; omega
  have hsum : R + pairLoss x y L = 2 * L := by unfold pairLoss; dsimp [R] at *; omega
  have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) hsum
  rw [pow_add, show 2 * L = L * 2 by omega, pow_mul] at hpow
  change (2 ^ R : ℝ)⁻¹ = _
  field_simp
  nlinarith only [hpow]

theorem joint_binary {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hL : 0 < L) :
    infiniteJointMoment L {x, y} = 0 ∨ infiniteJointMoment L {x, y} =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
  let z : Fin 2 → ℕ := ![x, y]
  have hs : FiniteFamilyEnumeration.tupleSet z = {x, y} := by
    simp [FiniteFamilyEnumeration.tupleSet, z, univ_fin2]
  have h := PaperP1.PrescribedTupleRank.joint_zero_or_rank (fun _ ↦ startRhs L) z
  rw [PaperP1.JointTupleSupport.prescribed_eq_support z hL, hs,
    PaperP1.ContactPairMass.pair_span x y L, rank_rate hx hy] at h
  exact h

theorem weight_eq_compatibility {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hL : 0 < L) :
    weight x y L = (if compatibility x y L then 1 else 0) * (2 ^ pairLoss x y L : ℝ) - 1 := by
  rcases joint_binary hx hy hL with hz | hmass
  · simp only [weight, compatibility, hz, lt_self_iff_false, decide_false, Bool.false_eq_true, ite_false, mul_zero, zero_mul]
  · have hpos : 0 < infiniteJointMoment L {x, y} := by rw [hmass]; positivity
    have hc : compatibility x y L = true := decide_eq_true hpos
    rw [hc]
    simp only [ite_true, one_mul]
    rw [weight, hmass]
    field_simp

theorem abs_weight_le {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hL : 0 < L) :
    |weight x y L| ≤ (2 ^ pairLoss x y L : ℝ) := by
  have hp : (1 : ℝ) ≤ 2 ^ pairLoss x y L := one_le_pow₀ (by norm_num)
  rw [weight_eq_compatibility hx hy hL]
  cases compatibility x y L with
  | false => simpa using hp
  | true =>
    simp only [ite_true, one_mul]
    rw [abs_of_nonneg (by linarith only [hp])]
    linarith only [hp]

theorem private_weight_eq_units {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxy : x ≠ y) (hL : 0 < L)
    (hp : PaperP1.FiniteEvenSquareClasses.Private (PaperP1.NormalizedWindowSets.union a b x y L)) :
    weight x y L = PaperP1.PrivateUnitCovariance.signedUnitSum a b x y L := by
  rw [weight, PaperP1.PrivateUnitCovariance.private_pair_mass ha hb hx hy hxy hL hp]
  field_simp
  ring

theorem weight_comm (x y L : ℕ) : weight x y L = weight y x L := by
  simp only [weight, pair_comm x y]

end PaperP1.ActualAffinePairWeight
