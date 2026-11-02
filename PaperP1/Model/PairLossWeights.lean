module

public import PaperP1.Model.PrescribedTupleRank
public import PaperP1.Model.ContactPairMass
public import PaperP1.Model.JointTupleSupport
public import PaperP1.Arithmetic.NormalizedPairRankLoss
public import PaperP1.Arithmetic.FixedChannelSourceGeometry

/-! # Actual pair joint mass from full pair loss, without regularity or compatibility -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairLossWeights

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedPairRankLoss

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem joint_bound {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hL : 0 < L) :
    infiniteJointMoment L {x, y} ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
  let z : Fin 2 → ℕ := ![x, y]
  have hs : FiniteFamilyEnumeration.tupleSet z = {x, y} := by
    simp [FiniteFamilyEnumeration.tupleSet, z, univ_fin2]
  have hspan : (⨆ i, squareClassSpace (z i) L : Submodule F₂ (ℕ →₀ F₂)) =
      squareClassSpace x L ⊔ squareClassSpace y L := by
    exact ContactPairMass.pair_span x y L
  have hmass := PrescribedTupleRank.joint_le_rank (fun _ ↦ startRhs L) z
  rw [JointTupleSupport.prescribed_eq_support z hL, hs, hspan] at hmass
  let R := Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have hrx := LocalRunRank.squareClass_rank_le x L hx
  have hry := LocalRunRank.squareClass_rank_le y L hy
  have hcap : R ≤ 2 * L := by dsimp [R]; omega
  have hsum : R + pairLoss x y L = 2 * L := by unfold pairLoss; dsimp [R] at *; omega
  have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) hsum
  rw [pow_add, show 2 * L = L * 2 by omega, pow_mul] at hpow
  have heq : (2 ^ R : ℝ)⁻¹ = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss x y L : ℝ) := by
    field_simp
    nlinarith only [hpow]
  exact hmass.trans_eq heq

theorem unit_order {N a b L : ℕ} (hN : 0 < N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {xy : ℕ × ℕ}
    (hxy : xy ∈ FixedChannelSourceGeometry.unitSources N a b L) : xy.1 < xy.2 := by
  obtain ⟨hxy, u, hu⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  exact ActualSourceTranslations.source_pair_order hN hab hlarge u.1 u.2
    (DyadicEndpointPairs.mem_sourcePairs.mpr ⟨hx, hy, NormalizedUnitCount.mem_units.mp hu⟩)

end PaperP1.PairLossWeights
