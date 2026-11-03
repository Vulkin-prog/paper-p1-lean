module

public import PaperP1.Model.TripleProbabilityBound
public import PaperP1.Model.HomogeneousSourcePairMass

/-! # Actual affine and homogeneous weights of a primitive full-rank triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveTripleWeights

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.TripleProbabilityBound

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem primitive_pair_good {L : ℕ} (X : Fin 3 → ℕ) (hinj : Function.Injective X)
    (hprim : Primitive L X)
    (hrank0 : Module.finrank F₂ (squareClassSpace (X 0) L) = L)
    (hrank1 : Module.finrank F₂ (squareClassSpace (X 1) L) = L) : PairGood L X := by
  have hxy : X 0 ≠ X 1 := fun heq ↦ (by decide : (0 : Fin 3) ≠ 1) (hinj heq)
  have hx2 : X 2 ∈ tupleSet X := mem_image.mpr ⟨2, mem_univ _, rfl⟩
  have hnot : X 2 ∉ ({X 0, X 1} : Finset ℕ) := by
    intro hx
    rcases mem_insert.mp hx with hx | hx
    · exact (by decide : (2 : Fin 3) ≠ 0) (hinj hx)
    · exact (by decide : (2 : Fin 3) ≠ 1) (hinj (mem_singleton.mp hx))
  have hproper : ({X 0, X 1} : Finset ℕ) ⊂ tupleSet X := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨pair_subset_tupleSet X, ?_⟩
    intro heq
    apply hnot
    rw [heq]
    exact hx2
  have hzero := hprim.2 {X 0, X 1} hproper
  rw [PaperP1.RetainedNullity.nullity_pair_eq_intersection (fun x ↦ squareClassSpace x L) (X 0) (X 1) hxy] at hzero
  have hdisj : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L) :=
    disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hzero)
  exact ⟨hxy, hrank0, hrank1, hdisj⟩

theorem homogeneous_pair_eq {L : ℕ} (X : Fin 3 → ℕ) (hx : 0 < X 0) (hy : 0 < X 1)
    (hgood : PairGood L X) :
    HomogeneousRunMass.probability L {X 0, X 1} = ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace (X 0) L) (squareClassSpace (X 1) L)
  rw [hgood.2.2.2.eq_bot, finrank_bot, add_zero, hgood.2.1, hgood.2.2.1] at hdim
  have hloss : NormalizedPairRankLoss.pairLoss (X 0) (X 1) L = 0 := by
    unfold NormalizedPairRankLoss.pairLoss
    omega
  rw [HomogeneousSourcePairMass.probability_pair hx hy, hloss, pow_zero, mul_one]

theorem homogeneous_triple_le {L : ℕ} (X : Fin 3 → ℕ) (hx : 0 < X 0) (hy : 0 < X 1)
    (hgood : PairGood L X) :
    HomogeneousRunMass.probability L (tupleSet X) ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 :=
  (HomogeneousRunMass.probability_antitone L (pair_subset_tupleSet X)).trans_eq (homogeneous_pair_eq X hx hy hgood)

end PaperP1.PrimitiveTripleWeights
