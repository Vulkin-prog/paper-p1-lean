module

public import PaperP1.Arithmetic.ContactWindowSpan
public import PaperP1.Model.PrescribedTupleRank

/-! # An exact-contact pair has the rank of the single full union window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactPairMass

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass

local instance contactPairMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

abbrev pair (x y : ℕ) : Fin 2 → ℕ := ![x, y]

theorem pair_span (x y L : ℕ) :
    (⨆ i, squareClassSpace (pair x y i) L : Submodule F₂ (ℕ →₀ F₂)) =
      squareClassSpace x L ⊔ squareClassSpace y L := by
  apply le_antisymm
  · exact iSup_le (Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩)
  · exact sup_le (le_iSup (fun i ↦ squareClassSpace (pair x y i) L) 0)
      (le_iSup (fun i ↦ squareClassSpace (pair x y i) L) 1)

theorem joint_le_union_rank {L x : ℕ} (c : ℕ → Fin L → F₂) (hx : 0 < x) :
    joint L c (pair x (x + L)) ≤ (2 ^ Module.finrank F₂ (squareClassSpace x (2 * L)) : ℝ)⁻¹ := by
  have h := PrescribedTupleRank.joint_le_rank c (pair x (x + L))
  rwa [pair_span, ContactWindowSpan.joined_space hx] at h

theorem joint_le_relation_ratio {L x : ℕ} (c : ℕ → Fin L → F₂) (hx : 0 < x) :
    joint L c (pair x (x + L)) ≤
      (2 ^ Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (2 * L + 1)) : ℝ) /
        (2 ^ (2 * L) : ℝ) := by
  have h := PaperP1.LocalRunRank.squareClass_rank_add_relation_rank (L := 2 * L) hx
  have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) h
  rw [pow_add] at hpow
  have hidentity : (2 ^ Module.finrank F₂ (squareClassSpace x (2 * L)) : ℝ)⁻¹ =
      (2 ^ Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (2 * L + 1)) : ℝ) /
        (2 ^ (2 * L) : ℝ) := by
    field_simp
    nlinarith only [hpow]
  exact (joint_le_union_rank c hx).trans_eq hidentity

end PaperP1.ContactPairMass
