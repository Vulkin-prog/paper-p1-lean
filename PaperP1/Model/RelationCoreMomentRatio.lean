module

public import PaperP1.Model.RelationCoreWitnesses
public import PaperP1.Affine.RelationCoreCounting
public import PaperP1.Model.CompatibleRunCentered

/-! # The literal compatible ten-core ratio q <= 2c below size 257 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationCoreMomentRatio

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

local instance relationCoreRatioPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem centered_count (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hq : 0 < infiniteJointMoment L I) :
    infiniteCenteredCoefficient L I = (∏ x ∈ I, infiniteMarginal x L) *
      (fullSupportRelations (fun x : I ↦ squareClassSpace x.val L)).card := by
  classical
  have hq' : 0 < infiniteFamilyJointMoment L (fun x : I ↦ x.val) := by
    rw [← infiniteJointMoment_eq_family_subtype]
    exact hq
  have h := PaperP1.CompatibleRunCentered.square_class_count L (fun x : I ↦ x.val) hL hq'
  have hcard : Nat.card {s : (x : I) → squareClassFamilySpace L (fun x : I ↦ x.val) x //
      IsFullSupportRelation (squareClassFamilySpace L (fun x : I ↦ x.val)) s} =
      (fullSupportRelations (fun x : I ↦ squareClassSpace x.val L)).card := by
    rw [Nat.card_eq_fintype_card]
    simpa only [fullSupportRelations] using
      (Fintype.card_subtype (IsFullSupportRelation (fun x : I ↦ squareClassSpace x.val L)))
  rw [hcard] at h
  rw [← infiniteCenteredCoefficient_eq_family_subtype] at h
  have hprod : (∏ x : I, infiniteMarginal x.val L) = ∏ x ∈ I, infiniteMarginal x L := by
    rw [univ_eq_attach]
    exact prod_attach I (fun x ↦ infiniteMarginal x L)
  rwa [hprod] at h

theorem ten_core_ratio (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hq : 0 < infiniteJointMoment L I) (hsize : I.card ≤ 256) (hcore : Core 10 L I) :
    infiniteJointMoment L I ≤ 2 * infiniteCenteredCoefficient L I := by
  let M := I.sup fun x ↦ x + L
  have hcut : ∀ x ∈ I, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  have hcount := PaperP1.RelationCoreCounting.half_full_support
    (fun x ↦ squareClassSpace x L) I hsize (by
      intro x hx
      exact hcore x hx)
  have hprod : 0 ≤ ∏ x ∈ I, infiniteMarginal x L :=
    prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have h := mul_le_mul_of_nonneg_left hcount hprod
  rw [infiniteJointMoment_exact_of_pos M L I hL hcut hq, centered_count L I hL hq]
  exact h.trans_eq (by ring)

end PaperP1.RelationCoreMomentRatio
