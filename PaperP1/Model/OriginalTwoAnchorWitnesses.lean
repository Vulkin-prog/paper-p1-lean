module

public import PaperP1.Model.RelationCoreWitnesses
public import PaperP1.Model.RelativeWindowFamilies

/-! # Coordinatewise original participation gives actual two-anchor witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalTwoAnchorWitnesses

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RelationCoreWitnesses

local instance originalTwoAnchorPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance (S : Submodule F₂ (ℕ →₀ F₂)) : AddCommGroup S :=
  Submodule.addCommGroup (R := F₂) (M := ℕ →₀ F₂) S

local instance (S : Submodule F₂ (ℕ →₀ F₂)) : Module F₂ S := S.module

theorem participating_core (L : ℕ) (I : Finset ℕ) (hw : PaperP1.RelativeWindowFamilies.Witnesses L ⊥ I) :
    Core 2 L I := by
  intro x hx
  let a : I := ⟨x, hx⟩
  obtain ⟨u, hu, hsum⟩ := hw a
  let r : PaperP1.PrimitiveCoordinateProjection.Kernel (fun x ↦ squareClassSpace x L) I :=
    ⟨u, by
      change (∑ j : I, (u j).val) = 0
      simpa only [Submodule.mem_bot] using hsum⟩
  let p : PaperP1.PrimitiveCoordinateProjection.Kernel (fun x ↦ squareClassSpace x L) I →ₗ[F₂]
      squareClassSpace x L := PaperP1.PrimitiveCoordinateProjection.projection
        (fun x ↦ squareClassSpace x L) I a
  let v : LinearMap.range p := ⟨u a, ⟨r, rfl⟩⟩
  have hv : v ≠ 0 := fun hz ↦ hu (congrArg Subtype.val hz)
  have hdim : 0 < Module.finrank F₂ (LinearMap.range p) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  rw [PaperP1.RelationProjectionRank.loss_eq_dimension _ I a]
  exact hdim

theorem connected_core (L : ℕ) (I : Finset ℕ) (hsize : 2 ≤ I.card)
    (hconn : PaperP1.ConnectedWindowFamilies.Connected L I) : Core 2 L I := by
  classical
  let : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [Fintype.card_coe] using (show 1 < I.card by omega))
  apply participating_core L I
  intro i
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨u, hsum, hne⟩ := PaperP1.ConnectedRelations.coordinate_relation
    (fun x : I ↦ squareClassSpace x.val L) hconn i j (fun hij ↦ hji hij.symm)
  refine ⟨u, (fun hz ↦ hne (congrArg Subtype.val hz)), ?_⟩
  simpa only [relationAddition_apply, Submodule.mem_bot] using hsum

theorem connected_witnesses (L : ℕ) (I : Finset ℕ) (hsize : 2 ≤ I.card)
    (hconn : PaperP1.ConnectedWindowFamilies.Connected L I) (hpos : ∀ x ∈ I, 0 < x) (Y T : ℝ) :
    PaperP1.MultiAnchorRelationFamilies.Witnesses 2 (L + 1) Y T I :=
  witnesses 2 L (by decide) I (connected_core L I hsize hconn) hpos Y T

end PaperP1.OriginalTwoAnchorWitnesses
