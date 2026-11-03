module

public import PaperP1.Affine.RelationCorePeeling
public import PaperP1.Arithmetic.HeavyPhysicalRelations
public import PaperP1.Model.MultiAnchorRelationFamilies

/-! # Actual relation cores have the block-dependent physical anchor witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationCoreWitnesses

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RelationProjectionRank

local instance relationCoreWitnessPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def Core (t L : ℕ) (I : Finset ℕ) : Prop :=
  ∀ x ∈ I, t - 1 ≤ loss (fun x ↦ squareClassSpace x L) I x

theorem witnesses (t L : ℕ) (ht : Even t) (I : Finset ℕ) (hcore : Core t L I)
    (hpos : ∀ x ∈ I, 0 < x) (Y T : ℝ) :
    PaperP1.MultiAnchorRelationFamilies.Witnesses t (L + 1) Y T I := by
  intro a _hunmarked
  have hprojection := loss_eq_dimension (fun x ↦ squareClassSpace x L) I a
  have hrank : t - 1 ≤ Module.finrank F₂
      (LinearMap.range (PaperP1.PhysicalWindowRelations.effectiveProjection
        (fun x : I ↦ x.val) L a)) := by
    exact (hcore a.val a.property).trans_eq hprojection
  exact PaperP1.HeavyPhysicalRelations.exists_relation (fun x : I ↦ x.val) L
    (fun x ↦ hpos x.val x.property) a t ht hrank

theorem exists_ten_core (L : ℕ) (I : Finset ℕ) :
    ∃ D ⊆ I, relativeNullityOn (fun x ↦ squareClassSpace x L) I ≤
      relativeNullityOn (fun x ↦ squareClassSpace x L) D + 8 * (I.card - D.card) ∧ Core 10 L D := by
  obtain ⟨D, hDI, hbudget, hstop⟩ :=
    PaperP1.RelationCorePeeling.exists_core (fun x ↦ squareClassSpace x L) I 8
  refine ⟨D, hDI, hbudget, ?_⟩
  intro x hx
  have h := hstop x hx
  omega

end PaperP1.RelationCoreWitnesses
