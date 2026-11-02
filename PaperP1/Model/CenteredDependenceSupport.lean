module

public import PaperP1.Affine.RelationCoordinateSpan
public import PaperP1.Model.SquareClassFourier
public import PaperP1.Model.CanonicalRunComponents

/-! # Every nonzero actual centered coefficient has a dependent target at each position -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CenteredDependenceSupport

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem exists_full_support (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) (hc : infiniteCenteredCoefficient L I ≠ 0) :
    ∃ s : (i : I) → squareClassSpace i.val L,
      IsFullSupportRelation (fun i : I ↦ squareClassSpace i.val L) s := by
  classical
  let M := I.sup fun x ↦ x + L
  have hcut : ∀ x : I, x.val + L ≤ M := fun x ↦ le_sup (f := fun x ↦ x + L) x.property
  have hcenter : infiniteFamilyCenteredMoment L (fun x : I ↦ x.val) ≠ 0 := by
    rwa [← infiniteCenteredCoefficient_eq_family_subtype]
  exact squareClass_full_relation_of_ne_zero M L (fun x : I ↦ x.val) hL hcut
    (fun x ↦ hp x.val x.property) hcenter

theorem every_target (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) (hc : infiniteCenteredCoefficient L I ≠ 0)
    {z : ℕ} (hz : z ∈ I) :
    squareClassSpace z L ⊓ SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) (I.erase z) ≠ ⊥ := by
  obtain ⟨s, hs⟩ := exists_full_support L hL I hp hc
  exact RelationCoordinateSpan.full_support_intersection (fun x ↦ squareClassSpace x L) I s hs ⟨z, hz⟩

theorem nullity_pos (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : I.Nonempty)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) (hc : infiniteCenteredCoefficient L I ≠ 0) :
    0 < relativeNullityOn (fun x ↦ squareClassSpace x L) I := by
  classical
  obtain ⟨i, hi⟩ := hI
  let : Nonempty I := ⟨⟨i, hi⟩⟩
  let M := I.sup fun x ↦ x + L
  have hcut : ∀ x : I, x.val + L ≤ M := fun x ↦ le_sup (f := fun x ↦ x + L) x.property
  have hbound := squareClass_centered_moment_bound M L (fun x : I ↦ x.val) hL hcut
    (fun x ↦ hp x.val x.property)
  by_contra hn
  have hz : relativeNullity (squareClassFamilySpace L (fun x : I ↦ x.val)) = 0 :=
    Nat.eq_zero_of_not_pos hn
  rw [hz, pow_zero, sub_self, mul_zero, ← infiniteCenteredCoefficient_eq_family_subtype] at hbound
  exact hc (abs_nonpos_iff.mp hbound)

theorem inserted_target (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (z : ℕ) (hz : z ∉ e)
    (hp : ∀ x ∈ insert z e, 0 < infiniteMarginal x L)
    (hc : infiniteCenteredCoefficient L (insert z e) ≠ 0) :
    squareClassSpace z L ⊓ SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e ≠ ⊥ := by
  simpa only [erase_insert hz] using every_target L hL (insert z e) hp hc (mem_insert_self z e)

end PaperP1.CenteredDependenceSupport
