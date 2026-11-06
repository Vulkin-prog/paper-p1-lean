module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # A nonempty finite-type fibre over an algebraically closed field has an actual rational lift -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.AlgClosedFieldPointLift

open AlgebraicGeometry CategoryTheory Limits

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

theorem exists_point (g : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (hX : Nonempty X) : ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ g = 𝟙 _ := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have hne : (Set.univ : Set X).Nonempty := by
    obtain ⟨x⟩ := hX
    exact ⟨x, Set.mem_univ _⟩
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    hne isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint g x hx, pointOfClosedPoint_comp g x hx⟩

theorem exists_lift (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Spec (CommRingCat.of K) ⟶ Y)
    (hy : y (IsLocalRing.closedPoint K) ∈ Set.range f) :
    ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y := by
  have hne : Nonempty (pullback f y : Scheme.{u}) := by
    have hm : IsLocalRing.closedPoint K ∈ Set.range (pullback.snd f y) := by
      rw [Scheme.Pullback.range_snd]
      exact hy
    obtain ⟨x, _⟩ := hm
    exact ⟨x⟩
  obtain ⟨p, hp⟩ := exists_point (pullback.snd f y) hne
  refine ⟨p ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hp, Category.id_comp]

end PaperP1.AlgClosedFieldPointLift
