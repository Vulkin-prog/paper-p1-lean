module

public import PaperP1.Arithmetic.ShortBasisActualSpace

/-! # Every free nontrivial component survives the full small-prime cut

The component's private large prime makes its first square-class image injective.
Thus no local rank hypothesis is needed in this lower bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentIntersectionLower

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeGraph
  PaperP1.ComponentProjectionInjectivity PaperP1.ShortBasisFinalCut
  PaperP1.MediumPrimeIncidence PaperP1.MediumPrimeColumns PaperP1.LocalDefectBound

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y J : ℕ) : DecidableRel (largePrimeGraph x y J).Adj := Classical.decRel _
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) :
    AddCommGroup U := Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

theorem finite_bound (x y J : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (Q : Finset (largePrimeGraph x y J).ConnectedComponent) (hQ : IsFreeFamily x y J Q) :
    Q.card ≤ FreeComponentRank.pairIntersectionRank x y J + primeCount (10 * (J + 1)) + 2 := by
  classical
  let z := 10 * (J + 1)
  let U : Submodule F₂ (Q → F₂) := ⊤
  have hU : U ≤ LinearMap.ker (actualMap x y J z Q) := by
    intro w _hw
    apply (actual_kernel_iff x y J z Q w).mpr
    intro p hp
    have hh := (mem_mediumPrimes J z p).mp hp
    dsimp [z] at hh
    omega
  let f := relationMap x y J z Q hx hy hQ U hU
  let g : CutSpace x y J z Q U →ₗ[F₂]
      ↥(squareClassSpace x J ⊓ squareClassSpace y J) :=
    ((ShortBasisActualSpace.commonClasses x y J).comp f).codRestrict _
      (fun w ↦ ShortBasisActualSpace.commonClasses_mem_intersection x y J (f w))
  have hg : Function.Injective g := by
    intro u v huv
    apply square_class_image_injective x y J z Q hx hy hQ U
    exact congrArg Subtype.val huv
  have hmono := LinearMap.finrank_le_finrank_of_injective hg
  have hd := dimension_lower x y J z Q U
  have htop : Module.finrank F₂ U = Q.card := by
    simp only [U, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [htop] at hd
  change Module.finrank F₂ (CutSpace x y J z Q U) ≤ FreeComponentRank.pairIntersectionRank x y J at hmono
  dsimp [z] at hd hmono
  omega

/-- The complete free-component population needs no local rank bound. -/
theorem all_nontrivial_bound (x y J : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    LargePrimeGraphResolution.nontrivialComponentCount x y J ≤
      FreeComponentRank.pairIntersectionRank x y J + primeCount (10 * (J + 1)) + 2 := by
  exact finite_bound x y J hx hy
    (PinnedGraphResolution.nontrivialUnpinnedComponents (largePrimeGraph x y J)
      (LargePrimeGraphResolution.pinnedVertices x y J)) Subset.rfl

end PaperP1.ComponentIntersectionLower
