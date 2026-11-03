module

public import PaperP1.Arithmetic.ActivePhysicalPrimeGroups
public import PaperP1.Coding.CoordinateErasureRank

/-! # Killing large composite groups leaves two small-kernel values in every block

All groups and their endpoint set are those of the initial regularized M.
No new support pool or recovery property is asserted after the erasure.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveGroupKernelErasure

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.ActivePhysicalPrimeGroups PaperP1.LargeOddKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module

local instance codeAddCommGroup (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)

local instance physicalAddCommGroup (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

abbrev remaining (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ) (Y : ℝ) :=
  CoordinateForms.zeroCoordinates (U := M) (label X L M) (badPositions X L M H Y)

theorem dimension_cost (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ) (Y : ℝ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (hι : Fintype.card ι ≤ 3) :
    Module.finrank F₂ M ≤ 3 * (largeGroups X L M H Y).card + Module.finrank F₂ (remaining X L M H Y) := by
  have hd := CoordinateErasureRank.dimension_cost (U := M) (label X L M) (badPositions X L M H Y)
  have hc := badPositions_card X L M H Y hX hH hι
  change Module.finrank F₂ M ≤ (badPositions X L M H Y).card +
    Module.finrank F₂ (remaining X L M H Y) at hd
  omega

theorem two_small_per_block (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H d t : ℕ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (hι : Fintype.card ι ≤ d + 1)
    (hd : 1 ≤ d) (hd₂ : d ≤ 2) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M d t)
    (hinj : ∀ i, Function.Injective ((projection X L i).comp M.subtype))
    (Y : ℝ) (hY : 1 ≤ Y)
    (hlarge : 3 * (largeGroups X L M H Y).card < Module.finrank F₂ M) :
    ∀ i : ι, ∃ a b : Fin (L + 1), a ≠ b ∧
      (largeOddKernel H (value X L (i, a)) : ℝ) ≤ Y ^ PhysicalLabelSupportCount.supportBound d t (t - 1) ∧
      (largeOddKernel H (value X L (i, b)) : ℝ) ≤ Y ^ PhysicalLabelSupportCount.supportBound d t (t - 1) := by
  classical
  let R := remaining X L M H Y
  have hdim : 0 < Module.finrank F₂ R := by
    have hh := dimension_cost X L M H Y hX hH (by omega)
    change Module.finrank F₂ M ≤ 3 * (largeGroups X L M H Y).card + Module.finrank F₂ R at hh
    omega
  intro i
  let f := ((projection X L i).comp M.subtype).comp R.subtype
  have hfinj : Function.Injective f := (hinj i).comp Subtype.val_injective
  have heven (u : R) : (∑ j, f u j) = 0 := by
    change (∑ j, u.val.val.val (i, j)) = 0
    simpa only [startVertexSum_apply] using u.val.val.property.1 i
  obtain ⟨a, b, hab, ha, hb⟩ := CoordinateErasureRank.two_active (U := R) f hfinj heven hdim
  have hcap (j : Fin (L + 1)) (hj : (LinearMap.proj j).comp f ≠ 0) :
      (largeOddKernel H (value X L (i, j)) : ℝ) ≤ Y ^ PhysicalLabelSupportCount.supportBound d t (t - 1) := by
    have hj' : (label X L M (i, j)).comp R.subtype ≠ 0 := hj
    obtain ⟨hactive, hnotbad⟩ := CoordinateErasureRank.surviving_active (U := M)
      (label X L M) (badPositions X L M H Y) (i, j) hj'
    exact kernel_cap_away_from_bad X L M H d t hX hH hι hd hd₂ ht hno Y hY (i, j) hactive hnotbad
  exact ⟨a, b, hab, hcap a ha, hcap b hb⟩

end PaperP1.ActiveGroupKernelErasure
