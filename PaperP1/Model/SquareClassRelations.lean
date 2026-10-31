module

public import PaperP1.Affine.StartCharacterSpace
public import PaperP1.Model.StartFourier
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Relative square-class relations and actual character relations

The coordinate pairing is injective on the whole represented prime-parity
space. It therefore preserves relations between every supported family of
effective square-class spaces, in addition to the individual local ranks.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Affine

namespace PaperP1.Model

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι]

abbrev squareClassFamilySpace (L : ℕ) (g : ι → ℕ) (i : ι) : Submodule F₂ (ℕ →₀ F₂) :=
  squareClassSpace (g i) L

instance squareClassFamilySpaceFintype (L : ℕ) (g : ι → ℕ) (i : ι) :
    Fintype (squareClassFamilySpace L g i) := squareClassSpaceFintype _ _

def squareClassFamilyEquivRow (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M) :
    ((i : ι) → squareClassFamilySpace L g i) ≃ₗ[F₂] ((i : ι) → startFamilySpace M L g i) :=
  LinearEquiv.piCongrRight fun i => squareClassEquivRow (hcut i)

omit [Fintype ι] in
@[simp]
theorem squareClassFamilyEquivRow_apply (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M)
    (s : (i : ι) → squareClassFamilySpace L g i) (i : ι) :
    (squareClassFamilyEquivRow M L g hcut s i).val = parityPairing M (s i).val := rfl

theorem sum_squareClassFamily_mem_bounded (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (s : (i : ι) → squareClassFamilySpace L g i) :
    relationAddition (squareClassFamilySpace L g) s ∈ boundedPrimeParity M := by
  apply Submodule.sum_mem
  intro i _
  exact squareClassSpace_le_boundedPrimeParity (hcut i) (s i).property

theorem relationAddition_squareClassFamilyEquivRow (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (s : (i : ι) → squareClassFamilySpace L g i) :
    relationAddition (startFamilySpace M L g) (squareClassFamilyEquivRow M L g hcut s) =
      parityPairing M (relationAddition (squareClassFamilySpace L g) s) := by
  simp only [relationAddition_apply, squareClassFamilyEquivRow_apply, map_sum]

theorem squareClassFamily_relation_zero_iff (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (s : (i : ι) → squareClassFamilySpace L g i) :
    relationAddition (startFamilySpace M L g) (squareClassFamilyEquivRow M L g hcut s) = 0 ↔
      relationAddition (squareClassFamilySpace L g) s = 0 := by
  rw [relationAddition_squareClassFamilyEquivRow]
  exact parityPairing_eq_zero_iff_of_bounded M _
    (sum_squareClassFamily_mem_bounded M L g hcut s)

omit [Fintype ι] in
theorem squareClassFamily_full_support_iff (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (s : (i : ι) → squareClassFamilySpace L g i) :
    HasFullSupport (startFamilySpace M L g) (squareClassFamilyEquivRow M L g hcut s) ↔
      HasFullSupport (squareClassFamilySpace L g) s := by
  constructor
  · intro h i hz
    apply h i
    change squareClassEquivRow (hcut i) (s i) = 0
    rw [hz, map_zero]
  · intro h i hz
    change squareClassEquivRow (hcut i) (s i) = 0 at hz
    apply h i
    apply (squareClassEquivRow (hcut i)).injective
    change squareClassEquivRow (hcut i) (s i) = squareClassEquivRow (hcut i) 0
    rw [map_zero]
    exact hz

theorem squareClassFamily_full_relation_iff (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (s : (i : ι) → squareClassFamilySpace L g i) :
    IsFullSupportRelation (startFamilySpace M L g) (squareClassFamilyEquivRow M L g hcut s) ↔
      IsFullSupportRelation (squareClassFamilySpace L g) s := by
  rw [IsFullSupportRelation, IsFullSupportRelation,
    squareClassFamily_full_support_iff, squareClassFamily_relation_zero_iff]

theorem map_squareClass_relation_kernel (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) :
    (LinearMap.ker (relationAddition (squareClassFamilySpace L g))).map
        (squareClassFamilyEquivRow M L g hcut).toLinearMap =
      LinearMap.ker (relationAddition (startFamilySpace M L g)) := by
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (squareClassFamily_relation_zero_iff M L g hcut s).mpr hs
  · intro hr
    change relationAddition (startFamilySpace M L g) r = 0 at hr
    let s := (squareClassFamilyEquivRow M L g hcut).symm r
    have hs : relationAddition (squareClassFamilySpace L g) s = 0 := by
      apply (squareClassFamily_relation_zero_iff M L g hcut s).mp
      simpa only [s, LinearEquiv.apply_symm_apply] using hr
    exact ⟨s, hs, (squareClassFamilyEquivRow M L g hcut).apply_symm_apply r⟩

def squareClassRelationEquivRow (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M) :
    LinearMap.ker (relationAddition (squareClassFamilySpace L g)) ≃ₗ[F₂]
      LinearMap.ker (relationAddition (startFamilySpace M L g)) :=
  (squareClassFamilyEquivRow M L g hcut).ofSubmodules _ _
    (map_squareClass_relation_kernel M L g hcut)

theorem relativeNullity_squareClassFamily_eq_rows (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) :
    relativeNullity (squareClassFamilySpace L g) = relativeNullity (startFamilySpace M L g) :=
  (squareClassRelationEquivRow M L g hcut).finrank_eq

end PaperP1.Model
