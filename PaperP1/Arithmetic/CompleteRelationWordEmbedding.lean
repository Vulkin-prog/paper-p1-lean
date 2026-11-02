module

public import PaperP1.Arithmetic.ShortBasisActualSpace
public import PaperP1.Arithmetic.FormalWordEncoding

/-! # Literal integer-offset words of actual complete relations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompleteRelationWordEmbedding

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ShortBasisActualSpace
  PaperP1.CurveWordMap PaperP1.LargePrimeOccurrences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : AddCommGroup Words := inferInstance
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

def finiteCoefficients {J : Type*} [Fintype J] : (J → F₂) →ₗ[F₂] (J →₀ F₂) :=
  (Finsupp.linearEquivFunOnFinite F₂ F₂ J).symm.toLinearMap

theorem finiteCoefficients_apply {J : Type*} [Fintype J] (w : J → F₂) (j : J) :
    finiteCoefficients w j = w j := rfl

theorem finiteCoefficients_support {J : Type*} [Fintype J] (w : J → F₂) :
    (finiteCoefficients w).support = selected w := by
  classical
  apply Finset.ext
  intro j
  simp only [Finsupp.mem_support_iff, finiteCoefficients_apply, selected, mem_filter, mem_univ, true_and]

def offset (L : ℕ) (i : Fin (L + 1)) : ℤ := (i.val : ℤ) - 1

theorem offset_injective (L : ℕ) : Function.Injective (offset L) := by
  intro i j h
  apply Fin.ext
  dsimp [offset] at h
  omega

def offsetEmbedding (L : ℕ) : Fin (L + 1) ↪ ℤ := ⟨offset L, offset_injective L⟩

theorem offset_bound (L : ℕ) (i : Fin (L + 1)) : |offset L i| ≤ (L + 1 : ℕ) := by
  have hi := i.isLt
  rw [abs_le]
  dsimp [offset]
  omega

def offsetMap (L : ℕ) : (Fin (L + 1) → F₂) →ₗ[F₂] (ℤ →₀ F₂) :=
  (Finsupp.lmapDomain F₂ F₂ (offsetEmbedding L)).comp finiteCoefficients

theorem offsetMap_injective (L : ℕ) : Function.Injective (offsetMap L) :=
  (Finsupp.mapDomain_injective (offsetEmbedding L).injective).comp
    (Finsupp.linearEquivFunOnFinite F₂ F₂ (Fin (L + 1))).symm.injective

theorem offsetMap_support (L : ℕ) (w : Fin (L + 1) → F₂) :
    (offsetMap L w).support = (selected w).map (offsetEmbedding L) := by
  change (Finsupp.mapDomain (offsetEmbedding L) (finiteCoefficients w)).support = _
  rw [Finsupp.support_mapDomain_embedding, finiteCoefficients_support]

theorem offsetMap_support_card (L : ℕ) (w : Fin (L + 1) → F₂) :
    (offsetMap L w).support.card = (selected w).card := by
  rw [offsetMap_support, card_map]

theorem offsetMap_support_bound (L : ℕ) (w : Fin (L + 1) → F₂) (u : ℤ)
    (hu : u ∈ (offsetMap L w).support) : |u| ≤ (L + 1 : ℕ) := by
  rw [offsetMap_support] at hu
  obtain ⟨i, _hi, rfl⟩ := mem_map.mp hu
  exact offset_bound L i

def wordMap (x y L : ℕ) : completeRelationCode x y L →ₗ[F₂] Words :=
  ((offsetMap L).comp (firstPhysical x y L)).prod ((offsetMap L).comp (secondPhysical x y L))

theorem wordMap_injective (x y L : ℕ) : Function.Injective (wordMap x y L) := by
  intro a b h
  have hl := offsetMap_injective L (congrArg Prod.fst h)
  have hr := offsetMap_injective L (congrArg Prod.snd h)
  apply Subtype.ext
  funext v
  cases v with
  | inl i => exact congrFun hl i
  | inr i => exact congrFun hr i

theorem selected_sum_type {I J : Type*} [Fintype I] [Fintype J] (w : (I ⊕ J) → F₂) :
    (selected w).card = (selected (fun i ↦ w (Sum.inl i))).card +
      (selected (fun j ↦ w (Sum.inr j))).card := by
  classical
  simp only [selected, card_eq_sum_ones, sum_filter, Fintype.sum_sum_type]

theorem wordMap_support_card (x y L : ℕ) (w : completeRelationCode x y L) :
    (wordMap x y L w).1.support.card + (wordMap x y L w).2.support.card =
      (physicalCoefficients x y L w).support.card := by
  change (offsetMap L (firstPhysical x y L w)).support.card +
    (offsetMap L (secondPhysical x y L w)).support.card = (finiteCoefficients w.val).support.card
  rw [offsetMap_support_card, offsetMap_support_card, finiteCoefficients_support, selected_sum_type]
  rfl

theorem wordMap_even (x y L : ℕ) (w : completeRelationCode x y L) :
    Even (wordMap x y L w).1.support.card ∧ Even (wordMap x y L w).2.support.card := by
  obtain ⟨_hp, hl, hr⟩ := (mem_completeRelationCode w.val).mp w.property
  have heven (v : Fin (L + 1) → F₂) (hv : ∑ i, v i = 0) : Even (selected v).card := by
    rw [sum_eq_selected_card, ZMod.natCast_eq_zero_iff, ← even_iff_two_dvd] at hv
    exact hv
  constructor
  · change Even (offsetMap L (firstPhysical x y L w)).support.card
    rw [offsetMap_support_card]
    exact heven _ hl
  · change Even (offsetMap L (secondPhysical x y L w)).support.card
    rw [offsetMap_support_card]
    exact heven _ hr

def wordSpace (x y L : ℕ) (cert : Certificate x y L) : Submodule F₂ Words :=
  cert.space.map (wordMap x y L)

def wordEquiv (x y L : ℕ) (cert : Certificate x y L) : cert.space ≃ₗ[F₂] wordSpace x y L cert :=
  Submodule.equivMapOfInjective (wordMap x y L) (wordMap_injective x y L) cert.space

def wordBasis (x y L : ℕ) (cert : Certificate x y L) :
    Module.Basis cert.index F₂ (wordSpace x y L cert) := cert.basis.map (wordEquiv x y L cert)

theorem wordSpace_finrank (x y L : ℕ) (cert : Certificate x y L) :
    Module.finrank F₂ (wordSpace x y L cert) = Module.finrank F₂ cert.space :=
  (wordEquiv x y L cert).finrank_eq.symm

theorem wordSpace_even (x y L : ℕ) (cert : Certificate x y L) (w : wordSpace x y L cert) :
    Even w.val.1.support.card ∧ Even w.val.2.support.card := by
  obtain ⟨r, _hr, he⟩ := Submodule.mem_map.mp w.property
  rw [← he]
  exact wordMap_even x y L r

theorem wordSpace_offsets_bound (x y L : ℕ) (cert : Certificate x y L) (w : wordSpace x y L cert) :
    (∀ u ∈ w.val.1.support, |u| ≤ (L + 1 : ℕ)) ∧
      (∀ v ∈ w.val.2.support, |v| ≤ (L + 1 : ℕ)) := by
  obtain ⟨r, _hr, he⟩ := Submodule.mem_map.mp w.property
  rw [← he]
  exact ⟨offsetMap_support_bound L (firstPhysical x y L r),
    offsetMap_support_bound L (secondPhysical x y L r)⟩

theorem wordSpace_projections_injective (x y L : ℕ) (cert : Certificate x y L) :
    Function.Injective (fun w : wordSpace x y L cert ↦ w.val.1) ∧
      Function.Injective (fun w : wordSpace x y L cert ↦ w.val.2) := by
  constructor
  · intro a b h
    obtain ⟨a₀, rfl⟩ := (wordEquiv x y L cert).surjective a
    obtain ⟨b₀, rfl⟩ := (wordEquiv x y L cert).surjective b
    exact congrArg (wordEquiv x y L cert) (cert.first_injective (offsetMap_injective L h))
  · intro a b h
    obtain ⟨a₀, rfl⟩ := (wordEquiv x y L cert).surjective a
    obtain ⟨b₀, rfl⟩ := (wordEquiv x y L cert).surjective b
    exact congrArg (wordEquiv x y L cert) (cert.second_injective (offsetMap_injective L h))

theorem wordBasis_support_card (x y L : ℕ) (cert : Certificate x y L) (i : cert.index) :
    (wordBasis x y L cert i).val.1.support.card + (wordBasis x y L cert i).val.2.support.card =
      (physicalCoefficients x y L (cert.basis i).val).support.card := by
  change (((cert.basis.map (wordEquiv x y L cert)) i).val).1.support.card +
    (((cert.basis.map (wordEquiv x y L cert)) i).val).2.support.card = _
  rw [Module.Basis.map_apply]
  exact wordMap_support_card x y L (cert.basis i).val

end PaperP1.CompleteRelationWordEmbedding
