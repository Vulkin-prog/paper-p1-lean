module

public import PaperP1.Arithmetic.ShortBasisFiniteConstruction

/-! # Actual subspaces and bases of complete relations with literal physical projections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisActualSpace

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LocalDefectBound
  PaperP1.LargePrimeOccurrences PaperP1.LargePrimeGraph PaperP1.MediumPrimeColumns
  PaperP1.MediumPrimeIncidence PaperP1.ShortBasisComponentStage

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableEq (largePrimeGraph x y L).ConnectedComponent := Classical.decEq _
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

def firstPhysical (x y L : ℕ) : completeRelationCode x y L →ₗ[F₂] (Fin (L + 1) → F₂) where
  toFun w i := w.val (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondPhysical (x y L : ℕ) : completeRelationCode x y L →ₗ[F₂] (Fin (L + 1) → F₂) where
  toFun w i := w.val (Sum.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def commonClasses (x y L : ℕ) : completeRelationCode x y L →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParityMap x L).comp (firstPhysical x y L)

def physicalCoefficients (x y L : ℕ) : completeRelationCode x y L →ₗ[F₂] (Occurrence L →₀ F₂) :=
  (Finsupp.linearEquivFunOnFinite F₂ F₂ (Occurrence L)).symm.toLinearMap.comp
    (completeRelationCode x y L).subtype

structure Certificate (x y L : ℕ) where
  space : Submodule F₂ (completeRelationCode x y L)
  index : Type
  basis : Module.Basis index F₂ space
  first_injective : Function.Injective ((firstPhysical x y L).comp space.subtype)
  second_injective : Function.Injective ((secondPhysical x y L).comp space.subtype)
  common_injective : Function.Injective ((commonClasses x y L).comp space.subtype)

theorem physical_support_card_le (x y L : ℕ) (w : completeRelationCode x y L) :
    (physicalCoefficients x y L w).support.card ≤ 2 * (L + 1) := by
  have h := (physicalCoefficients x y L w).support.card_le_univ
  simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using h

theorem finite_certificate (x y L z M r d : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hpow : (mediumPrimes L z).card + 1 < d ^ r) :
    ∃ cert : Certificate x y L,
      (retainedComponents x y L z M).card - (2 * d) * ((mediumPrimes L z).card + 1) -
          (primeCount z + 2) ≤ Module.finrank F₂ cert.space ∧
      ∀ i, (physicalCoefficients x y L (cert.basis i).val).support.card ≤
        M * (2 * r + 1) * (primeCount z + 3) := by
  obtain ⟨U, hU, I, b, hdim, hsupport, hfirst, hsecond, hcommon⟩ :=
    ShortBasisFiniteConstruction.complete_space x y L z M r d hx hy hpow
  let f := ShortBasisFinalCut.relationMap x y L z (retainedComponents x y L z M)
    hx hy (retained_subset_free x y L z M) U hU
  have hf : Function.Injective f := ShortBasisFinalCut.relationMap_injective x y L z
    (retainedComponents x y L z M) hx hy (retained_subset_free x y L z M) U hU
  let W := LinearMap.range f
  let e := LinearEquiv.ofInjective f hf
  have hfirst' : Function.Injective ((firstPhysical x y L).comp W.subtype) := by
    intro a c h
    obtain ⟨a₀, rfl⟩ := e.surjective a
    obtain ⟨c₀, rfl⟩ := e.surjective c
    exact congrArg e (hfirst h)
  have hsecond' : Function.Injective ((secondPhysical x y L).comp W.subtype) := by
    intro a c h
    obtain ⟨a₀, rfl⟩ := e.surjective a
    obtain ⟨c₀, rfl⟩ := e.surjective c
    exact congrArg e (hsecond h)
  have hcommon' : Function.Injective ((commonClasses x y L).comp W.subtype) := by
    intro a c h
    obtain ⟨a₀, rfl⟩ := e.surjective a
    obtain ⟨c₀, rfl⟩ := e.surjective c
    exact congrArg e (hcommon h)
  let cert : Certificate x y L := ⟨W, I, b.map e, hfirst', hsecond', hcommon'⟩
  refine ⟨cert, hdim, ?_⟩
  intro i
  change (physicalCoefficients x y L (((b.map e) i).val)).support.card ≤ _
  rw [Module.Basis.map_apply]
  exact hsupport i

theorem projections_nonzero (x y L : ℕ) (cert : Certificate x y L) (w : cert.space) (hw : w ≠ 0) :
    firstPhysical x y L w.val ≠ 0 ∧ secondPhysical x y L w.val ≠ 0 ∧ commonClasses x y L w.val ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hw
    apply cert.first_injective
    exact h.trans (map_zero ((firstPhysical x y L).comp cert.space.subtype)).symm
  · intro h
    apply hw
    apply cert.second_injective
    exact h.trans (map_zero ((secondPhysical x y L).comp cert.space.subtype)).symm
  · intro h
    apply hw
    apply cert.common_injective
    exact h.trans (map_zero ((commonClasses x y L).comp cert.space.subtype)).symm

theorem commonClasses_equal (x y L : ℕ) (w : completeRelationCode x y L) :
    commonClasses x y L w = vertexParityMap y L (secondPhysical x y L w) := by
  have hw := ((mem_completeRelationCode w.val).mp w.property).1
  have hsplit : pairVertexParityMap x y L w.val =
      vertexParityMap x L (firstPhysical x y L w) + vertexParityMap y L (secondPhysical x y L w) := by
    change (∑ v : Occurrence L, w.val v • parityVec (twoStartCompleteVertexLabel x y L v)) =
      (∑ i, w.val (Sum.inl i) • parityVec (startCompleteVertexLabel x L i)) +
        ∑ i, w.val (Sum.inr i) • parityVec (startCompleteVertexLabel y L i)
    simp only [Fintype.sum_sum_type, twoStartCompleteVertexLabel]
  rw [hsplit] at hw
  apply Finsupp.ext
  intro p
  have hp := congrArg (fun a : ℕ →₀ F₂ ↦ a p) hw
  simp only [Finsupp.add_apply, Finsupp.zero_apply] at hp
  exact CharTwo.add_eq_zero.mp hp

def selected {J : Type*} [Fintype J] (w : J → F₂) : Finset J := by
  classical
  exact univ.filter (fun j ↦ w j ≠ 0)

theorem sum_eq_selected_card {J : Type*} [Fintype J] (w : J → F₂) :
    (∑ j, w j) = ((selected w).card : F₂) := by
  classical
  calc
    (∑ j, w j) = ∑ j ∈ selected w, (1 : F₂) := by
      rw [selected, sum_filter]
      apply sum_congr rfl
      intro j _hj
      have hbit : w j = 0 ∨ w j = 1 := by generalize w j = z; revert z; decide
      rcases hbit with hzero | hone
      · simp [hzero]
      · simp [hone]
    _ = _ := by simp

theorem selected_nonempty {J : Type*} [Fintype J] (w : J → F₂) (hw : w ≠ 0) :
    (selected w).Nonempty := by
  classical
  by_contra h
  apply hw
  funext j
  by_contra hj
  exact h ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩

theorem commonClasses_mem_intersection (x y L : ℕ) (w : completeRelationCode x y L) :
    commonClasses x y L w ∈ (squareClassSpace x L ⊓ squareClassSpace y L : Submodule F₂ (ℕ →₀ F₂)) := by
  obtain ⟨_hp, hl, hr⟩ := (mem_completeRelationCode w.val).mp w.property
  constructor
  · exact ⟨⟨firstPhysical x y L w, hl⟩, rfl⟩
  · rw [commonClasses_equal]
    exact ⟨⟨secondPhysical x y L w, hr⟩, rfl⟩

theorem nonzero_even_selections (x y L : ℕ) (cert : Certificate x y L) (w : cert.space) (hw : w ≠ 0) :
    (selected (firstPhysical x y L w.val)).Nonempty ∧
      Even (selected (firstPhysical x y L w.val)).card ∧
      (selected (secondPhysical x y L w.val)).Nonempty ∧
      Even (selected (secondPhysical x y L w.val)).card ∧ commonClasses x y L w.val ≠ 0 := by
  obtain ⟨hl, hr, hc⟩ := projections_nonzero x y L cert w hw
  obtain ⟨_hp, hleft, hright⟩ := (mem_completeRelationCode w.val.val).mp w.val.property
  have heven {J : Type} [Fintype J] (v : J → F₂) (hv : ∑ j, v j = 0) : Even (selected v).card := by
    rw [sum_eq_selected_card, ZMod.natCast_eq_zero_iff, ← even_iff_two_dvd] at hv
    exact hv
  exact ⟨selected_nonempty _ hl, heven _ hleft, selected_nonempty _ hr, heven _ hright, hc⟩

end PaperP1.ShortBasisActualSpace
