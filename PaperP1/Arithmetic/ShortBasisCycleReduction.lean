module

public import PaperP1.Algebra.BinaryIncidenceShortVectors
public import PaperP1.Arithmetic.ComponentSelectionSupport
public import PaperP1.Arithmetic.ShortBasisFinalCut

/-! # The actual short-basis construction reduced to local short incidence vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisCycleReduction

open Finset PaperP1.Arithmetic PaperP1.LocalDefectBound PaperP1.LargePrimeOccurrences PaperP1.LargePrimeGraph
  PaperP1.MediumPrimeColumns PaperP1.MediumPrimeIncidence PaperP1.ShortBasisComponentStage
  PaperP1.ComponentSelectionSupport PaperP1.GreedyShortKernel
  PaperP1.BinaryIncidenceAugmentation PaperP1.BinaryIncidenceShortVectors

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableEq (largePrimeGraph x y L).ConnectedComponent := Classical.decEq _
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

def mediumFinsuppMap (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q →₀ F₂) →ₗ[F₂] (mediumPrimes L z → F₂) :=
  (actualMap x y L z Q).comp (Finsupp.linearEquivFunOnFinite F₂ F₂ Q).toLinearMap

def ShortVectors (x y L z M r k : ℕ) : Prop :=
  ∀ S : Finset (retainedComponents x y L z M), r < S.card →
    HasShortVector (mediumFinsuppMap x y L z (retainedComponents x y L z M)) S k

theorem actual_incidence_presentation (x y L z M : ℕ) :
    ∃ left right : retainedComponents x y L z M → Option (mediumPrimes L z),
      finsuppIncidence left right = augment.comp
        (mediumFinsuppMap x y L z (retainedComponents x y L z M)) := by
  obtain ⟨left, right, he, _hk⟩ := retained_incidence_model x y L z M
  refine ⟨left, right, ?_⟩
  apply LinearMap.ext
  intro w
  rw [finite_apply, he]
  rfl

theorem medium_space_from_short_vectors (x y L z M r k : ℕ) (hfind : ShortVectors x y L z M r k) :
    ∃ (n : ℕ) (U : Submodule F₂ (retainedComponents x y L z M → F₂)) (b : Module.Basis (Fin n) F₂ U),
      U ≤ LinearMap.ker (actualMap x y L z (retainedComponents x y L z M)) ∧
      (retainedComponents x y L z M).card - r ≤ Module.finrank F₂ U ∧
      ∀ i, (ShortBasisFinalCut.physicalMap x y L (retainedComponents x y L z M) U (b i)).support.card ≤ M * k := by
  classical
  let Q := retainedComponents x y L z M
  let e := Finsupp.linearEquivFunOnFinite F₂ F₂ Q
  let f := mediumFinsuppMap x y L z Q
  let g : (Q →₀ F₂) →ₗ[F₂] (Occurrence L →₀ F₂) :=
    (physicalSelection x y L Q).comp e.toLinearMap
  have hsingle (c : Q) : (g (Finsupp.single c 1)).support.card ≤ M := by
    change (physicalSelection x y L Q ((Finsupp.linearEquivFunOnFinite F₂ F₂ Q) (Finsupp.single c 1))).support.card ≤ M
    rw [Finsupp.linearEquivFunOnFinite_single]
    exact retained_single_card x y L z M c
  obtain ⟨n, U₀, b₀, hdim, hphysical⟩ := GreedyShortKernel.physical_subspace_basis
    (K := F₂) (V := mediumPrimes L z → F₂) (E := Q) f g univ r k M
    (fun S _hS hlarge ↦ hfind S hlarge) hsingle
  let m : LinearMap.ker f →ₗ[F₂] (Q → F₂) := e.toLinearMap.comp (LinearMap.ker f).subtype
  have hm : Function.Injective m := e.injective.comp (LinearMap.ker f).subtype_injective
  let U := U₀.map m
  let eU : U₀ ≃ₗ[F₂] U := Submodule.equivMapOfInjective m hm U₀
  let b : Module.Basis (Fin n) F₂ U := b₀.map eU
  have hU : U ≤ LinearMap.ker (actualMap x y L z Q) := by
    intro w hw
    obtain ⟨v, _hv, hvw⟩ := Submodule.mem_map.mp hw
    rw [← hvw]
    exact v.property
  refine ⟨n, U, b, hU, ?_, ?_⟩
  · have hn : Q.card - r ≤ Module.finrank F₂ U₀ := by
      simpa only [card_univ, Fintype.card_coe] using hdim
    exact hn.trans_eq eU.finrank_eq
  · intro i
    have heq : ShortBasisFinalCut.physicalMap x y L Q U (b i) = g (b₀ i).val.val := by
      change ShortBasisFinalCut.physicalMap x y L Q U ((b₀.map eU) i) = g (b₀ i).val.val
      rw [Module.Basis.map_apply]
      change physicalSelection x y L Q ((Submodule.equivMapOfInjective m hm U₀ (b₀ i)).val) = g (b₀ i).val.val
      rw [Submodule.coe_equivMapOfInjective_apply]
      rfl
    rw [heq]
    exact hphysical i

theorem complete_space_from_short_vectors (x y L z M r k : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hfind : ShortVectors x y L z M r k) :
    ∃ (U : Submodule F₂ (retainedComponents x y L z M → F₂))
      (hU : U ≤ LinearMap.ker (actualMap x y L z (retainedComponents x y L z M)))
      (I : Type) (b : Module.Basis I F₂
        (ShortBasisFinalCut.CutSpace x y L z (retainedComponents x y L z M) U)),
      (retainedComponents x y L z M).card - r - (primeCount z + 2) ≤
        Module.finrank F₂ (LinearMap.range (ShortBasisFinalCut.relationMap x y L z
          (retainedComponents x y L z M) hx hy (retained_subset_free x y L z M) U hU)) ∧
      (∀ i, (ShortBasisFinalCut.physicalMap x y L (retainedComponents x y L z M) U
        (b i).val).support.card ≤ M * k * (primeCount z + 3)) ∧
      Function.Injective ((ComponentProjectionInjectivity.firstProjection x y L
        (retainedComponents x y L z M)).comp (ShortBasisFinalCut.coefficientMap x y L z
          (retainedComponents x y L z M) U)) ∧
      Function.Injective ((ComponentProjectionInjectivity.secondProjection x y L
        (retainedComponents x y L z M)).comp (ShortBasisFinalCut.coefficientMap x y L z
          (retainedComponents x y L z M) U)) ∧
      Function.Injective ((ComponentProjectionInjectivity.firstClasses x y L
        (retainedComponents x y L z M)).comp (ShortBasisFinalCut.coefficientMap x y L z
          (retainedComponents x y L z M) U)) := by
  obtain ⟨n, U, b₀, hU, hdim, hphysical⟩ :=
    medium_space_from_short_vectors x y L z M r k hfind
  obtain ⟨I, b, hb⟩ := ShortBasisFinalCut.exists_cut_basis x y L z
    (retainedComponents x y L z M) U b₀ (M * k) hphysical
  obtain ⟨hfirst, hsecond⟩ := ShortBasisFinalCut.physical_projections_injective x y L z
    (retainedComponents x y L z M) hx hy (retained_subset_free x y L z M) U
  refine ⟨U, hU, I, b, ?_, hb, hfirst, hsecond, ?_⟩
  · exact (Nat.sub_le_sub_right hdim (primeCount z + 2)).trans
      (ShortBasisFinalCut.complete_image_dimension_lower x y L z
        (retainedComponents x y L z M) hx hy (retained_subset_free x y L z M) U hU)
  · exact ShortBasisFinalCut.square_class_image_injective x y L z
      (retainedComponents x y L z M) hx hy (retained_subset_free x y L z M) U

end PaperP1.ShortBasisCycleReduction
