module

public import PaperP1.Algebra.SparseConstraintBasis
public import PaperP1.Arithmetic.MediumPrimeIncidence
public import PaperP1.Affine.SmallPrimePairConstraints

/-! # The actual final small-prime and parity cut after the medium-prime kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisFinalCut

universe u

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LocalDefectBound
  PaperP1.LargePrimeOccurrences PaperP1.LargePrimeGraph PaperP1.ComponentSelection
  PaperP1.ComponentProjectionInjectivity PaperP1.MediumPrimeColumns PaperP1.MediumPrimeIncidence

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev ConstraintTarget (z : ℕ) := (Fin (primeCount z) → F₂) × F₂ × F₂

def vertexConstraints (x y L z : ℕ) : (Occurrence L → F₂) →ₗ[F₂] ConstraintTarget z where
  toFun w := (fun i ↦ pairVertexParityMap x y L w (smallPrime z i), pairLeftSum L w, pairRightSum L w)
  map_add' _ _ := by
    apply Prod.ext
    · funext i; simp
    · apply Prod.ext <;> simp
  map_smul' _ _ := by
    apply Prod.ext
    · funext i; simp [Finsupp.smul_apply]
    · apply Prod.ext <;> simp

def constraints (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q → F₂) →ₗ[F₂] ConstraintTarget z :=
  (vertexConstraints x y L z).comp (selection (largePrimeGraph x y L) Q)

theorem constraintTarget_finrank (z : ℕ) :
    Module.finrank F₂ (ConstraintTarget z) = primeCount z + 2 := by
  simp only [ConstraintTarget, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Module.finrank_self]

theorem mem_constraints_ker (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (w : Q → F₂) : w ∈ LinearMap.ker (constraints x y L z Q) ↔
      (∀ i : Fin (primeCount z), pairVertexParityMap x y L (selection (largePrimeGraph x y L) Q w) (smallPrime z i) = 0) ∧
      (∑ i, selection (largePrimeGraph x y L) Q w (Sum.inl i)) = 0 ∧
      (∑ i, selection (largePrimeGraph x y L) Q w (Sum.inr i)) = 0 := by
  constructor
  · intro h
    exact ⟨fun i ↦ congrArg (fun d : ConstraintTarget z ↦ d.1 i) h,
      congrArg (fun d : ConstraintTarget z ↦ d.2.1) h,
      congrArg (fun d : ConstraintTarget z ↦ d.2.2) h⟩
  · rintro ⟨hp, hl, hr⟩
    exact Prod.ext (funext hp) (Prod.ext hl hr)

theorem complete_of_medium_and_small (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (w : Q → F₂)
    (hmedium : w ∈ LinearMap.ker (actualMap x y L z Q))
    (hsmall : w ∈ LinearMap.ker (constraints x y L z Q)) :
    selection (largePrimeGraph x y L) Q w ∈ completeRelationCode x y L := by
  have hlarge := selection_mem_largePrimeSolution x y L Q hx hy hQ w
  have hm := (actual_kernel_iff x y L z Q w).mp hmedium
  obtain ⟨hs, hl, hr⟩ := (mem_constraints_ker x y L z Q w).mp hsmall
  apply (mem_completeRelationCode _).mpr
  refine ⟨?_, hl, hr⟩
  apply Finsupp.ext
  intro p
  by_cases hp : p.Prime
  · by_cases hbig : 10 * (L + 1) < p
    · rw [pairVertexParityMap_coord]
      exact (mem_largePrimeSolution_iff_boundary_prime_equations.mp hlarge) p ⟨hp, hbig⟩
    · by_cases hsmallp : p ≤ z
      · obtain ⟨i, hi⟩ := smallPrime_covers hp hsmallp
        simpa only [hi, Finsupp.zero_apply] using hs i
      · rw [pairVertexParityMap_coord]
        exact hm p ((mem_mediumPrimes L z p).mpr ⟨hp, by omega, by omega⟩)
  · rw [pairVertexParityMap_coord]
    apply sum_eq_zero
    intro v _hv
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_prime _ hp, Nat.cast_zero, mul_zero]

abbrev CutSpace (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (U : Submodule F₂ (Q → F₂)) := LinearMap.ker ((constraints x y L z Q).comp U.subtype)

def coefficientMap (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (U : Submodule F₂ (Q → F₂)) : CutSpace x y L z Q U →ₗ[F₂] (Q → F₂) :=
  U.subtype.comp (CutSpace x y L z Q U).subtype

def relationMap (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (U : Submodule F₂ (Q → F₂))
    (hU : U ≤ LinearMap.ker (actualMap x y L z Q)) :
    CutSpace x y L z Q U →ₗ[F₂] completeRelationCode x y L :=
  ((selection (largePrimeGraph x y L) Q).comp (coefficientMap x y L z Q U)).codRestrict
    (completeRelationCode x y L) (fun w ↦ complete_of_medium_and_small x y L z Q hx hy hQ
      w.val.val (hU w.val.property) w.property)

theorem relationMap_injective (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (U : Submodule F₂ (Q → F₂))
    (hU : U ≤ LinearMap.ker (actualMap x y L z Q)) : Function.Injective (relationMap x y L z Q hx hy hQ U hU) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply selection_injective (largePrimeGraph x y L) Q
  exact congrArg Subtype.val h

theorem dimension_lower (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (U : Submodule F₂ (Q → F₂)) [Module.Finite F₂ U] :
    Module.finrank F₂ U - (primeCount z + 2) ≤ Module.finrank F₂ (CutSpace x y L z Q U) := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (K := F₂) (V := U) (V₂ := ConstraintTarget z)
    ((constraints x y L z Q).comp U.subtype)
  have hrange := (LinearMap.range ((constraints x y L z Q).comp U.subtype)).finrank_le
  rw [constraintTarget_finrank] at hrange
  change _ + Module.finrank F₂ (CutSpace x y L z Q U) = Module.finrank F₂ U at hrank
  omega

theorem coefficientMap_injective (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (U : Submodule F₂ (Q → F₂)) : Function.Injective (coefficientMap x y L z Q U) :=
  U.subtype_injective.comp (CutSpace x y L z Q U).subtype_injective

theorem physical_projections_injective (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (U : Submodule F₂ (Q → F₂)) :
    Function.Injective ((firstProjection x y L Q).comp (coefficientMap x y L z Q U)) ∧
      Function.Injective ((secondProjection x y L Q).comp (coefficientMap x y L z Q U)) :=
  ⟨(firstProjection_injective x y L Q hx hy hQ).comp (coefficientMap_injective x y L z Q U),
    (secondProjection_injective x y L Q hx hy hQ).comp (coefficientMap_injective x y L z Q U)⟩

theorem square_class_image_injective (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (U : Submodule F₂ (Q → F₂)) :
    Function.Injective ((firstClasses x y L Q).comp (coefficientMap x y L z Q U)) :=
  (firstClasses_injective x y L Q hx hy hQ).comp (coefficientMap_injective x y L z Q U)

theorem complete_image_dimension_lower (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (U : Submodule F₂ (Q → F₂))
    [Module.Finite F₂ U] (hU : U ≤ LinearMap.ker (actualMap x y L z Q)) :
    Module.finrank F₂ U - (primeCount z + 2) ≤
      Module.finrank F₂ (LinearMap.range (relationMap x y L z Q hx hy hQ U hU)) := by
  have he := LinearMap.finrank_range_of_inj (relationMap_injective x y L z Q hx hy hQ U hU)
  exact (dimension_lower x y L z Q U).trans_eq he.symm

def physicalMap (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (U : Submodule F₂ (Q → F₂)) : U →ₗ[F₂] (Occurrence L →₀ F₂) :=
  (Finsupp.linearEquivFunOnFinite F₂ F₂ (Occurrence L)).symm.toLinearMap.comp
    ((selection (largePrimeGraph x y L) Q).comp U.subtype)

theorem exists_cut_basis {J : Type u} (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (U : Submodule F₂ (Q → F₂)) (b : Module.Basis J F₂ U) (ℓ : ℕ)
    (hphysical : ∀ j, (physicalMap x y L Q U (b j)).support.card ≤ ℓ) :
    ∃ (I : Type u) (bcut : Module.Basis I F₂ (CutSpace x y L z Q U)),
      ∀ i, (physicalMap x y L Q U (bcut i).val).support.card ≤ ℓ * (primeCount z + 3) := by
  obtain ⟨I, bcut, hb⟩ := SparseConstraintBasis.exists_sparse_cut_basis b
    ((constraints x y L z Q).comp U.subtype) (physicalMap x y L Q U) ℓ hphysical
  refine ⟨I, bcut, ?_⟩
  intro i
  simpa only [constraintTarget_finrank, Nat.add_assoc] using hb i

end PaperP1.ShortBasisFinalCut
