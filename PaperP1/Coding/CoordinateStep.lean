module

public import PaperP1.Coding.CoordinateForms

/-! # The exact dimension drop and the two finite regularization budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateForms

open Finset PaperP1.Arithmetic

local instance coordinateStepPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V U : Type*} [Fintype V] [DecidableEq V] [AddCommGroup U] [Module F₂ U]

local instance coordinateStepDecidableEq (A : Submodule F₂ U) : DecidableEq (Module.Dual F₂ A) :=
  Classical.decEq _

omit [DecidableEq V] in
theorem mem_activeCoordinates (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) (v : V) :
    v ∈ activeCoordinates L A ↔ restrictForm L A v ≠ 0 := by
  classical
  simp only [activeCoordinates, mem_filter, mem_univ, true_and]

omit [Fintype V] [DecidableEq V] in
theorem restrictForm_zero_of_mem (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) (hv : v ∈ D) :
    restrictForm L (zeroCoordinates L D) v = 0 := by
  ext x
  exact x.property v hv

theorem distinctForms_step_image (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    distinctForms L (zeroCoordinates L (insert v D)) =
      ((distinctForms L (zeroCoordinates L D)).image (stepRestriction L D v)).erase 0 := by
  classical
  ext β
  constructor
  · intro hβ
    obtain ⟨hβ0, w, hw⟩ := (mem_distinctForms L _ β).mp hβ
    have hw0 : restrictForm L (zeroCoordinates L D) w ≠ 0 := by
      intro hz
      have h := congrArg (stepRestriction L D v) hz
      rw [stepRestriction_coordinate, map_zero, hw] at h
      exact hβ0 h
    exact mem_erase.mpr ⟨hβ0, mem_image.mpr
      ⟨restrictForm L (zeroCoordinates L D) w,
        (mem_distinctForms L _ _).mpr ⟨hw0, w, rfl⟩,
        (stepRestriction_coordinate L D v w).trans hw⟩⟩
  · intro hβ
    obtain ⟨hβ0, γ, hγ, hγβ⟩ := mem_erase.mp hβ |>.imp_right mem_image.mp
    obtain ⟨_, w, hw⟩ := (mem_distinctForms L _ γ).mp hγ
    apply (mem_distinctForms L _ β).mpr
    refine ⟨hβ0, w, ?_⟩
    rw [← stepRestriction_coordinate L D v w, hw, hγβ]

theorem distinctForms_card_step (L : V → Module.Dual F₂ U) (D : Finset V) (v : V)
    (hv : restrictForm L (zeroCoordinates L D) v ≠ 0) :
    (distinctForms L (zeroCoordinates L (insert v D))).card +
      (PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
        (restrictForm L (zeroCoordinates L D) v)).card + 1 ≤
      (distinctForms L (zeroCoordinates L D)).card := by
  classical
  rw [distinctForms_step_image]
  exact PairDecompositions.nonzero_image_card_drop _ _ (stepRestriction L D v).toAddMonoidHom
    (zero_not_mem_distinctForms L _) ((mem_distinctForms L _ _).mpr ⟨hv, v, rfl⟩)
    (stepRestriction_killed L D v) binary_neg_eq_self

theorem activeCoordinates_card_step (L : V → Module.Dual F₂ U) (D : Finset V) (v : V)
    (hv : restrictForm L (zeroCoordinates L D) v ≠ 0) :
    (activeCoordinates L (zeroCoordinates L (insert v D))).card +
      multiplicity L (zeroCoordinates L D) (restrictForm L (zeroCoordinates L D) v) ≤
      (activeCoordinates L (zeroCoordinates L D)).card := by
  classical
  let A := activeCoordinates L (zeroCoordinates L D)
  let B := activeCoordinates L (zeroCoordinates L (insert v D))
  let M := univ.filter fun w ↦ restrictForm L (zeroCoordinates L D) w =
    restrictForm L (zeroCoordinates L D) v
  have hBA : B ⊆ A := by
    intro w hw
    apply (mem_activeCoordinates L _ w).mpr
    intro hw0
    apply (mem_activeCoordinates L _ w).mp hw
    rw [← stepRestriction_coordinate L D v w, hw0, map_zero]
  have hMA : M ⊆ A := by
    intro w hw
    apply (mem_activeCoordinates L _ w).mpr
    rw [(mem_filter.mp hw).2]
    exact hv
  have hBM : Disjoint B M := by
    apply disjoint_left.mpr
    intro w hwB hwM
    apply (mem_activeCoordinates L _ w).mp hwB
    rw [← stepRestriction_coordinate L D v w, (mem_filter.mp hwM).2, stepRestriction_killed]
  have h := card_le_card (union_subset hBA hMA)
  rw [card_union_of_disjoint hBM] at h
  exact h

omit [Fintype V] in
theorem good_dimension_step [FiniteDimensional F₂ U] (L : V → Module.Dual F₂ U)
    (D : Finset V) (v : V) (hv : restrictForm L (zeroCoordinates L D) v ≠ 0)
    (hD : Module.finrank F₂ (zeroCoordinates L D) + D.card = Module.finrank F₂ U) :
    Module.finrank F₂ (zeroCoordinates L (insert v D)) + (insert v D).card =
      Module.finrank F₂ U := by
  have hvD : v ∉ D := fun h ↦ hv (restrictForm_zero_of_mem L D v h)
  have hdim := step_dimension L D v hv
  rw [card_insert_of_notMem hvD]
  omega

end PaperP1.CoordinateForms
