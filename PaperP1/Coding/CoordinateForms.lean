module

public import PaperP1.Arithmetic.ParityVector
public import PaperP1.Combinatorics.PairDecompositions
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi

/-! # Restricting a finite family of binary coordinate forms -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateForms

open Finset PaperP1.Arithmetic

local instance coordinatePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V U : Type*} [Fintype V] [DecidableEq V]
variable [AddCommGroup U] [Module F₂ U] [FiniteDimensional F₂ U]

def restrictForm (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) (v : V) : Module.Dual F₂ A :=
  (L v).comp A.subtype

def distinctForms (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) : Finset (Module.Dual F₂ A) := by
  classical
  exact (univ.image (restrictForm L A)).erase 0

def activeCoordinates (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) : Finset V := by
  classical
  exact univ.filter fun v ↦ restrictForm L A v ≠ 0

def multiplicity (L : V → Module.Dual F₂ U) (A : Submodule F₂ U)
    (α : Module.Dual F₂ A) : ℕ := by
  classical
  exact (univ.filter fun v ↦ restrictForm L A v = α).card

def zeroCoordinates (L : V → Module.Dual F₂ U) (D : Finset V) : Submodule F₂ U where
  carrier := {x | ∀ v ∈ D, L v x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy v hv
    rw [map_add, hx v hv, hy v hv, add_zero]
  smul_mem' := by
    intro c x hx v hv
    rw [map_smul, hx v hv, smul_zero]

omit [Fintype V] [DecidableEq V] [FiniteDimensional F₂ U] in
@[simp] theorem mem_zeroCoordinates (L : V → Module.Dual F₂ U) (D : Finset V) (x : U) :
    x ∈ zeroCoordinates L D ↔ ∀ v ∈ D, L v x = 0 := Iff.rfl

omit [Fintype V] [DecidableEq V] [FiniteDimensional F₂ U] in
theorem zeroCoordinates_empty (L : V → Module.Dual F₂ U) : zeroCoordinates L ∅ = ⊤ := by
  ext x
  simp

omit [Fintype V] [FiniteDimensional F₂ U] in
theorem zeroCoordinates_insert (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    zeroCoordinates L (insert v D) = zeroCoordinates L D ⊓ LinearMap.ker (L v) := by
  ext x
  simp only [mem_zeroCoordinates, mem_insert, forall_eq_or_imp,
    Submodule.mem_inf, LinearMap.mem_ker]
  exact and_comm

omit [Fintype V] [FiniteDimensional F₂ U] in
theorem zeroCoordinates_insert_le (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    zeroCoordinates L (insert v D) ≤ zeroCoordinates L D := by
  rw [zeroCoordinates_insert]
  exact inf_le_left

def stepInclusion (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    zeroCoordinates L (insert v D) →ₗ[F₂] zeroCoordinates L D :=
  Submodule.inclusion (zeroCoordinates_insert_le L D v)

def stepRestriction (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    Module.Dual F₂ (zeroCoordinates L D) →ₗ[F₂] Module.Dual F₂ (zeroCoordinates L (insert v D)) :=
  (stepInclusion L D v).dualMap

omit [Fintype V] [FiniteDimensional F₂ U] in
theorem stepRestriction_coordinate (L : V → Module.Dual F₂ U) (D : Finset V) (v w : V) :
    stepRestriction L D v (restrictForm L (zeroCoordinates L D) w) =
      restrictForm L (zeroCoordinates L (insert v D)) w := rfl

omit [Fintype V] [FiniteDimensional F₂ U] in
theorem stepRestriction_killed (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    stepRestriction L D v (restrictForm L (zeroCoordinates L D) v) = 0 := by
  ext x
  exact x.property v (mem_insert_self _ _)

def stepKernelEquiv (L : V → Module.Dual F₂ U) (D : Finset V) (v : V) :
    zeroCoordinates L (insert v D) ≃ₗ[F₂]
      LinearMap.ker (restrictForm L (zeroCoordinates L D) v) where
  toFun x := ⟨stepInclusion L D v x, x.property v (mem_insert_self _ _)⟩
  invFun x := ⟨x.val.val, by
    rw [zeroCoordinates_insert]
    exact ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] in
theorem step_dimension (L : V → Module.Dual F₂ U) (D : Finset V) (v : V)
    (hv : restrictForm L (zeroCoordinates L D) v ≠ 0) :
    Module.finrank F₂ (zeroCoordinates L (insert v D)) + 1 =
      Module.finrank F₂ (zeroCoordinates L D) := by
  rw [(stepKernelEquiv L D v).finrank_eq]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hv

omit [DecidableEq V] [FiniteDimensional F₂ U] in
theorem mem_distinctForms (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) (α : Module.Dual F₂ A) :
    α ∈ distinctForms L A ↔ α ≠ 0 ∧ ∃ v : V, restrictForm L A v = α := by
  classical
  simp only [distinctForms, mem_erase, mem_image, mem_univ, true_and]

omit [DecidableEq V] [FiniteDimensional F₂ U] in
theorem zero_not_mem_distinctForms (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) :
    (0 : Module.Dual F₂ A) ∉ distinctForms L A := by
  classical
  exact notMem_erase _ _

def encoding (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) :
    A →ₗ[F₂] (distinctForms L A → F₂) where
  toFun x α := α.val x
  map_add' x y := by ext α; exact map_add α.val x y
  map_smul' c x := by ext α; exact map_smul α.val c x

omit [DecidableEq V] [FiniteDimensional F₂ U] in
theorem encoding_injective (L : V → Module.Dual F₂ U)
    (hsep : ∀ x : U, (∀ v : V, L v x = 0) → x = 0) (A : Submodule F₂ U) :
    Function.Injective (encoding L A) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hsep
  intro v
  rw [map_sub]
  by_cases hv : restrictForm L A v = 0
  · have hx := DFunLike.congr_fun hv x
    have hy := DFunLike.congr_fun hv y
    change L v x.val = 0 at hx
    change L v y.val = 0 at hy
    rw [hx, hy, sub_self]
  · have hmem : restrictForm L A v ∈ distinctForms L A :=
      (mem_distinctForms L A _).mpr ⟨hv, v, rfl⟩
    have h := congrFun hxy ⟨restrictForm L A v, hmem⟩
    exact sub_eq_zero.mpr h

omit [DecidableEq V] [FiniteDimensional F₂ U] in
theorem dimension_le_distinct_card (L : V → Module.Dual F₂ U)
    (hsep : ∀ x : U, (∀ v : V, L v x = 0) → x = 0) (A : Submodule F₂ U) :
    Module.finrank F₂ A ≤ (distinctForms L A).card := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := encoding L A) (encoding_injective L hsep A)
  simpa using h

theorem binary_neg_eq_self {W : Type*} [AddCommGroup W] [Module F₂ W] (w : W) : -w = w := by
  rw [← neg_one_smul F₂, show (-1 : F₂) = 1 by decide, one_smul]

end PaperP1.CoordinateForms
