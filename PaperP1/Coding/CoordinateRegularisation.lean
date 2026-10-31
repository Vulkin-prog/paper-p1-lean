module

public import PaperP1.Coding.CoordinatePotential
public import Mathlib.Data.Finset.Max

/-! # Simultaneous regularization by independent coordinate restrictions

A maximal admissible set of killed coordinates stops both kinds of bad
labels. Its finite potential pays for every step and gives the full source
codimension bound, rather than an assumed output of a greedy algorithm.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateForms

open Finset PaperP1.Arithmetic

local instance coordinateRegularisationPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V U : Type*} [Fintype V] [DecidableEq V] [AddCommGroup U] [Module F₂ U]

local instance coordinateRegularisationDecidableEq (A : Submodule F₂ U) : DecidableEq (Module.Dual F₂ A) :=
  Classical.decEq _

def Regular (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) (K d : ℕ) : Prop :=
  ∀ α ∈ distinctForms L A, multiplicity L A α ≤ K ∧
    (PairDecompositions.pairs (distinctForms L A) α).card ≤ d

theorem coordinate_regularisation [FiniteDimensional F₂ U] (L : V → Module.Dual F₂ U)
    (hsep : ∀ x : U, (∀ v : V, L v x = 0) → x = 0) (K d : ℕ) :
    ∃ D : Finset V,
      Module.finrank F₂ (zeroCoordinates L D) + D.card = Module.finrank F₂ U ∧
      (D.card : ℝ) ≤ budget L K d ∧ Regular L (zeroCoordinates L D) K d := by
  classical
  let C := univ.powerset.filter fun D : Finset V ↦
    Module.finrank F₂ (zeroCoordinates L D) + D.card = Module.finrank F₂ U ∧
      potential L K d D ≤ budget L K d
  have hempty : (∅ : Finset V) ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (empty_subset _), ?_, potential_empty_le_budget L K d⟩
    rw [zeroCoordinates_empty, finrank_top, card_empty, add_zero]
  obtain ⟨D, hDC, hmax⟩ := exists_max_image C Finset.card ⟨∅, hempty⟩
  obtain ⟨hDdim, hDpot⟩ := (mem_filter.mp hDC).2
  refine ⟨D, hDdim, (card_le_potential L hsep K d D).trans hDpot, ?_⟩
  intro α hα
  by_contra hbad
  have hbad' : K < multiplicity L (zeroCoordinates L D) α ∨
      d < (PairDecompositions.pairs (distinctForms L (zeroCoordinates L D)) α).card := by omega
  obtain ⟨hα0, v, hvα⟩ := (mem_distinctForms L _ α).mp hα
  have hv : restrictForm L (zeroCoordinates L D) v ≠ 0 := by rwa [hvα]
  have hvD : v ∉ D := fun h ↦ hv (restrictForm_zero_of_mem L D v h)
  have hpay := potential_step L K d D v hv (by simpa only [hvα] using hbad')
  have hnext : insert v D ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (subset_univ _), good_dimension_step L D v hv hDdim, hpay.trans hDpot⟩
  have hcard := hmax (insert v D) hnext
  rw [card_insert_of_notMem hvD] at hcard
  omega

def activeEncoding (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) :
    A →ₗ[F₂] (activeCoordinates L A → F₂) where
  toFun x v := L v.val x.val
  map_add' x y := by ext v; exact map_add (L v.val) x.val y.val
  map_smul' c x := by ext v; exact map_smul (L v.val) c x.val

omit [DecidableEq V] in
theorem activeEncoding_injective (L : V → Module.Dual F₂ U)
    (hsep : ∀ x : U, (∀ v : V, L v x = 0) → x = 0) (A : Submodule F₂ U) :
    Function.Injective (activeEncoding L A) := by
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
  · have hmem := (mem_activeCoordinates L A v).mpr hv
    exact sub_eq_zero.mpr (congrFun hxy ⟨v, hmem⟩)

omit [DecidableEq V] in
theorem removing_zero_coordinates_preserves_dimension (L : V → Module.Dual F₂ U)
    (hsep : ∀ x : U, (∀ v : V, L v x = 0) → x = 0) (A : Submodule F₂ U) :
    Module.finrank F₂ (LinearMap.range (activeEncoding L A)) = Module.finrank F₂ A :=
  LinearMap.finrank_range_of_inj (activeEncoding_injective L hsep A)

def coordinateFamily (R : Submodule F₂ (V → F₂)) (v : V) : Module.Dual F₂ R :=
  (LinearMap.proj v).comp R.subtype

omit [Fintype V] [DecidableEq V] in
theorem coordinateFamily_separates (R : Submodule F₂ (V → F₂)) :
    ∀ x : R, (∀ v : V, coordinateFamily R v x = 0) → x = 0 := by
  intro x hx
  apply Subtype.ext
  funext v
  exact hx v

def ambientRestriction (R : Submodule F₂ (V → F₂)) (D : Finset V) : Submodule F₂ (V → F₂) :=
  (zeroCoordinates (coordinateFamily R) D).map R.subtype

omit [Fintype V] [DecidableEq V] in
theorem mem_ambientRestriction (R : Submodule F₂ (V → F₂)) (D : Finset V) (x : V → F₂) :
    x ∈ ambientRestriction R D ↔ x ∈ R ∧ ∀ v ∈ D, x v = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hxR, hx⟩
    exact ⟨⟨x, hxR⟩, hx, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem ambientRestriction_dimension (R : Submodule F₂ (V → F₂)) (D : Finset V) :
    Module.finrank F₂ (ambientRestriction R D) =
      Module.finrank F₂ (zeroCoordinates (coordinateFamily R) D) :=
  Submodule.finrank_map_subtype_eq _ _

/-- Full T2.2, including zero budgets as well as its original K,d≥1 domain. -/
theorem companion_T2_2 (R : Submodule F₂ (V → F₂)) (K d : ℕ) :
    ∃ D : Finset V,
      Module.finrank F₂ R - Module.finrank F₂ (ambientRestriction R D) = D.card ∧
      (D.card : ℝ) ≤ (Fintype.card V : ℝ) / (K + 1 : ℝ) +
        (((originalForms (coordinateFamily R)).card : ℝ) - (Module.finrank F₂ R : ℝ)) / (d + 1 : ℝ) ∧
      Regular (coordinateFamily R) (zeroCoordinates (coordinateFamily R) D) K d ∧
      Module.finrank F₂ (LinearMap.range
        (activeEncoding (coordinateFamily R) (zeroCoordinates (coordinateFamily R) D))) =
          Module.finrank F₂ (ambientRestriction R D) := by
  obtain ⟨D, hdim, hcard, hreg⟩ := coordinate_regularisation (coordinateFamily R)
    (coordinateFamily_separates R) K d
  refine ⟨D, ?_, hcard.trans (budget_le_ground_card _ _ _), hreg, ?_⟩
  · rw [ambientRestriction_dimension]
    omega
  · rw [ambientRestriction_dimension]
    exact removing_zero_coordinates_preserves_dimension (coordinateFamily R)
      (coordinateFamily_separates R) _

/-- The stronger budget charges only coordinates nonzero on the initial R. -/
theorem companion_T2_2_active_budget (R : Submodule F₂ (V → F₂)) (K d : ℕ) :
    ∃ D : Finset V,
      Module.finrank F₂ R - Module.finrank F₂ (ambientRestriction R D) = D.card ∧
      (D.card : ℝ) ≤ ((originalActive (coordinateFamily R)).card : ℝ) / (K + 1 : ℝ) +
        (((originalForms (coordinateFamily R)).card : ℝ) - (Module.finrank F₂ R : ℝ)) / (d + 1 : ℝ) ∧
      Regular (coordinateFamily R) (zeroCoordinates (coordinateFamily R) D) K d := by
  obtain ⟨D, hdim, hcard, hreg⟩ := coordinate_regularisation (coordinateFamily R)
    (coordinateFamily_separates R) K d
  refine ⟨D, ?_, hcard, hreg⟩
  rw [ambientRestriction_dimension]
  omega

end PaperP1.CoordinateForms
