module

public import PaperP1.Combinatorics.ImageRepetitionBudget
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # At most twice the codimension coordinates vanish or coincide on an actual subspace -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniqueCoordinateBudget

open Finset

variable {K ι : Type*} [DivisionRing K] [Fintype ι] [DecidableEq ι]

def form (R : Submodule K (ι → K)) (i : ι) : Module.Dual K R := (LinearMap.proj i).comp R.subtype

def labels (R : Submodule K (ι → K)) : Finset (Module.Dual K R) := by
  classical
  exact (univ.image (form R)).erase 0

def good (R : Submodule K (ι → K)) : Finset ι := by
  classical
  exact ImageRepetitionBudget.good (form R)

def bad (R : Submodule K (ι → K)) : Finset ι := univ \ good R

def encoding (R : Submodule K (ι → K)) : R →ₗ[K] (labels R → K) where
  toFun x α := α.val x
  map_add' x y := by ext α; exact map_add α.val x y
  map_smul' c x := by ext α; exact map_smul α.val c x

omit [DecidableEq ι] in
theorem encoding_injective (R : Submodule K (ι → K)) : Function.Injective (encoding R) := by
  classical
  intro x y hxy
  apply Subtype.ext
  funext i
  by_cases hi : form R i = 0
  · have hx := DFunLike.congr_fun hi x
    have hy := DFunLike.congr_fun hi y
    change x.val i = 0 at hx
    change y.val i = 0 at hy
    exact hx.trans hy.symm
  · have hmem : form R i ∈ labels R := mem_erase.mpr ⟨hi, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
    exact congrFun hxy ⟨form R i, hmem⟩

omit [DecidableEq ι] in
theorem dimension_le_labels (R : Submodule K (ι → K)) : Module.finrank K R ≤ (labels R).card := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := encoding R) (encoding_injective R)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

theorem mem_good (R : Submodule K (ι → K)) (i : ι) :
    i ∈ good R ↔ form R i ≠ 0 ∧ ∀ j, form R j = form R i → j = i := by
  classical
  exact ImageRepetitionBudget.mem_good (form R) i

theorem bad_card_le_twice_codim (R : Submodule K (ι → K)) :
    (bad R).card ≤ 2 * (Fintype.card ι - Module.finrank K R) := by
  classical
  have hb := ImageRepetitionBudget.bad_budget (form R)
  change (bad R).card + 2 * (labels R).card ≤ 2 * Fintype.card ι at hb
  have hd := dimension_le_labels R
  have hR : Module.finrank K R ≤ Fintype.card ι := by
    simpa only [Module.finrank_fintype_fun_eq_card] using R.finrank_le
  omega

theorem good_card_lower (R : Submodule K (ι → K)) :
    Fintype.card ι - 2 * (Fintype.card ι - Module.finrank K R) ≤ (good R).card := by
  have hb := bad_card_le_twice_codim R
  have hpartition : (bad R).card + (good R).card = Fintype.card ι := by
    simpa only [bad, card_univ] using card_sdiff_add_card_eq_card (subset_univ (good R))
  omega

end PaperP1.UniqueCoordinateBudget
