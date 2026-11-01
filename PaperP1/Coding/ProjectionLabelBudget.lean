module

public import PaperP1.Coding.ProjectionRestrictionBudget
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Finset.Image

/-! # Projection rank is at most the number of its distinct nonzero coordinate labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectionLabelBudget

open Finset

variable {K U I : Type*} [Field K] [AddCommGroup U] [Module K U] [Fintype I]

def form (f : U →ₗ[K] (I → K)) (i : I) : Module.Dual K U := (LinearMap.proj i).comp f

def labels (f : U →ₗ[K] (I → K)) : Finset (Module.Dual K U) := by
  classical
  exact (univ.image (form f)).erase 0

def labelMap (f : U →ₗ[K] (I → K)) : U →ₗ[K] (labels f → K) := LinearMap.pi fun a ↦ a.val

theorem mem_labels (f : U →ₗ[K] (I → K)) (a : Module.Dual K U) :
    a ∈ labels f ↔ a ≠ 0 ∧ ∃ i, form f i = a := by
  classical
  simp only [labels, mem_erase, mem_image, mem_univ, true_and]

theorem labelMap_kernel (f : U →ₗ[K] (I → K)) :
    LinearMap.ker (labelMap f) = LinearMap.ker f := by
  classical
  ext u
  simp only [LinearMap.mem_ker]
  constructor
  · intro hu
    funext i
    by_cases hi : form f i = 0
    · exact DFunLike.congr_fun hi u
    · have hlabel := (mem_labels f (form f i)).mpr ⟨hi, i, rfl⟩
      exact congrFun hu ⟨form f i, hlabel⟩
  · intro hu
    funext a
    obtain ⟨_, i, hi⟩ := (mem_labels f a.val).mp a.property
    change a.val u = 0
    rw [← hi]
    exact congrFun hu i

variable [FiniteDimensional K U]

theorem rank_le_labels_card (f : U →ₗ[K] (I → K)) :
    Module.finrank K (LinearMap.range f) ≤ (labels f).card := by
  have hf := f.finrank_range_add_finrank_ker
  have hl := (labelMap f).finrank_range_add_finrank_ker
  rw [labelMap_kernel] at hl
  have hle := Submodule.finrank_le (LinearMap.range (labelMap f))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
  omega

theorem restricted_labels_lower_bound (f : U →ₗ[K] (I → K)) (M : Submodule K U) :
    (Module.finrank K (LinearMap.range f) : ℝ) -
      ((Module.finrank K U - Module.finrank K M : ℕ) : ℝ) ≤ (labels (f.comp M.subtype)).card := by
  exact (ProjectionRestrictionBudget.real_rank_lower_bound f M).trans
    (by exact_mod_cast rank_le_labels_card (f.comp M.subtype))

end PaperP1.ProjectionLabelBudget
