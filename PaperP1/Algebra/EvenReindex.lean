module

public import PaperP1.Algebra.EvenImage

/-! # Explicit transport of zero-sum selections and their actual value combinations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenReindex

open Finset

variable {K ι κ : Type*} [DivisionRing K] [Fintype ι] [Fintype κ]

theorem sum_comp_symm (e : ι ≃ κ) (w : ι → K) :
    (∑ j : κ, w (e.symm j)) = ∑ i : ι, w i :=
  Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

def reindex (e : ι ≃ κ) :
    LinearMap.ker (EvenSupportRank.sumMap K ι) ≃ₗ[K] LinearMap.ker (EvenSupportRank.sumMap K κ) where
  toFun w := ⟨(fun j ↦ w.val (e.symm j)), by
    rw [LinearMap.mem_ker, EvenSupportRank.sumMap_apply, sum_comp_symm]
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property⟩
  invFun w := ⟨(fun i ↦ w.val (e i)), by
    rw [LinearMap.mem_ker, EvenSupportRank.sumMap_apply]
    have hsum := sum_comp_symm e.symm w.val
    have hw : (∑ j : κ, w.val j) = 0 := by
      simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property
    exact hsum.trans hw⟩
  left_inv w := by apply Subtype.ext; funext i; simp only [Equiv.symm_apply_apply]
  right_inv w := by apply Subtype.ext; funext j; simp only [Equiv.apply_symm_apply]
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem reindex_apply (e : ι ≃ κ) (w : LinearMap.ker (EvenSupportRank.sumMap K ι)) (j : κ) :
    (reindex e w).val j = w.val (e.symm j) := rfl

variable {E : Type*} [AddCommGroup E] [Module K E]

theorem combination_reindex (e : ι ≃ κ) (dataι : ι → E) (dataκ : κ → E)
    (heq : ∀ i : ι, dataκ (e i) = dataι i) (w : LinearMap.ker (EvenSupportRank.sumMap K ι)) :
    EvenImage.evenMap dataκ (reindex e w) = EvenImage.evenMap dataι w := by
  change EvenImage.combination dataκ (fun j ↦ w.val (e.symm j)) = EvenImage.combination dataι w.val
  rw [EvenImage.combination_apply, EvenImage.combination_apply]
  apply Fintype.sum_equiv e.symm
  intro j
  simpa only [Equiv.apply_symm_apply] using congrArg (fun z : E ↦ w.val (e.symm j) • z) (heq (e.symm j))

end PaperP1.EvenReindex
