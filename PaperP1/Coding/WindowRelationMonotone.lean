module

public import PaperP1.Coding.WindowRelationCode

/-!
# Extending window relations by zero

At a fixed base U, every even square relation in a window of length B is an
even square relation in every longer window. The extension is injective, so
the actual relation dimension is monotone in the window length, including
the empty window. No arithmetic regularity assumption is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowRelationMonotone

open PaperP1.Arithmetic WindowRelationCode Finset

local instance windowMonotonePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def extend {B C : ℕ} (_h : B ≤ C) : (Fin B → F₂) →ₗ[F₂] (Fin C → F₂) where
  toFun w j := if hj : j.val < B then w ⟨j.val, hj⟩ else 0
  map_add' w v := by
    funext j
    by_cases hj : j.val < B <;> simp [hj]
  map_smul' a w := by
    funext j
    by_cases hj : j.val < B <;> simp [hj]

@[simp]
theorem extend_castLE {B C : ℕ} (h : B ≤ C) (w : Fin B → F₂) (i : Fin B) :
    extend h w (Fin.castLE h i) = w i := by
  simp [extend, i.isLt]

theorem extend_eq_zero {B C : ℕ} (h : B ≤ C) (w : Fin B → F₂) (j : Fin C)
    (hj : B ≤ j.val) : extend h w j = 0 := by
  simp [extend, Nat.not_lt.mpr hj]

theorem extend_injective {B C : ℕ} (h : B ≤ C) : Function.Injective (extend h) := by
  intro w v hwv
  funext i
  have hi := congrFun hwv (Fin.castLE h i)
  simpa only [extend_castLE] using hi

theorem sum_castLE_of_support {M : Type*} [AddCommMonoid M] {B C : ℕ}
    (h : B ≤ C) (f : Fin C → M) (hf : ∀ j, B ≤ j.val → f j = 0) :
    (∑ j, f j) = ∑ i : Fin B, f (Fin.castLE h i) := by
  classical
  let S := Finset.univ.image (Fin.castLE h)
  have hinj : Function.Injective (Fin.castLE h) := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin C ↦ x.val) hij)
  calc
    (∑ j, f j) = ∑ j ∈ S, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hf j
      by_contra hjB
      have hjlt : j.val < B := Nat.lt_of_not_ge hjB
      apply hj
      exact Finset.mem_image.mpr
        ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    _ = ∑ i : Fin B, f (Fin.castLE h i) := Finset.sum_image hinj.injOn

theorem parity_sum_extend {U B C : ℕ} (h : B ≤ C) (w : Fin B → F₂) :
    (∑ j, extend h w j • parityVec (U + j.val)) =
      ∑ i, w i • parityVec (U + i.val) := by
  rw [sum_castLE_of_support h _ (fun j hj ↦ by rw [extend_eq_zero h w j hj, zero_smul])]
  simp only [extend_castLE, Fin.val_castLE]

theorem sum_extend {B C : ℕ} (h : B ≤ C) (w : Fin B → F₂) :
    (∑ j, extend h w j) = ∑ i, w i := by
  rw [sum_castLE_of_support h _ (extend_eq_zero h w)]
  simp only [extend_castLE]

def relationExtend (U : ℕ) {B C : ℕ} (h : B ≤ C) :
    windowRelationCode U B →ₗ[F₂] windowRelationCode U C :=
  ((extend h).domRestrict (windowRelationCode U B)).codRestrict
    (windowRelationCode U C) (fun w ↦ by
      apply (mem_windowRelationCode _).mpr
      change (∑ j, extend h w.val j • parityVec (U + j.val) = 0) ∧
        (∑ j, extend h w.val j = 0)
      rw [parity_sum_extend, sum_extend]
      exact (mem_windowRelationCode _).mp w.property)

theorem relationExtend_injective (U : ℕ) {B C : ℕ} (h : B ≤ C) :
    Function.Injective (relationExtend U h) := by
  intro w v hwv
  apply Subtype.ext
  apply extend_injective h
  exact congrArg Subtype.val hwv

theorem window_relation_finrank_mono (U : ℕ) {B C : ℕ} (h : B ≤ C) :
    Module.finrank F₂ (windowRelationCode U B) ≤
      Module.finrank F₂ (windowRelationCode U C) :=
  LinearMap.finrank_le_finrank_of_injective (relationExtend_injective U h)

end PaperP1.WindowRelationMonotone
