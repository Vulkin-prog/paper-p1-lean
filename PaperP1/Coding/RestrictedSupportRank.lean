module

public import PaperP1.Coding.MaximalSupportWord

/-! # Bounding a binary code by the number of unrestricted coordinates and the remaining support -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RestrictedSupportRank

open Finset PaperP1.Arithmetic PaperP1.BinaryEvenSelections

local instance restrictedSupportPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem restriction_card (w : ι → F₂) (S : Finset ι) :
    (selected (fun i : ↥((univ : Finset ι) \ S) ↦ w i.val)).card = (selected w \ S).card := by
  classical
  have hset : (selected (fun i : ↥((univ : Finset ι) \ S) ↦ w i.val)).image Subtype.val = selected w \ S := by
    ext i
    simp only [mem_image, selected, mem_filter, mem_univ, true_and, mem_sdiff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, (mem_sdiff.mp j.property).2⟩
    · rintro ⟨hi, hS⟩
      exact ⟨⟨i, mem_sdiff.mpr ⟨mem_univ _, hS⟩⟩, hi, rfl⟩
  rw [← hset, card_image_of_injective _ Subtype.val_injective]

theorem finrank_bound (C : Submodule F₂ (ι → F₂)) (S : Finset ι) (d : ℕ)
    (hword : ∀ w : C, (selected w.val \ S).card ≤ d) :
    Module.finrank F₂ C ≤ S.card + d := by
  classical
  let p : C →ₗ[F₂] (↥((univ : Finset ι) \ S) → F₂) :=
    (LinearMap.pi fun i : ↥((univ : Finset ι) \ S) ↦ LinearMap.proj i.val).comp C.subtype
  have hrange : Module.finrank F₂ (LinearMap.range p) ≤ d := by
    obtain ⟨v, hv⟩ := PaperP1.MaximalSupportWord.exists_large_word (LinearMap.range p)
    obtain ⟨w, hw⟩ := v.property
    rw [← hw] at hv
    exact hv.trans ((restriction_card w.val S).le.trans (hword w))
  let q : LinearMap.ker p →ₗ[F₂] (S → F₂) :=
    (LinearMap.pi fun i : S ↦ (LinearMap.proj i.val).comp C.subtype).comp (LinearMap.ker p).subtype
  have hq : Function.Injective q := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact congrFun hvw ⟨i, hi⟩
    · have hv := congrFun v.property ⟨i, mem_sdiff.mpr ⟨mem_univ _, hi⟩⟩
      have hw := congrFun w.property ⟨i, mem_sdiff.mpr ⟨mem_univ _, hi⟩⟩
      exact hv.trans hw.symm
  have hker : Module.finrank F₂ (LinearMap.ker p) ≤ S.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      LinearMap.finrank_le_finrank_of_injective hq
  have hdim := p.finrank_range_add_finrank_ker
  omega

end PaperP1.RestrictedSupportRank
