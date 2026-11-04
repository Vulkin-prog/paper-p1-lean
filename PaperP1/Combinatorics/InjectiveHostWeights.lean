module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-! # Exact transfer of weights through an injective finite host encoding -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InjectiveHostWeights

open Finset

variable {α β : Type*} [DecidableEq β] [Inhabited α]

def recover (P : Finset α) (f : α → β) (y : β) : α :=
  if h : ∃ x ∈ P, f x = y then Classical.choose h else default

theorem recover_spec (P : Finset α) (f : α → β) {y : β} (hy : y ∈ P.image f) :
    recover P f y ∈ P ∧ f (recover P f y) = y := by
  classical
  have h := mem_image.mp hy
  simp only [recover, dite_eq_left h]
  exact Classical.choose_spec h

theorem recover_apply (P : Finset α) (f : α → β) (hinj : Set.InjOn f P)
    {x : α} (hx : x ∈ P) : recover P f (f x) = x :=
  hinj (recover_spec P f (mem_image.mpr ⟨x, hx, rfl⟩)).1 hx
    (recover_spec P f (mem_image.mpr ⟨x, hx, rfl⟩)).2

theorem sum_transfer (P : Finset α) (f : α → β) (hinj : Set.InjOn f P) (w : α → ℝ) :
    (∑ y ∈ P.image f, w (recover P f y)) = ∑ x ∈ P, w x := by
  rw [sum_image hinj]
  exact sum_congr rfl (fun x hx ↦ congrArg w (recover_apply P f hinj hx))

end PaperP1.InjectiveHostWeights
