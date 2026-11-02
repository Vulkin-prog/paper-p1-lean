module

public import PaperP1.Probability.UniformFubini
public import Mathlib.Logic.Equiv.Prod

/-! # Conditional expectations obtained by fixing any subset of finite fair coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateConditioning

open Finset PaperP1.UniformFubini

local instance coordinateConditioningDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [Nonempty Ω]

abbrev split (P : κ → Prop) [DecidablePred P] := Equiv.piEquivPiSubtypeProd P (fun _ ↦ Ω)

def merge (P : κ → Prop) [DecidablePred P] (σ τ : κ → Ω) : κ → Ω :=
  (split P).symm ((split P σ).1, (split P τ).2)

def conditionalAverage (P : κ → Prop) [DecidablePred P] (f : (κ → Ω) → ℝ) (σ : κ → Ω) : ℝ :=
  average (fun τ : κ → Ω ↦ if (split P τ).1 = (split P σ).1 then f τ else 0) /
    average (fun τ : κ → Ω ↦ if (split P τ).1 = (split P σ).1 then (1 : ℝ) else 0)

omit [Fintype κ] [DecidableEq κ] [Fintype Ω] [Nonempty Ω] in
theorem merge_apply (P : κ → Prop) [DecidablePred P] (σ τ : κ → Ω) (i : κ) :
    merge P σ τ i = if P i then σ i else τ i := by
  unfold merge split
  by_cases h : P i <;> simp [Equiv.piEquivPiSubtypeProd, h]

theorem averaging_merge (P : κ → Prop) [DecidablePred P] (f : (κ → Ω) → ℝ) (σ : κ → Ω) :
    average (fun τ : κ → Ω ↦ f (merge P σ τ)) =
      average (fun ν : {i // ¬P i} → Ω ↦ (f ((split P).symm ((split P σ).1, ν)))) := by
  classical
  rw [← UniformFubini.equiv (split P).symm, UniformFubini.product]
  simp only [merge, Equiv.apply_symm_apply]
  exact UniformFubini.constant _

theorem conditional_eq_average_merge (P : κ → Prop) [DecidablePred P]
    (f : (κ → Ω) → ℝ) (σ : κ → Ω) :
    conditionalAverage P f σ = average (fun τ : κ → Ω ↦ f (merge P σ τ)) := by
  classical
  unfold conditionalAverage
  rw [← UniformFubini.equiv (split P).symm (fun τ : κ → Ω ↦
    if (split P τ).1 = (split P σ).1 then f τ else 0)]
  rw [← UniformFubini.equiv (split P).symm (fun τ : κ → Ω ↦
    if (split P τ).1 = (split P σ).1 then (1 : ℝ) else 0)]
  simp only [Equiv.apply_symm_apply]
  rw [averaging_merge]
  have h := UniformFubini.condition_first
    (fun p : ({i // P i} → Ω) × ({i // ¬P i} → Ω) ↦ f ((split P).symm p)) ((split P σ).1)
  convert h using 1
  congr 1
  all_goals
    apply UniformFubini.congr
    intro p
    split_ifs <;> rfl

omit [Fintype κ] [DecidableEq κ] [Fintype Ω] [Nonempty Ω] in
theorem split_fst_eq_iff (P : κ → Prop) [DecidablePred P] (σ τ : κ → Ω) :
    (split P τ).1 = (split P σ).1 ↔ ∀ i, P i → τ i = σ i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.property

end PaperP1.CoordinateConditioning
