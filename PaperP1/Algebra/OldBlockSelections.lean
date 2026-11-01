module

public import PaperP1.Model.OldSpaceProjection
public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Diophantine.LinearKernelFibres
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Full old spans are represented by actual selections in the old blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OldBlockSelections

open Finset PaperP1.Arithmetic PaperP1.LinearKernelFibres

variable {κ : Type*} [Fintype κ]

def values (z : κ → ℕ) (O : κ → Finset ℤ) : Finset ℕ :=
  univ.biUnion fun j ↦ (O j).image (value (z j))

theorem exists_selections (z : κ → ℕ) (O : κ → Finset ℤ) (u : ℕ →₀ F₂)
    (hu : u ∈ PaperP1.OldSpaceProjection.oldSpace (values z O)) :
    ∃ T : κ → Finset ℤ, (∀ j, T j ⊆ O j) ∧
      (∑ j, ∑ a ∈ T j, parityVec (value (z j) a)) = u := by
  classical
  let f : (Σ j : κ, O j) → (ℕ →₀ F₂) := fun a ↦ parityVec (value (z a.1) a.2.val)
  have hspan : PaperP1.OldSpaceProjection.oldSpace (values z O) ≤
      Submodule.span F₂ (Set.range f) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨j, _, hn⟩ := mem_biUnion.mp hn
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    exact Submodule.subset_span ⟨⟨j, ⟨a, ha⟩⟩, rfl⟩
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F₂)).mp (hspan hu)
  let T := fun j ↦ ((univ : Finset (O j)).filter fun a ↦ w ⟨j, a⟩ ≠ 0).image Subtype.val
  have hT : ∀ j, T j ⊆ O j := by
    intro j a ha
    obtain ⟨v, _, rfl⟩ := mem_image.mp ha
    exact v.property
  have hsum : ∀ j, (∑ a ∈ T j, parityVec (value (z j) a)) =
      ∑ a : O j, w ⟨j, a⟩ • parityVec (value (z j) a.val) := by
    intro j
    rw [sum_image]
    · rw [sum_filter]
      apply sum_congr rfl
      intro a _
      rcases binary_eq_zero_or_one (w ⟨j, a⟩) with hz | ho
      · simp only [hz, ne_eq, not_true_eq_false, ite_false, zero_smul]
      · simp only [ho, one_smul]
        rw [ite_eq_left (by decide : (1 : F₂) ≠ 0)]
    · intro a _ b _ heq
      exact Subtype.ext heq
  refine ⟨T, hT, ?_⟩
  rw [sum_congr rfl (fun j _ ↦ hsum j)]
  have hsig := Fintype.sum_sigma (fun a : (Σ j : κ, O j) ↦ w a • f a)
  calc
    _ = ∑ a : (Σ j : κ, O j), w a • f a := by simpa only [f] using hsig.symm
    _ = u := hw

end PaperP1.OldBlockSelections
