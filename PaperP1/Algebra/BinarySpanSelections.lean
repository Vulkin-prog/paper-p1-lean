module

public import PaperP1.Algebra.FiniteSetValueSpan
public import PaperP1.Algebra.BinaryEvenSelections

/-! # Every vector in a finite binary value span is a literal subset sum

No parity condition is imposed on the old selection.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinarySpanSelections

open Finset PaperP1.Arithmetic

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι V E : Type*} [Fintype ι] [AddCommGroup E] [Module F₂ E]

theorem weighted_selected_smul (w : ι → F₂) (f : ι → E) :
    (∑ i, w i • f i) = ∑ i ∈ BinaryEvenSelections.selected w, f i := by
  classical
  rw [BinaryEvenSelections.selected, sum_filter]
  apply sum_congr rfl
  intro i _
  rcases BinaryEvenSelections.binary_bit (w i) with hh | hh <;> simp [hh]

theorem exists_subset_sum (f : V → E) (S : Finset V) (u : E)
    (hu : u ∈ Submodule.span F₂ (f '' (S : Set V))) :
    ∃ T : Finset V, T ⊆ S ∧ (∑ v ∈ T, f v) = u := by
  classical
  change u ∈ FiniteSetValueSpan.span f S at hu
  rw [FiniteSetValueSpan.span_eq_range] at hu
  obtain ⟨w, hw⟩ := hu
  have hw' : (∑ v : S, w v • f v.val) = u := by
    simpa only [FiniteSetValueSpan.fullMap, FiniteSetValueSpan.data, EvenImage.combination_apply] using hw
  refine ⟨(BinaryEvenSelections.selected w).image Subtype.val, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, _ha, rfl⟩ := mem_image.mp hv
    exact a.property
  · rw [sum_image]
    · exact (weighted_selected_smul w (fun v : S ↦ f v.val)).symm.trans hw'
    · intro a _ b _ hab
      exact Subtype.ext hab

end PaperP1.BinarySpanSelections
