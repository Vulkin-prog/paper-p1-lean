module

public import PaperP1.Algebra.BinarySpanSelections

/-! # Literal selections in a forward interval have exact binary coordinate vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ForwardSubsetSelections

open Finset PaperP1.Arithmetic

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def coefficients (U H : ℕ) (A : Finset ℕ) (i : Fin H) : F₂ := if U + i.val ∈ A then 1 else 0

theorem label_injective (U H : ℕ) : Function.Injective (fun i : Fin H ↦ U + i.val) := by
  intro i j he
  exact Fin.ext (Nat.add_left_cancel he)

theorem selected_image (U H : ℕ) (A : Finset ℕ) (hA : A ⊆ Ico U (U + H)) :
    (BinaryEvenSelections.selected (coefficients U H A)).image (fun i ↦ U + i.val) = A := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hh := (mem_filter.mp hi).2
    by_contra hm
    simp only [coefficients, hm, ite_false, ne_eq, not_true_eq_false] at hh
  · intro hn
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp (hA hn)
    let i : Fin H := ⟨n - U, by omega⟩
    have he : U + i.val = n := by dsimp [i]; omega
    refine mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, ?_⟩, he⟩
    simp only [coefficients, he, hn, ite_true, ne_eq, one_ne_zero, not_false_eq_true]

theorem sum_coefficients {E : Type*} [AddCommGroup E] [Module F₂ E]
    (U H : ℕ) (A : Finset ℕ) (hA : A ⊆ Ico U (U + H)) (f : ℕ → E) :
    (∑ i : Fin H, coefficients U H A i • f (U + i.val)) = ∑ n ∈ A, f n := by
  classical
  calc
    _ = ∑ i ∈ BinaryEvenSelections.selected (coefficients U H A), f (U + i.val) :=
      BinarySpanSelections.weighted_selected_smul _ _
    _ = ∑ n ∈ (BinaryEvenSelections.selected (coefficients U H A)).image (fun i ↦ U + i.val), f n :=
      (sum_image (label_injective U H).injOn).symm
    _ = _ := by rw [selected_image U H A hA]

theorem index_of_mem (U H : ℕ) (A : Finset ℕ) (hA : A ⊆ Ico U (U + H))
    {n : ℕ} (hn : n ∈ A) : ∃ i : Fin H, U + i.val = n ∧ coefficients U H A i ≠ 0 := by
  obtain ⟨i, hi, he⟩ := mem_image.mp ((selected_image U H A hA).symm ▸ hn)
  exact ⟨i, he, (mem_filter.mp hi).2⟩

end PaperP1.ForwardSubsetSelections
