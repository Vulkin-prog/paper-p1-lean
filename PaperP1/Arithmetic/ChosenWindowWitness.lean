module

public import PaperP1.Arithmetic.ProjectedWindowLists

/-! # Choosing actual list witnesses without enumerating their selections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChosenWindowWitness

open Finset PaperP1.ProjectedWindowLists

def chosen {r s : ℕ} (W : ℕ) (old : Fin s → ℕ) (n : Fin r → ℕ) : Fin r → Finset ℤ := by
  classical
  exact if h : ∃ A, Witness W old n A then Classical.choose h else fun _ ↦ ∅

theorem chosen_spec {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ) (n : Fin r → ℕ)
    (hn : n ∈ lists G W old) : Witness W old n (chosen W old n) := by
  classical
  have hex := ((mem_lists G W old n).mp hn).2.2
  simp only [chosen, dite_eq_left hex]
  exact Classical.choose_spec hex

theorem long_index {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ) (n : Fin r → ℕ) (m : ℕ)
    (hn : n ∈ lists G W old) (hnot : n ∉ shortLists G W old m) :
    ∃ i, m < (chosen W old n i).card := by
  classical
  by_contra hnone
  have hall : ∀ i, (chosen W old n i).card ≤ m := by simpa only [not_exists, not_lt] using hnone
  exact hnot (mem_filter.mpr ⟨hn, chosen W old n, chosen_spec G W old n hn, hall⟩)

end PaperP1.ChosenWindowWitness
