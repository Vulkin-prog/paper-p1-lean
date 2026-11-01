module

public import PaperP1.Arithmetic.WindowPoolCount

/-! # The branching exception set on any bounded finite set of enclosing windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralBranchingExceptions

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.WindowPoolCount

def exceptions (G R : Finset ℕ) (L : ℕ) : Finset ℕ :=
  G.filter fun x ↦ 2 ≤ (supportedIndices R (x - 1) (L + 1)).card

theorem exceptions_subset (G R : Finset ℕ) (L : ℕ) : exceptions G R L ⊆ G := filter_subset _ _

theorem retained_card_le_one {G R : Finset ℕ} {L x : ℕ} (hx : x ∈ G) (hnot : x ∉ exceptions G R L) :
    (supportedIndices R (x - 1) (L + 1)).card ≤ 1 := by
  by_contra h
  exact hnot (mem_filter.mpr ⟨hx, by omega⟩)

theorem twice_card_le {G R : Finset ℕ} {L X : ℕ}
    (hlo : ∀ x ∈ G, 2 ≤ x) (hhi : ∀ x ∈ G, x + L ≤ X) :
    2 * (exceptions G R L).card ≤ (L + 1) * (poolValues R (L + 1) X).card := by
  calc
    _ = ∑ _x ∈ exceptions G R L, (2 : ℕ) := by simp; omega
    _ ≤ ∑ x ∈ exceptions G R L, (supportedIndices R (x - 1) (L + 1)).card :=
      sum_le_sum fun _ hx ↦ (mem_filter.mp hx).2
    _ ≤ ∑ x ∈ G, (supportedIndices R (x - 1) (L + 1)).card :=
      sum_le_sum_of_subset_of_nonneg (exceptions_subset G R L) (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ _ := sum_supportedIndices_le hlo (by simpa only [Nat.add_sub_cancel] using hhi)

theorem card_le_half {G R : Finset ℕ} {L X : ℕ}
    (hlo : ∀ x ∈ G, 2 ≤ x) (hhi : ∀ x ∈ G, x + L ≤ X) :
    ((exceptions G R L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2 * (poolValues R (L + 1) X).card := by
  have h : 2 * ((exceptions G R L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * (poolValues R (L + 1) X).card := by
    exact_mod_cast twice_card_le (R := R) hlo hhi
  linarith

end PaperP1.GeneralBranchingExceptions
