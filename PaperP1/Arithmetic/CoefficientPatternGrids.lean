module

public import PaperP1.Arithmetic.CoefficientSplitRadicalPatterns
public import PaperP1.Arithmetic.SelectedProportionalPairs

/-! # The actual selected grids of a finite coefficient pattern have fixed total cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoefficientPatternGrids

open Finset PaperP1.CoefficientSplitRadicalPatterns

def left {k : ℕ} (q : Pattern k) : Finset ℤ := univ.biUnion q.1.1

def right {k : ℕ} (q : Pattern k) : Finset ℤ := univ.biUnion q.1.2

theorem left_subset {k : ℕ} (q : Pattern k) (i : Fin k) : q.1.1 i ⊆ left q :=
  fun _ hz ↦ mem_biUnion.mpr ⟨i, mem_univ _, hz⟩

theorem right_subset {k : ℕ} (q : Pattern k) (i : Fin k) : q.1.2 i ⊆ right q :=
  fun _ hz ↦ mem_biUnion.mpr ⟨i, mem_univ _, hz⟩

theorem total_card_le {k K : ℕ} (q : Pattern k) (hK : ∀ i, (q.1.1 i).card + (q.1.2 i).card ≤ K) :
    (left q).card + (right q).card ≤ k * K := by
  calc
    _ ≤ (∑ i : Fin k, (q.1.1 i).card) + ∑ i : Fin k, (q.1.2 i).card := Nat.add_le_add card_biUnion_le card_biUnion_le
    _ = ∑ i : Fin k, ((q.1.1 i).card + (q.1.2 i).card) := sum_add_distrib.symm
    _ ≤ ∑ _i : Fin k, K := sum_le_sum (fun i _ ↦ hK i)
    _ = _ := by simp

theorem values_card_le {k K : ℕ} (q : Pattern k) (hK : ∀ i, (q.1.1 i).card + (q.1.2 i).card ≤ K)
    (x y : ℤ) :
    (SelectedProportionalPairs.values x (left q)).card + (SelectedProportionalPairs.values y (right q)).card ≤ k * K :=
  (Nat.add_le_add card_image_le card_image_le).trans (total_card_le q hK)

end PaperP1.CoefficientPatternGrids
