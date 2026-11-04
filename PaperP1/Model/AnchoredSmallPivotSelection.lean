module

public import PaperP1.Arithmetic.OrdinarySmoothSourcePopulation
public import PaperP1.Model.AnchoredCleanSourceData

/-! # Selecting an actual small private source pivot outside every arithmetic anchor

The only unbounded source census left explicit is the actual number of
windows missing two ordinary smooth candidates. Everything here is a
finite construction in the original integer and prime-cylinder model.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredSmallPivotSelection

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.AnchoredPrivateValues
  PaperP1.AnchoredPrivateField PaperP1.AnchoredCleanBoundaryPairs
  PaperP1.OrdinarySmoothSourcePopulation PaperP1.NonanchorPivotSelection

theorem goodSources_subset_retained {N K B Y Z : ℕ} (Q : ℝ) (hN : 2 ≤ N) (hYZ : Y ≤ Z) :
    goodSources N K B Z Q ⊆ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y := by
  intro j hj
  obtain ⟨hjB, _, hjbad⟩ := mem_goodSources.mp hj
  exact PaperP1.AnchoredDyadicField.retained_of_not_bad hN hYZ hjB hjbad

theorem selectedPrime_pos {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K + 1)}
    (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j)) (n : ℕ) :
    0 < selectedPrime D selected n := by
  unfold selectedPrime
  split
  · exact (PaperP1.AnchoredWindowForcing.pivots (D.window _) (selected _)).property.pos
  · exact Nat.zero_lt_one

theorem exists_actual_small_selector {N K B Y Z M : ℕ} (Q : ℝ) (hN : 2 ≤ N) (hK : 1 ≤ K)
    (hYZ : Y ≤ Z) (anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1))
    (D : Data M Y K (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y) anchor) :
    ∃ selected : ∀ j : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y, Free (anchor j),
      ∀ j ∈ goodSources N K B Z Q, (selectedPrime D selected j : ℝ) ≤ Q := by
  obtain ⟨selected, hs⟩ := exists_selector (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y)
    K hK anchor (fun j ↦ j.val ∈ goodSources N K B Z Q) Q
    (fun _ hj ↦ (mem_goodSources.mp hj).2.1)
  refine ⟨selected, ?_⟩
  intro j hj
  let v : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y :=
    ⟨j, goodSources_subset_retained Q hN hYZ hj⟩
  have hp := hs v hj
  rw [selectedPrime_apply D selected v]
  exact hp

theorem reciprocal_source_lower {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K + 1)}
    (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j))
    (J : Finset ℕ) (Q : ℝ) (hQ : ∀ j ∈ J, (selectedPrime D selected j : ℝ) ≤ Q) :
    (J.card : ℝ) / Q ≤ PaperP1.CleanPivotPairs.reciprocalSum J (selectedPrime D selected) := by
  calc
    _ = ∑ _j ∈ J, 1 / Q := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have hpos : (0 : ℝ) < selectedPrime D selected j := by exact_mod_cast selectedPrime_pos D selected j
      exact one_div_le_one_div_of_le hpos (hQ j hj)

end PaperP1.AnchoredSmallPivotSelection
